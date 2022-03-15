#include <stddef.h>
#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "calcul.h"

/**
 * PROPOSITION D'ARCHITECTURE
 *
 * Soit N le nombre d'activités en parallèle
 * Soit M le nombre de zones Z de l'image
 *
 * Z doit être une relation d'ordre (Z1 < Z2 < ... < ZM)
 * On représente Z par un entier (son ordre) et sa zone
 * (pixels) correpondant.
 * 
 * Un tableau T de N Threads
 * Un tableau D de N entiers initialisés à 0
 * Un tableau A de N fonctions prenant en entrée une zone
 * Un tableau C de N-1 variables conditionnelles
 * Un verrour v (qui verrouille l'accès au tableau D)
 * 
 * Chaque thread représente une activité. Ils doivent récupérer
 * en paramètre leur identifiant, les tableaux Z, D, A et C et le
 * verrou v.
 *
 * Le thread numéro i ne peut lancer son activité A[i] que si la zone
 * Zx actuelle a déjà été traitée par l'activité précédente (i - 1).
 *
 * - Il ne peut traiter sa zone que si D[i - 1] > x.
 * - Il doit donc attendre cet événement.
 * - Si ce n'est pas le cas, le thread s'endort en attendant ledit
 * événement. (C[i] s'endort)
 * - Lorsqu'un thread a terminé un événement il réveille son prochain.
 *
 * 1. Initialisation
 *    a. z = 0 (zone actuelle)
 * 
 * 2. Vérification de la possibilité de traitement de la zone z
 *    a. i == 0 OU D[i - 1] > z ?
 *    b. Si non, C[i - 1] s'endort, si oui, on passe à 3.a
 *    c. Lorsque C[i - 1] se réveille, retour à 2.a.
 *
 * 3. Traitement de la zone
 *    a. On fait notre traitement sur la zone z (appel de l'activité A[i](z))
 *    b. z += 1
 *    c. On demande le verrou v
 *    d. Une fois le verrou obtenu, on modifie D[i] pour valoir z
 *
 * 4. On indique à notre prochain que la zone a été traité
 *    a. On revéille C[i]
**/

struct pixel_t {
    size_t x;
    size_t y;
    size_t v;
};

struct zone_t {
    size_t id;
    size_t size;
    struct pixel_t* pixels;
};

struct activity_params_t {
    size_t id;
    size_t nb_zones;
    size_t nb_activities;

    struct zone_t* zones;   // Tableau dynamique de taille nb_zones
    size_t* activity_zones; // Tableau dynamique de taille nb_activities
    pthread_cond_t* conds;  // Tableau dynamique de taille nb_activities

    pthread_mutex_t* lock;

    void (**activities)(struct zone_t*); // Tableau dynamique de taille nb_activities
};

void activity_1(struct zone_t* zone) {
    zone->pixels[0].v += 1;
}

void activity_2(struct zone_t* zone) {
    zone->pixels[0].v *= 2;
}

void* activity(void* p) {
    struct activity_params_t* params = (struct activity_params_t*) p;

    printf("[Thread %li] : début activité\n", params->id);

    for (int actual_zone = 0; actual_zone < params->nb_zones; ++actual_zone) {
        if (params->id != 0) {
            pthread_mutex_lock(params->lock);
            if (params->activity_zones[params->id - 1] <= actual_zone) {
                pthread_cond_wait(&params->conds[params->id - 1], params->lock);
            }
            pthread_mutex_unlock(params->lock);
        }

        //printf("[Thread %li] : traitement zone %li\n", params->id, params->zones[actual_zone].id);
        params->activities[params->id](&params->zones[actual_zone]);

        pthread_mutex_lock(params->lock);
        params->activity_zones[params->id]++;
        pthread_mutex_unlock(params->lock);
        pthread_cond_broadcast(&params->conds[params->id]);
    }

    printf("[Thread %li] : fin activité\n", params->id);

    pthread_exit(NULL);
}

int main (int argc, char** argv) {

    // Récupération des paramètres
    if (argc != 4) {
        printf("Utilisation : %s longueur largeur activités\n", argv[0]);
        exit(1);
    }

    // Gestion des erreurs
    int err;

    // Définition des constantes
    size_t n = atoll(argv[1]);
    size_t m = atoll(argv[2]);
    size_t nb_activities = atoll(argv[3]);
    size_t nb_pixels = n*m;
    int display = 1;

    printf("[Thread principal] : début du programme, allocation mémoire\n");

    // Allocations mémoires

    // Il y a autant de zone que de pixel pour commencer
    // Chaque zone ne contient qu'un seul pixel
    struct zone_t* zones = malloc(nb_pixels * sizeof(struct zone_t));

    for (int i = 0; i < nb_pixels; ++i) {
        zones[i].id = i;
        zones[i].size = 1;
        zones[i].pixels = malloc(sizeof(struct pixel_t));
        zones[i].pixels[0].x = i % n;
        zones[i].pixels[0].y = i / n;
        zones[i].pixels[0].v = i;
    }

    pthread_t* activities = malloc(nb_activities * sizeof(size_t));
    size_t* activity_zones = malloc(nb_activities * sizeof(size_t));
    pthread_cond_t* conds = malloc(nb_activities * sizeof(pthread_cond_t));
    struct activity_params_t* params = malloc(nb_activities * sizeof(struct activity_params_t));
    void (**activity_functions)(struct zone_t*) = malloc(nb_activities * sizeof(void (*)(struct zone_t*)));

    activity_functions[0] = activity_1;
    activity_functions[1] = activity_2;

    for (int i = 0; i < nb_activities; ++i) {
        activity_zones[i] = 0;
        
        // Initialisation de toutes les variables conditionnelles
        if ((err = pthread_cond_init(&conds[i], NULL)) != 0) {
            printf("Erreur initiation variable conditionnelle n°%i : %s\n", i, strerror(err));
            exit(1);
        }
    }

    // Initialisation du verrou
    pthread_mutex_t lock;
    if ((err = pthread_mutex_init(&lock, NULL)) != 0) {
        printf("Erreur initiation verrou : %s", strerror(err));
        exit(1);
    }

    // Affichage "image" de base
    if (display) {
        for (int j = 0; j < m; ++j) {
            for (int i = 0; i < n; ++i) {
                printf("%li ", zones[j*n + i].pixels[0].v);
            }
            printf("\n");
        }
    }

    printf("[Thread principal] : création des activités\n");

    // Création de tous les threads
    for (int i = 0; i < nb_activities; ++i) {
        params[i].id = i;
        params[i].nb_zones = nb_pixels;
        params[i].nb_activities = nb_activities;
        params[i].zones = zones;
        params[i].activity_zones = activity_zones;
        params[i].conds = conds;
        params[i].lock = &lock;
        params[i].activities = activity_functions;

        printf("[Thread %i] : lancement\n", i);

        // Pour le moment, la même fonction pour toutes les activités
        if ((err = pthread_create(&activities[i], NULL, activity, &params[i])) != 0) {
            printf("[Thread %i] : erreur creation : %s\n", i, strerror(err));
            exit(1);
        }
    }

    // Attente de la fin des threads
    for (int i = 0; i < nb_activities; i++) {
        if ((err = pthread_join(activities[i], NULL)) != 0) {
            printf("[Thread %i] : erreur fin : %s\n", i, strerror(err));
            exit(1);
        }
        printf("[Thread %i] : fini\n", i);
    }

    printf("[Thread principal] : fin du programme, désallocation mémoire\n");

    // Affichage "image" finale
    if (display) {
        for (int j = 0; j < m; ++j) {
            for (int i = 0; i < n; ++i) {
                printf("%li ", zones[j*n + i].pixels[0].v);
            }
            printf("\n");
        }
    }

    // Désallocations mémoires

    for (int i = 0; i < nb_pixels; ++i) {
        free(zones[i].pixels);
    }

    free(zones);

    for (int i = 0; i < nb_activities; ++i) {
        if ((err = pthread_cond_destroy(&conds[i])) != 0) {
            printf("Erreur destruction variable conditionnelle n°%i : %s\n", i, strerror(err));
            exit(1);
        }
    }

    free(activities);
    free(activity_zones);
    free(conds);
    free(params);
    free(activity_functions);

    if ((err = pthread_mutex_destroy(&lock)) != 0) {
        printf("Erreur destruction verrou : %s\n", strerror(err));
        exit(1);
    }

    return 0;
}