/**
 * fichier: traitementImage.c
 * auteur: Johann Rosain
 * date: 11/03/2022
 **/
#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/time.h>

#include "calcul.h"

// structure qui regroupe les variables partag�es entre les threads.
struct varPartagees {
    int nbZones;
    struct timeval start;
    int *di; // Tableau des zones actuellement traitées
    pthread_cond_t *cond; // Tableau des conditions deux à deux
    pthread_mutex_t lock;
};

struct params {
    int idThread;
    struct varPartagees *vPartage;
};

typedef struct params Params;
typedef struct varPartagees Shared;

double getTimeElapsed(struct timeval start) {
    struct timeval end;
    gettimeofday(&end, NULL);
    double elapsed = (end.tv_sec - start.tv_sec) * 1000.;
    elapsed += (end.tv_usec - start.tv_usec) / 1000.;
    return elapsed / 1000.;
}
 
void *traitement (void *p) {
    Params *args = (Params *)p;
    Shared *vPartage = args->vPartage;

    printf("[%i][%fs] Traitement de %i zones.\n", args->idThread, 
        getTimeElapsed(vPartage->start), vPartage->nbZones);

    for(int i = 1; i <= vPartage->nbZones; i++) {
        pthread_mutex_lock(&vPartage->lock);
        // Le premier traitement n'attend personne : il doit forcément finir sa zone pour que les suivants la traite.
        if(args->idThread > 0) {
            if(vPartage->di[args->idThread - 1] <= vPartage->nbZones && 
                    vPartage->di[args->idThread - 1] < i + 1) {
                pthread_cond_wait(&vPartage->cond[args->idThread - 1], &vPartage->lock);
            }
        }
        pthread_mutex_unlock(&vPartage->lock);

        int wait = args->idThread + rand() % 3;
        printf("[%i][%fs] Début du calcul sur la zone %i. Temps estimé: %i secondes\n", args->idThread, 
            getTimeElapsed(vPartage->start), i, wait * 3);
        calcul(wait);
        printf("[%i][%fs] Fin du calcul sur la zone %i.\n", args->idThread, 
            getTimeElapsed(vPartage->start), i);

        pthread_mutex_lock(&vPartage->lock);
        // On signale que le thread actuel traite la i-ème zone :
        vPartage->di[args->idThread] = i + 1;
        pthread_cond_signal(&vPartage->cond[args->idThread]);
        pthread_mutex_unlock(&vPartage->lock);
    }    
    
    pthread_exit(NULL); 
}

int main(int argc, char * argv[]) {
    if (argc != 3) {
        printf("Utilisation: %s nombre_traitements nombre_zones\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Initialisation 
    int nTreatments = atoi(argv[1]);
    pthread_t threads[nTreatments];
    Params tabParams[nTreatments];
    Shared sharedData;
    sharedData.nbZones =  atoi(argv[2]);
    sharedData.di = (int *)calloc(nTreatments, sizeof(int));  
    sharedData.cond = (pthread_cond_t *)malloc(nTreatments * sizeof(pthread_cond_t));
    gettimeofday(&sharedData.start, NULL);

    int err;
    if ((err = pthread_mutex_init(&sharedData.lock, NULL)) != 0) {
        printf("Erreur : %s\n", strerror(err));
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < nTreatments; ++i) {
        if ((err = pthread_cond_init(&sharedData.cond[i], NULL)) != 0) {
            printf("Erreur : %s\n", strerror(err));
            exit(EXIT_FAILURE);
        }
    }

    // Pour la simulation des temps de calcul
    srand(atoi(argv[1])); 
    
    // Création des threads
    for (int i = 0; i < atoi(argv[1]); ++i) {
        tabParams[i].idThread = i;
        tabParams[i].vPartage = &sharedData; 
        if (pthread_create(&threads[i], NULL, traitement, (void *)&tabParams[i]) != 0) {
            perror("Erreur lors de la création du thread ");
            exit(1);
        }
    }
    
    // Attente de la fin des threads. 
    for (int i = 0; i < atoi(argv[1]); i++) {
        pthread_join(threads[i], NULL);
    }
    printf("Thread principal : fin de tous les threads secondaires. Temps total : %fs\n", getTimeElapsed(sharedData.start));

    for (int i = 0; i < nTreatments; ++i) {
        pthread_cond_destroy(&sharedData.cond[i]);
    }
    pthread_mutex_destroy(&sharedData.lock);
    free(sharedData.di); free(sharedData.cond);
    return 0;
}