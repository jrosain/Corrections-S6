/**
 * fichier: rdv.c
 * auteur: Johann Rosain
 * date: 11/03/2022
 **/
#include <stdio.h>
#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#include "calcul.h"

struct predicatRdv {
    // regroupe les données partagées entres les threads participants aux RdV :
    pthread_mutex_t lock;
    pthread_cond_t cond;
    int sharedData;
};

struct params {
    // structure pour regrouper les paramètres d'un thread. 
    int idThread; // un identifiant de thread, de 1 à N (N le nombre
            // total de theads secondaires
    int n;
    struct predicatRdv *varPartagee;
};

// fonction associée a chaque thread participant au RdV.
void * participant (void *p) {
    struct params *args = (struct params *) p;

    int wait = args->idThread + rand() % 5;
    printf("[%i] Début du calcul. Attente : %i secondes\n", args->idThread, wait * 3);
    // Simulation d'un long calcul pour le travail avant RdV
    calcul(wait); // C'est un exemple.

    // RdV 
    pthread_mutex_lock(&args->varPartagee->lock);
    args->varPartagee->sharedData += 1;
    printf("[%i] %i/%i.\n", args->idThread, args->varPartagee->sharedData, args->n);
    if (args->varPartagee->sharedData < args->n) {  // attention : le dernier arrivé ne doit pas attendre. Il doit réveiller tous les autres.
        pthread_cond_wait(&args->varPartagee->cond, &args->varPartagee->lock);
    }
    else if (args->varPartagee->sharedData == args->n) {
        printf("[%i] Rendez-vous atteint, réveil des threads.\n", args->idThread);
        pthread_cond_broadcast(&args->varPartagee->cond);
    }
    pthread_mutex_unlock(&args->varPartagee->lock);

    wait = args->idThread + rand() % 5;
    printf("[%i] Suite du calcul. Attente : %i secondes.\n", args->idThread, wait * 3);
    calcul(wait); // reprise et poursuite de l'execution.

    pthread_exit(NULL); // fortement recommandé.
}

int main(int argc, char *argv[]){
    if (argc != 2) {
        printf("Utilisation: %s nombre_threads\n", argv[0]);
        exit(1);
    }

    // Initialisations 
    pthread_t threads[atoi(argv[1])];
    struct params tabParams[atoi(argv[1])];
    struct predicatRdv predicat;
    predicat.sharedData = 0;

    int err;
    if ((err = pthread_mutex_init(&predicat.lock, NULL)) != 0) {
        printf("Erreur : %s\n", strerror(err));
        exit(EXIT_FAILURE);
    }
    if ((err = pthread_cond_init(&predicat.cond, NULL)) != 0) {
        printf("Erreur : %s\n", strerror(err));
        exit(EXIT_FAILURE);
    }

    srand(atoi(argv[1]));  // initialisation de rand pour la simulation de longs calculs
    
    // Création des threards 
    for (int i = 0; i < atoi(argv[1]); i++){
        tabParams[i].idThread = i + 1;
        tabParams[i].n = atoi(argv[1]);
        tabParams[i].varPartagee = &predicat; 

        if (pthread_create(&threads[i], NULL, participant, (void*)&tabParams[i]) != 0) {
            perror("Erreur : problème lors de la création du thread ");
            exit(1);
        }
    }

    // Attente de la fin des  threards. Partie obligatoire 
    for (int i = 0; i < atoi(argv[1]); i++) {
        pthread_join(threads[i], NULL);
    }
    printf("Thread principal : fin de tous les threads secondaires.\n");

    // terminer "proprement". 
    pthread_cond_destroy(&predicat.cond);
    pthread_mutex_destroy(&predicat.lock);
    return 0;
}
 
