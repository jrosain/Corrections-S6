#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include "calcul.h"

struct predicatRdv {
    int waitingThread;
};

struct params {
    // un identifiant de thread, de 1 à N (N le nombre total de threads) secondaires
    int idThread;
    int N;
    struct predicatRdv* varPartagee;
    pthread_mutex_t* verrou;
    pthread_cond_t* cond;
};

void* participant(void* p) { 
    struct params* args = (struct params*) p;
    struct predicatRdv* predicat = args->varPartagee;

    // On lock 
    printf("[Thread %i] : je me mets en attente du verrou\n", args->idThread);
    pthread_mutex_lock(args->verrou);
    printf("[Thread %i] : je vérouille le verrou\n", args->idThread);

    int attente = 1;

    // Simulation d'un long calcul pour le travail avant RdV
    printf("[Thread %i] : début calcul, duration : %is\n", args->idThread, attente*3);
    calcul(attente);
    printf("[Thread %i] : fin calcul\n", args->idThread);

    // On incrémente le nombre de thread en attente
    // Si on a N thread en attente alors on réveille tout le monde
    if (++(predicat->waitingThread) == args->N) {
        printf("[Thread %i] : dernier thread je réveille tout le monde !\n", args->idThread);
        pthread_cond_broadcast(args->cond);
    }

    // RdV 
    while (predicat->waitingThread != args->N) {
        // Les threads attendent que tout le monde est fini, l'attente libère le verrou
        // Lorsque le thread se réveille, il attend que le verrou se déverouille
        // Une fois le verrou déverouillé il le récupère et le vérouille à son tour
        printf("[Thread %i] : je rompish et je libère le verrou\n", args->idThread);
        pthread_cond_wait(args->cond, args->verrou);
        printf("[Thread %i] : je me réveille et vérouille le verrou\n", args->idThread);
    }

    // On unlock le verrou locké par la fin du wait
    // Ou par le lock pour le dernier thread
    pthread_mutex_unlock(args->verrou);
    printf("[Thread %i] : je libère le verrou\n", args->idThread);

    attente = 2;

    // Simulation d'un long calcul pour le travail avant RdV
    printf("[Thread %i] : début calcul final, duration : %is\n", args->idThread, attente*3);
    calcul(attente);
    printf("[Thread %i] : fin calcul final\n", args->idThread);

    pthread_exit(NULL);
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        printf("argument requis\n");
        printf("%s nombre_Threads\n", argv[0]);
        exit(1);
    }

    // Initialisations 
    pthread_t threads[atoi(argv[1])];
    struct params tabParams[atoi(argv[1])];
    
    // Initialisation de rand pour la simulation de longs calculs
    srand(atoi(argv[1]));

    struct predicatRdv predicat;
    predicat.waitingThread = 0;
  
    // Création du verrou et de la variable conditionnelle
    pthread_mutex_t verrou;
    pthread_cond_t cond;
    pthread_mutex_init(&verrou, NULL);
    pthread_cond_init(&cond, NULL);

    // Création des threads 
    for (int i = 0; i < atoi(argv[1]); i++){
        tabParams[i].idThread = i + 1;
        tabParams[i].N = atoi(argv[1]);
        tabParams[i].varPartagee = &predicat;
        tabParams[i].verrou = &verrou;
        tabParams[i].cond = &cond;

        if (pthread_create(&threads[i], NULL, &participant, &tabParams[i]) != 0){
            perror("erreur creation thread");
            exit(1);
        }
    }

    // Attente de la fin des threads. Partie obligatoire 
    for (int i = 0; i < atoi(argv[1]); i++) {
        pthread_join(threads[i], NULL);
    }

    printf("[Thread principal] : fin de tous les threads secondaires\n");
    
    pthread_mutex_destroy(&verrou);
    pthread_cond_destroy(&cond);
    
    return 0;
}
 
