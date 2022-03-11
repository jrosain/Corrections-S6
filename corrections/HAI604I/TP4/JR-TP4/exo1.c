/**
 * fichier: exo1.c
 * auteur: Johann Rosain
 * date: 11/03/2022
 **/
#include <string.h>
#include <stdio.h>
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

#include "calcul.h"


struct paramsFonctionThread {
    int idThread;
    int waitSeconds;
    // Question 4
    int *data;
};


void * fonctionThread (void * params){
    struct paramsFonctionThread * args = (struct paramsFonctionThread *) params;

    printf("[%i] Calcul de durée : %i secondes. Donnée = %i. Début.\n", args->idThread, args->waitSeconds*3, *args->data);
    // Question 4/5 : il se passe des trucs bizarres à cause de cette ligne !
    *(args->data) += 1;
    calcul(args->waitSeconds);
    /*
    Question 3 : cet exit ferme le programme ; les autres threads ne finissent pas et l'exécution 
    ne dépasse pas cette étape. 
    if (args->waitSeconds > 1) {
        exit(EXIT_FAILURE);
    }
    */
    *(args->data) += args->waitSeconds;
    printf("[%i] Calcul de durée : %i secondes. Donnée = %i. Fin.\n", args->idThread, args->waitSeconds*3, *args->data);
    free(args);
    pthread_exit(NULL);
}


int main(int argc, char * argv[]){
    if (argc < 2) {
        printf("Utilisation: %s nombre_threads\n", argv[0]);
        return 1;
    }

    pthread_t threads[atoi(argv[1])];
    int data = 0;

    for (int i = 0; i < atoi(argv[1]); i++) {
        // Initialisation des paramètres
        struct paramsFonctionThread *args = (struct paramsFonctionThread *)malloc(sizeof(struct paramsFonctionThread));
        args->idThread = i;
        args->data = &data;
        if (i % 2 == 0) {
            args->waitSeconds = i / 2;
        }
        else {
            args->waitSeconds = i;
        }
        if (pthread_create(&threads[i], NULL, fonctionThread, args) != 0){
            perror("Erreur : problème lors de la création du thread ");
            exit(EXIT_FAILURE);
        }
    }

    // Question 2 : si on n'attend pas toutes les tâches, le calcul s'arrête et on n'obtient pas tous les résultats attendus.
    for (int i = 0; i < atoi(argv[1]); ++i) {
        pthread_join(threads[i], NULL);
    }

    return 0;
 
}
 
