/**
 * fichier: bus.c
 * auteur: Johann Rosain
 * date: 09/04/2022
 **/
/*
  Programme bus � compl�ter. Les zones � compl�ter sont indiqu�es et il n'est pas n�cessaire d'ajouter de nouvelles traces d'ex�cution.
  
  Rappel pour le d�p�t : sur Moodle, donner les instructions pour la cr�ation et l'initisalisation du tableau de semaphores n�cessaires au lancement de ./bin/semInit (voir le sujet)
*/


#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <stdlib.h>
#include "simulation.h"

#define ERROR -1
#define EMBARQUEMENT 0
#define DEBARQUEMENT 1

typedef struct sembuf SemBuf;

int main(int argc, char * argv[]){
    if (argc != 4) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s nombre-places fichier-pour-cle-ipc entier-pour-cle-ipc\n", argv[0]);
        exit(0);
    }
        
    int cleSem = ftok(argv[2], atoi(argv[3]));
    int idSem = semget(cleSem, 1, 0666);

    // j'utilise semget de sorte a s'assurer que le tableau existe.
    if (idSem == -1){
        perror("erreur semget");
        exit(-1);
    }

    printf("Id tableau de semaphores : %d \n", idSem);
    
    int nbPlaces = atoi(argv[1]);

    SemBuf ops[] = { 
        (SemBuf) { .sem_num = EMBARQUEMENT, .sem_op = 0, .sem_flg = 0 }, 
        (SemBuf) { .sem_num = DEBARQUEMENT, .sem_op = nbPlaces, .sem_flg = 0 },
        (SemBuf) { .sem_num = DEBARQUEMENT, .sem_op = 0, .sem_flg = 0 },
        (SemBuf) { .sem_num = EMBARQUEMENT, .sem_op = nbPlaces, .sem_flg = 0 }, 
    };
        
    while(1) {
        if (semop(idSem, ops + 3, 1) == ERROR) {
            perror("Erreur: le tableau de sémaphores n'a pas pu être remis à 0 ");
            exit(EXIT_FAILURE);
        }

        // les traces d'ex�cution sont � garder inchang�es.
        printf("Bus : embarquement immediat, soyez les bienvenus! \n");
        if (semop(idSem, ops, 1) == ERROR) {
            perror("Erreur: la sémaphore n'a pas pu être mise en attente ");
            exit(EXIT_FAILURE);
        }

        printf("Bus : bus complet, la visite commence !\n"); 
        visite(10);
        printf("Bus : visite terminee, tout le monde descend !\n"); 
    
        if (semop(idSem, ops + 1, 1) == ERROR) {
            perror("Erreur: la sémaphore n'a pas pu être mise à niveau ");
            exit(EXIT_FAILURE);
        }
        
        printf("Bus : attendre que le bus soit vide\n");
        
        if (semop(idSem, ops + 2, 1) == ERROR) {
            perror("Erreur: la sémaphore n'a pas pu être mise en attente ");
            exit(EXIT_FAILURE);
        }
    }
    return 0;
}

