/**
 * fichier: visiteur.c
 * auteur: Johann Rosain
 * date: 09/04/2022
 **/
/*
  Programme visiteur à compléter : les zones à compléter sont indiquées et il n'est pas nécessaire d'ajouter de nouvelles traces d'exécution. 
  
  Attention : dans ce programme, il n'y a aucun besoin de simuler un temps de visite. Le temps de visite est géré par le programme bus. Aussi, les actions de monter et de descendre ne sont pas a mettre en oeuvre. La synchronisation doit assurer que le bus soit vide avant un nouvel embarquement.
  
*/
#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <stdlib.h>

#define ERROR -1
#define EMBARQUEMENT 0
#define DEBARQUEMENT 1

typedef struct sembuf SemBuf;

int main(int argc, char * argv[]){
    if (argc!=4) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s monNumero fichier-pour-cle-ipc entier-pour-cle-ipc\n", argv[0]);
        exit(0);
    }
        
    int cleSem=ftok(argv[2], atoi(argv[3]));
    int idSem = semget(cleSem, 1, 0666);

    // j'utilise semget de sorte a s'assurer que le tableau existe.
    if (idSem == ERROR) {
        perror("erreur  semget");
        exit(-1);
    }

    int monNum = atoi(argv[1]);
    
    printf("Visiteur %d : Id tableau de semaphores : %d \n", monNum, idSem);
    
    // ... zone à utiliser si nécessaire.
        
    printf("Visiteur %d: je demande a monter \n", monNum);
    SemBuf ops[] = { 
        (SemBuf) { .sem_num = EMBARQUEMENT, .sem_op = -1, .sem_flg = 0 },
        (SemBuf) { .sem_num = DEBARQUEMENT, .sem_op = -1, .sem_flg = 0 },
    };

    if (semop(idSem, ops, 1) == ERROR) {
        perror("Erreur lors de l'embarquement ");
        exit(EXIT_FAILURE);
    }
       
    printf("Visiteur %d : je suis a bord et bien installe.\n", monNum); 
        
    if (semop(idSem, ops + 1, 1) == ERROR) {
        perror("Erreur lors du signal de débarquement ");
        exit(EXIT_FAILURE);
    }
        
    printf("Visiteur %d : visite terminee, je descends.\n", monNum);
    
    return 0;
}

