/*
 * fichier: semClient.c
 * auteur: Robin Boanca
 * date: 03/2022
 */

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/wait.h>
#include <stdlib.h>

union semun {
    int val ;                   /* cmd = SETVAL */
    struct semid_ds *buf;       /* cmd = IPC STAT ou IPC SET */
    unsigned short *array;      /* cmd = GETALL ou SETALL */
    struct seminfo* __buf;      /* cmd = IPC INFO (sous Linux) */
};

int main(int argc, char * argv[]){
    
    if (argc!=4) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s nombre-clients fichier-pour-cle-ipc entier-pour-clé-ipc\n", argv[0]);
        exit(0);
    }

    int clesem = ftok(argv[2], atoi(argv[3]));
    int nbSem = 2;
    int nbClient = atoi(argv[1]);
    int idSem=semget(clesem, nbSem, 0);
    if(idSem == -1) {
        perror("erreur semget : ");
        exit(-1);
    }
    printf("sem id : %d \n", idSem);

    int proc = 0;

    for (int i=1; i<nbClient; i++) {
        if (fork() == 0) {proc=i;break;}
    }

    printf("[PROC %i] : je me connecte au serveur\n", proc);

    struct sembuf opp;
    opp.sem_num = 0;
    opp.sem_op = -1;
    opp.sem_flg = 0;
    int res = semop(idSem, &opp, 1);
    if (res < 0) {
        printf("[PROC %i] : ", proc);
        perror("problème lors de la décrémentation du sem 0");
        exit(0);
    }

    printf("[PROC %i] : j'ai décrémenté\n", proc);

    opp.sem_num = 1;
    res = semop(idSem, &opp, 1);
    if (res < 0) {
        printf("[PROC %i] : ", proc);
        perror("problème lors de l'incrémentation du sem 1");
        exit(0);
    }

    printf("[PROC %i] : j'ai incrémenté\n", proc);

    while(wait(0)!=-1);
    return 0;
}
