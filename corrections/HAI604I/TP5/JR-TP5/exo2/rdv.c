/**
 * fichier: rdv.c
 * auteur: Johann Rosain
 * date: 23/03/2022
 **/
#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <stdlib.h>
#include <time.h>
#include <sys/wait.h>

#define ERROR -1

typedef int ipc_id; 

typedef union semun {
    int val;
    struct semid_ds *buf;
    ushort *array;
} SemUn;

typedef struct sembuf SemBuf;

void destructAndExit(ipc_id semid) {
    if (semctl(semid, 0, IPC_RMID) == ERROR) {
        perror("Erreur fatale lors de l'exécution du processus ");
    }
    exit(EXIT_FAILURE);
}

void calcul(int nProc) {
    int wait = (rand() % 6) + 1;
    printf("\033[%im[%i] Calcul d'environ %i secondes.\n\033[0m", nProc + 31, nProc, wait);
    sleep(wait);
}

/* Un RDV termine le processus (exit()) */
void rdv(int nProc, ipc_id idSem, int nbRdv) {
    // Initialisation du random pour le wait
    srand(time(NULL) ^ (getpid() << 16)); 
    for (int i = 0; i < nbRdv; ++i) {
        calcul(nProc);

        printf("\033[%im[%i] Calcul terminé, mise à jour du point de rendez-vous.\n\033[0m", nProc + 31, nProc);
        // On retire 1 du tableau de sémaphores car ce processus est arrivé au RDV
        SemBuf op[] = { (SemBuf){ .sem_num = i, .sem_op = -1, .sem_flg = 0 },
                        (SemBuf){ .sem_num = i, .sem_op = 0, .sem_flg = 0 } };
        if (semop(idSem, op, 1) == ERROR)
            exit(EXIT_FAILURE);

        // Récupération de semaphores[i] pour affichage
        int semValue = semctl(idSem, i, GETVAL, (SemUn){ .val = 0 });
        if (semValue == ERROR) 
            exit(EXIT_FAILURE);
        printf("\033[%im[%i] Valeur actuelle de la sémaphore : %i\n\033[0m", nProc + 31, nProc, semValue);

        // Tant que semaphores[i] n'est pas à 0, on attend.
        if (semop(idSem, op + 1, 1) == ERROR)
            exit(EXIT_FAILURE);
    }

    exit(EXIT_SUCCESS);
}

int main(int argc, char * argv[]){
    if (argc != 5) {
        printf("Utilisation: %s nombreRdv nombreProcessus fichierCle entierCle\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Création de la sémaphore.
    int nbSem = atoi(argv[1]);

    key_t clesem = ftok(argv[3], atoi(argv[4]));
    ipc_id idSem = semget(clesem, nbSem, IPC_CREAT|IPC_EXCL|0600);
    
    if(idSem == ERROR){
        perror("Erreur lors du semget ");
        exit(EXIT_FAILURE);
    }

    printf("ID de la sémaphore : %d\n", idSem);

    // Initialisation des sémaphores 
    ushort tabinit[nbSem];
    for (int i = 0; i < nbSem; ++i) 
        tabinit[i] = atoi(argv[2]);

    SemUn semaphores;
    semaphores.array = tabinit;

    if (semctl(idSem, nbSem, SETALL, semaphores) == ERROR) {
        perror("Erreur lors de l'initialisation des sémaphores ");
        destructAndExit(idSem);
    }

    semaphores.array = (ushort*)malloc(nbSem * sizeof(ushort)); 

    if (semctl(idSem, nbSem, GETALL, semaphores) == ERROR) {
        perror("Erreur d'initialisation des sémaphores ");
        destructAndExit(idSem);
    }
    
    printf("Valeurs des sempahores apres initialisation [ "); 
    for(int i = 0; i < nbSem - 1; i++) {
        printf("%d, ", semaphores.array[i]);
    } 
    printf("%d ] \n", semaphores.array[nbSem - 1]);

    for (int i = 0; i < atoi(argv[2]); ++i) {
        if (fork() == 0)
            rdv(i, idSem, nbSem);
    }

    // Attente des enfants 
    while (wait(NULL) > 0) ;

    free(semaphores.array);
    if (semctl(idSem, 0, IPC_RMID) == ERROR) {
        perror("Erreur lors de la fin du processus ");
    }
    return 0;
}
