/**
 * fichier: traitement.c
 * auteur: Johann Rosain
 * date: 23/03/2022
 **/
#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <time.h>

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

int format(int n) {
    return (n % 10) + 31;
}

void calcul(int zone, int nProc) {
    int wait = (rand() % 10) + 1;
    printf("\033[%im[%i] Début du traitement de la zone %i. Environ %i secondes restante.\n\033[0m", format(nProc), nProc, zone, wait);
    sleep(wait);
}

/* Traite l'image avec le traitement numéro numProcessus. */
void traitement(key_t sharedMem, ipc_id idSem, int nZones, int numProcessus) {
    // Initialisation du random pour le wait
    srand(time(NULL) ^ (getpid() << 16)); 
    // Récupération de la mémoire partagée
    int *sharedData = (int *)shmat(sharedMem, NULL, 0);
    if (sharedData == (int *)ERROR) {
        perror("Erreur lors du shmat (attachement de la mémoire partagée) ");
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < nZones; ++i) {
        // Pas besoin de le faire pour le processus 0, il vit sa vie normal
        if (numProcessus != 0) {
            // Sinon, on récupère la valeur de la sémaphore de numProcessus - 1
            int semValue = semctl(idSem, numProcessus - 1, GETVAL, (SemUn){ .val = 0 });
            if (semValue == ERROR) 
                exit(EXIT_FAILURE);

            // Si semValue == i, on attend
            if (semValue == i + 1) {
                printf("\033[%im[%i] Attente de la zone %i.\n\033[0m", format(numProcessus), numProcessus, i);
                SemBuf op[] = { (SemBuf){ .sem_num = numProcessus - 1, .sem_op = 0, .sem_flg = 0 } };
                if (semop(idSem, op, 1) == ERROR)
                    exit(EXIT_FAILURE);
            }
        }

        calcul(i, numProcessus);
        // Modification de la mémoire partagée
        int x = sharedData[i];
        sharedData[i] = 3*x*x*x*x + 7*x*x*x - 5*x + 1;
        printf("\033[%im[%i] Fin du traitement de la zone %i.\nÉtat du tableau: %i\n\033[0m", format(numProcessus), numProcessus, i, sharedData[i]);

        // Augmentation de la sémaphore pour débloquer les autres processus
        SemBuf op[] = { (SemBuf) { .sem_num = numProcessus, .sem_op = -(i + 1), .sem_flg = 0 },
                        (SemBuf) { .sem_num = numProcessus, .sem_op = i + 2, .sem_flg = 0 } };
        if (semop(idSem, op, 1) == ERROR)
            exit(EXIT_FAILURE);
        if (semop(idSem, op + 1, 1) == ERROR)
            exit(EXIT_FAILURE);
    }

    // Détachement de la mémoire partagée
    if (shmdt(sharedData) == ERROR) {
        perror("Erreur lors du détachement du segment mémoire partagée ");
        exit(EXIT_FAILURE);
    }

    exit(EXIT_SUCCESS);
}

int main(int argc, char * argv[]) {
    if (argc != 4) {
        printf("Utilisation: %s nombreTraitements nombreZones fichierCle\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Création de la sémaphore
    int nbSem = atoi(argv[1]);
    key_t key = ftok(argv[3], 73);
    ipc_id idSem = semget(key, nbSem, IPC_CREAT | IPC_EXCL | 0600);
    
    if(idSem == ERROR) {
        perror("Erreur lors du semget ");
        exit(EXIT_FAILURE);
    }

    printf("ID de la sémaphore : %d\n", idSem);
    
    ushort tabinit[nbSem];
    for (int i = 0; i < nbSem; i++) 
        tabinit[i] = 1;
    
    SemUn semaphores = (SemUn) { .array = tabinit };

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

    free(semaphores.array);

    // Création et initialisation du segment de mémoire partagé 

    ipc_id sharedMem = shmget(key, atoi(argv[2]) * sizeof(int), IPC_CREAT | IPC_EXCL | 0600);
    if (sharedMem == ERROR) {
        perror("Erreur lors du shmget ");
        destructAndExit(idSem);
    }

    printf("Segment mémoire bien créé. ID : %d\n", sharedMem);
    
    // On attache le segment pour y accéder.
    int *p_att = (int *)shmat(sharedMem, NULL, 0);
    if (p_att == (int *)ERROR) {
        perror("Erreur lors du shmat (attachement de la mémoire partagée) ");
        destructAndExit(idSem);
    }

    // Initialisation du tableau
    for(int i = 0; i < atoi(argv[2]); i++)
        p_att[i] = 0;

    // Début du traitement multiprocessus
    for (int i = 0; i < atoi(argv[1]); ++i) {
        if (fork() == 0) {
            traitement(sharedMem, idSem, atoi(argv[2]), i);
        }
    }

    // Attente des enfants 
    while (wait(NULL) > 0) ;

    if (semctl(idSem, 0, IPC_RMID) == ERROR) {
        perror("Erreur lors de la fin du processus ");
    }

    if (shmdt(p_att) == ERROR) {
        perror("Erreur lors du détachement du segment mémoire partagée ");
    }

    if (shmctl(sharedMem, IPC_RMID, NULL) == ERROR) {
        perror("Erreur lors de la suppression du bloc de mémoire partagé ");
        exit(EXIT_FAILURE);
    }
    
    return 0;
}
