/*
 * fichier: semInit.c
 * auteur: Robin Boanca
 * date: 03/2022
 */

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
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
        printf("%s nombre-proc-en-attente fichier-pour-cle-ipc entier-pour-clé-ipc\n", argv[0]);
        exit(0);
    }

    int clesem = ftok(argv[2], atoi(argv[3]));
    int nbSem = 2;
    int nbClient = atoi(argv[1]);
    int idSem=semget(clesem, nbSem, IPC_CREAT | IPC_EXCL | 0600);
    if(idSem == -1) {
        perror("erreur semget : ");
        exit(-1);
    }
    printf("sem id : %d \n", idSem);

    // initialisation des sémaphores a la valeur passée en paramètre (faire autrement pour des valeurs différentes ):
    ushort tabinit[nbSem];
    tabinit[0] = nbClient;
    tabinit[1] = 0;

    union semun valinit;
    valinit.array = tabinit;
    // mettre les valeurs de valinit.array dans le sémaphore
    if (semctl(idSem, nbSem, SETALL, valinit) == -1){
        perror("erreur initialisation sem : ");
        exit(1);
    }

    /* test affichage valeurs des sémaphores du tableau */
    valinit.array = (ushort*)malloc(nbSem * sizeof(ushort)); // pour montrer qu'on récupère bien un nouveau tableau dans la suite

    // récupérer les valeurs du sémaphore et les mettre dans valinit.array
    if (semctl(idSem, nbSem, GETALL, valinit) == -1){
        perror("erreur initialisation sem : ");
        exit(1);
    } 
    
    printf("Valeurs des sémaphores après initialisation [ "); 
    for(int i=0; i < nbSem-1; i++){
        printf("%d, ", valinit.array[i]);
    }
    printf("%d ] \n", valinit.array[nbSem-1]);

    // définir la série de deux opérations
    struct sembuf op[] = {
        {(ushort)0,(short)0,0},
        {(ushort)1,(short)nbClient,0}
    };

    // attendre que le premier sémaphore soit à zéro
    // une fois à zéro, on lance le jeu aka on met le second sémaphore au nombre indiqué
        
    int res = semop(idSem, op, 2);
    if (res < 0) {
        printf("%i\n",op[1].sem_op);
        perror("Problème sur les opérations");
    }

    // if (semop(idSem, &op[0], 1) < 0) perror("dec");
    // if (semop(idSem, &op[1], 1) < 0) perror("inc");
        


    free(valinit.array);
    return 0;
}
