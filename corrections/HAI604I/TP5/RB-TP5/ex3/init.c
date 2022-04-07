/*
 * fichier: init.c
 * auteur: Robin Boanca
 * date: 04/2022
*/


#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <sys/wait.h>
#include <stdlib.h>
#include <math.h>

/*
création et initialisation d'un tableau de sémaphores pour le
traitement synchronisé. Le nombre d'éléments correspond au nombre de
traitements -1 et les valeurs initiales sont à 0 (à la case i, la
valeur correspond à la dernière zone traitée par le processus
P_(i+1))

création d'un segment de memoire partagé qui sera un tableau d'entier (un élément correspondra à une zone)
*/

union semun {
    int val ;                   /* cmd = SETVAL */
    struct semid_ds *buf;       /* cmd = IPC STAT ou IPC SET */
    unsigned short *array;      /* cmd = GETALL ou SETALL */
    struct seminfo* __buf;      /* cmd = IPC INFO (sous Linux) */
};

const char* FINCOL = "\033[0m";

const char* COL(int n) {
    n = n%8;
    if (n == 0) return "\033[90m";
    if (n == 1) return "\033[91m";
    if (n == 2) return "\033[92m";
    if (n == 3) return "\033[93m";
    if (n == 4) return "\033[94m";
    if (n == 5) return "\033[95m";
    if (n == 6) return "\033[96m";
    return "\033[97m";
}

void calculeMoiCommeUneDeTesFrancaises() {
    for (int i=0; i<500000000; i++) {
        double a = sqrt((long)159631*157571);
        a++;
    }
}

int main(int argc, char * argv[]){
    
    if (argc!=5) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s nombre-traitements nombre-zones fichier-pour-cle-ipc entier-pour-clé-ipc\n", argv[0]);
        exit(0);
    }
    int nbZones = atoi(argv[2]);
    int cle = ftok(argv[3], atoi(argv[4]));
    int nbSem = atoi(argv[1]) -1;
    int idSem=semget(cle, nbSem, IPC_CREAT | IPC_EXCL | 0600);
    if(idSem == -1){
        perror("erreur semget");
        exit(-1);
    }
    printf("sem id : %d \n", idSem);
    
    // initialisation des sémaphores à 0
    ushort tabinit[nbSem];
    for (int i = 0; i < nbSem; i++) tabinit[i] = 0;

    union semun valinit;
    valinit.array = tabinit;
    if (semctl(idSem, nbSem, SETALL, valinit) == -1){
        perror("erreur initialisation sem : ");
        exit(1);
    }

    /* test affichage des valeurs des sémaphores du tableau */
    valinit.array = (ushort*)malloc(nbSem * sizeof(ushort));
    if (semctl(idSem, nbSem, GETALL, valinit) == -1){
        perror("erreur initialisation sem : ");
        exit(1);
    } 
    printf("Valeurs des sempahores apres initialisation [ "); 
    for(int i=0; i < nbSem-1; i++){
        printf("%d, ", valinit.array[i]);
    }
    printf("%d ] \n", valinit.array[nbSem-1]);
    free(valinit.array);

    // création et initialisation du segment de mémoire partagée :
    // on réutilise la méme clé puisque la numérotation des IPC dépend du type d'objet.
    int laMem = shmget(cle, nbZones*sizeof(int), IPC_CREAT | IPC_EXCL | 0600);
    if (laMem == -1){
        perror("erreur shmget : ");
        exit(-1);
    }
    printf("Creation segment de mémoire ok. mem id : %d \n", laMem);
    //attachement au segment pour pouvoir y accéder
    int * p_att = (int *)shmat(laMem, NULL, 0);
    if (p_att== (int *)-1){
        perror("erreur shmat : ");
        exit(-1);
    }
    // j'ai un pointeur sur le segment, j'initialise le tableau 
    for(int i=0; i < nbZones; i++){
        p_att[i] = 0;
    }
    // détachement pour signaler au système la fin de l'utilisation du segment
    if (shmdt(p_att) == -1){
        perror("erreur shmdt : ");
        exit(-1);
    }

    printf("Zone mémoire partagée correctement initialisée.\n");

    int nbProc = atoi(argv[1]);
    int proc = 0;
    for (int i=1; i<nbProc; i++) {
        if (fork() == 0) {
            proc = i;
            break;
        }
    }
    printf("%s[PROC %i] : je commence le long cheminement vers la fierté du travail accompli%s\n", COL(proc), proc, FINCOL);

    laMem = shmget(cle, atoi(argv[2])*sizeof(int), 0600);
    if (laMem == -1){
        printf("[PROC %i]", proc);
        perror("erreur shmget : ");
        exit(-1);
    }
    printf("%s[PROC %i] : j'ai ouvert mes chakras%s\n", COL(proc), proc, FINCOL);

    int* memPart = (int *)shmat(laMem, NULL, 0);
    if (memPart == (int *)-1){
        printf("%s[PROC %i] : impossible de se rattacher au segment partagé%s\n", COL(proc), proc, FINCOL);
        perror("erreur shmat : ");
        exit(-1);
    }

    // pour chaque proc (à part 0 qui n'attends personne)
    // on travaille sur chaque zone dans l'ordre
    // pour savoir si on peut travailler sur une zone, on prend 1 dans le sémaphore du proc précédent
    // une fois le travail sur une zone terminé, on ajoute 1 dans notre sémaphore
    // voilà c'est tout trkl

    struct sembuf opp;

    for (int i=0; i<nbZones; i++) {
        if (proc == 0) {  // le processus zéro n'attend personne
            //calcul complexe
            calculeMoiCommeUneDeTesFrancaises();
            memPart[i]++;
            opp.sem_num = proc;
            opp.sem_op = 1;
            opp.sem_flg = 0;
            int res = semop(idSem, &opp, 1);
            if (res < 0) {
                printf("%s[PROC %i] : problème lors de l'incrémentation de mon sémaphore%s\n", COL(proc), proc, FINCOL);
                perror("inc");
                exit(0);
            }
            printf("%s[PROC %i] : je me rapproche un peu plus de la plenitude (%i / %i)%s\n", COL(proc), proc, i+1, nbZones, FINCOL);
        } else {
            // prendre un dans le sémaphore précédent
            opp.sem_num = proc-1;
            opp.sem_op = -1;
            opp.sem_flg = 0;
            int res = semop(idSem, &opp, 1);
            if (res < 0) {
                printf("%s[PROC %i] : problème lors de la décrémentation du sémaphore précédent%s\n", COL(proc), proc, FINCOL);
                perror("dec");
                exit(0);
            }
            // calculer
            calculeMoiCommeUneDeTesFrancaises();
            memPart[i]++;
            // ajouter un au sémaphore suivant
            // le dernier proc n'incrémente pas de sémaphore
            if (proc < nbSem) {     
                opp.sem_num = proc;
                opp.sem_op = 1;
                opp.sem_flg = 0;
                res = semop(idSem, &opp, 1);
                if (res < 0) {
                    printf("%s[PROC %i] : problème lors de l'incrémentation de mon sémaphore%s\n", COL(proc), proc, FINCOL);
                    perror("inc");
                    exit(0);
                }
            }
            printf("%s[PROC %i] : je me rapproche un peu plus de la plenitude (%i / %i)%s\n", COL(proc), proc, i+1, nbZones, FINCOL);
        }
    }

    printf("%s[PROC %i] : je laisse mon enveloppe physique derrière moi: %s[", COL(proc), proc, FINCOL);
    for (int i=0; i<nbZones; i++) {
        printf(" %i", memPart[i]);
    }
    printf(" ]\n");

    if (shmdt(memPart) == -1){
        printf("%s[PROC %i] : impossible de se détacher du segment partagé%s\n", COL(proc), proc, FINCOL);
        perror("erreur shmdt : ");
        exit(-1);
    }
    printf("%s[PROC %i] : j'ai atteint le total détachement de toute vicissitude terrestre%s\n", COL(proc), proc, FINCOL);
    

    while(wait(0)!=-1);
    if (proc == 0) {
        printf("DESTRUCTION MAXIMALE\n");
        if (shmctl(laMem, IPC_RMID, NULL) < 0) {
            perror("erreur destruction mémoire partagée");
        }
        if (semctl(idSem, 0, IPC_RMID, NULL)==-1)
            perror("erreur destruction sémaphores");
    }
    return 0;
}
