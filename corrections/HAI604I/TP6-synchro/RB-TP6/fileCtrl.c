/*
 * fichier: fileCtrl.c
 * auteur: Robin Boanca
 * date: 04/2022
 */

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <signal.h>

#define DEMANDE 2
#define RENDU 1

const int numCle = 250;
const char* fichierCle = "fileCtrl.c";

static volatile int keepRunning = 1;

void intHandler(int dummy) {
    keepRunning = 0;
}

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

void afficheErreur(int id, char* err) {
    printf("%s[PROC %i] : %s%s\n", COL(id), id, err, FINCOL);
    printf("errno: %d , %s\n", errno, strerror(errno));
}

void afficheInfo(int id, char* info) {
    printf("%s[PROC %i] : %s%s\n", COL(id), id, info, FINCOL);
}

void destroySem(int idSem) {
    if (semctl(idSem, 0, IPC_RMID, NULL)==-1)
        afficheErreur(0, "erreur smctl, impossible de détruire le sémaphore");
}

void destroyMem(int memShare) {
    if (shmctl(memShare, IPC_RMID, NULL) < 0) {
        afficheErreur(0, "erreur destruction mémoire partagée");
    }
}

void destroyFile(int cleFile) {
    if (msgctl(cleFile, IPC_RMID, NULL) == -1)
        afficheErreur(0, "erreur suppression file de message :");
}

void enrobeSemOp(int idSem, int numSem, int op) {
    struct sembuf opp;
    opp.sem_num = numSem;
    opp.sem_op = op;
    opp.sem_flg = 0;
    int res = semop(idSem, &opp, 1);
    if (res < 0) {
        afficheErreur(0, "problème lors d'une opération sur le sémaphore");
        exit(1);
    }
}

union semun {
    int val ;                   /* cmd = SETVAL */
    struct semid_ds *buf;       /* cmd = IPC STAT ou IPC SET */
    unsigned short *array;      /* cmd = GETALL ou SETALL */
    struct seminfo* __buf;      /* cmd = IPC INFO (sous Linux) */
};

struct msg {
    long etiquette;
    int numRes;
    int cleRes;
    long demandeur;
};

struct Imprimante {
    int id;
    char contenu[200];
};

struct Planning {
    int id;
    long contenu[100];
};

struct Identifiant {
    int id;
    char nom[100];
    char prenom[100];
    unsigned long telephone;
};

int sizeRes[] = { sizeof(struct Imprimante), sizeof(struct Planning), sizeof(struct Identifiant) };

int main(int argc, char * argv[]){

    signal(SIGINT, intHandler);
    
    if (argc < 3) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s [nb-res-différente] [int] [int] [int] (pour chaque res le nb d'instances)\n", argv[0]);
        exit(0);
    }

    const int nbRes = atoi(argv[1]);
    if (nbRes <= 0) {
        printf("nb-res-differente doit être plus grand que 1 \n");
        exit(0);
    }
    if (nbRes > argc-2) {
        printf("Entrez un nombre d'instance pour chaque ressource différente\n");
        exit(0);
    }

    int cleRoulante = numCle+2;

    // init les tableaux de contenu (combien d'instances, clé des instances)
    int* nbInstances = (int*)malloc(sizeof(int)*nbRes);
    int** cleInstance = (int**)malloc(sizeof(int*)*nbRes);
    int** dispoInstance = (int**)malloc(sizeof(int*)*nbRes);
    for (int i=0; i<nbRes; i++) {
        nbInstances[i] = atoi(argv[i+2]);
        cleInstance[i] = (int*)malloc(sizeof(int)*atoi(argv[i+2]));
        dispoInstance[i] = (int*)malloc(sizeof(int)*atoi(argv[i+2]));
        for (int j=0; j < atoi(argv[i+2]); j++) {
            dispoInstance[i][j] = 1;
            cleInstance[i][j] = cleRoulante;
            cleRoulante++;
        }
    }

    printf("Tableau alloués\n");

    const int id = 0; // on est le fork 0 c'est ainsi
    // init le tableau de sémaphore
    int clesem = ftok(fichierCle, numCle);
    int idSem = semget(clesem, nbRes, IPC_CREAT | IPC_EXCL | 0600);
    if(idSem == -1) {
        afficheErreur(id, "erreur création sem: ");
        exit(-1);
    }
    ushort tabinit[nbRes];
    for (int i=0; i<nbRes; i++) tabinit[i] = nbInstances[i];

    union semun valinit;
    valinit.array = tabinit;
    // mettre les valeurs de valinit.array dans le sémaphore
    if (semctl(idSem, nbRes, SETALL, valinit) == -1){
        afficheErreur(id, "erreur initialisation sem : ");
        exit(1);
    }

    printf("Sémaphores instanciés\n");

    // init les tableaux avec la disponibilité et l'accès à chaque structure

    for (int i=0; i<nbRes; i++) {
        for (int j=0; j < nbInstances[i]; j++) {
            int memShare = shmget(cleInstance[i][j], sizeRes[i], IPC_CREAT | IPC_EXCL | 0666);
            if (memShare == -1){
                afficheErreur(id, "erreur shmget memShare");
                exit(-1);
            }
            if (i == 0) {
                struct Imprimante* instance = (struct Imprimante*)shmat(memShare, NULL, 0);
                instance->id = cleInstance[i][j];
                instance->contenu[0] = '\0';
                if (shmdt(instance) == -1)
                    afficheErreur(id, "impossible de se détacher du segment partagé");
            } else if (i == 1) {
                struct Planning* instance = (struct Planning*)shmat(memShare, NULL, 0);
                instance->id = cleInstance[i][j];
                for (int k=0; k<200; k++) instance->contenu[k] = 0;
                if (shmdt(instance) == -1)
                    afficheErreur(id, "impossible de se détacher du segment partagé");
            } else if (i == 2) {
                struct Identifiant* instance = (struct Identifiant*)shmat(memShare, NULL, 0);
                instance->id = cleInstance[i][j];
                instance->nom[0] = '\0';
                instance->prenom[0] = '\0';
                instance->telephone = 0;
                if (shmdt(instance) == -1)
                    afficheErreur(id, "impossible de se détacher du segment partagé");
            }
        }
    }

    printf("Mémoires créées\n");

    // init file de message
    key_t cleFile = ftok(fichierCle, numCle+1);
    if (cleFile == -1) {
        afficheErreur(0, "Erreur ftok : ");
        exit(2);
    }
    int fileId = msgget(cleFile, IPC_CREAT | 0666);
    if(fileId == -1) {
        afficheErreur(0, "Erreur msgget : ");
        exit(2);
    }
    struct msg message;
    ssize_t res;
    size_t taille = sizeof(message);

    printf("File de message créée\n");

    // boucle -> gérer la réincrémentation des sémaphores
    while(keepRunning) {
        res = msgrcv(fileId, &message, taille, -DEMANDE, 0);
        afficheInfo(0, "j'ai reçu un message");
        if (res == -1) {
            afficheErreur(id, "erreur msgrcv");
            continue;
        }
        if (message.etiquette == DEMANDE) {

            int found = -1;
            for (int j=0; j < nbInstances[message.numRes]; j++) {
                if (dispoInstance[message.numRes][j] == 1) {
                    found = j;
                    dispoInstance[message.numRes][j] = 0;
                }
            }
            if (found == -1) {
                afficheInfo(id, "On m'a demandé une ressource, je n'en ai pas trouvé dans mes instances");
            }
            printf("%s[PROC %i] : J'accorde une ressource du type %i%s\n", COL(id), id, message.numRes, FINCOL);
            // renvoyer un message donnant la ressource
            message.etiquette = message.demandeur;
            message.cleRes = cleInstance[message.numRes][found];
            message.demandeur = id;
            res = msgsnd(fileId, &message, taille, 0);
            if (res == -1) {
                afficheErreur(id, "erreur msgsnd");
                exit(2);
            }

        } else if (message.etiquette == RENDU) {

            int found = 0;
            for (int j=0; j < nbInstances[message.numRes]; j++) {
                if (cleInstance[message.numRes][j] == message.cleRes) {
                    found = 1;
                    dispoInstance[message.numRes][j] = 1;
                }
            }
            if (found == 0) afficheInfo(id, "On m'a rendu une ressource, je ne l'ai pas trouvée dans mes instances");
            else enrobeSemOp(idSem, message.numRes, 1);

            printf("%s[PROC %i] : On me rend une ressource du type %i%s\n", COL(id), id, message.numRes, FINCOL);

        } else {
            afficheErreur(id, "Message reçu n'est ni une demande ni un rendu, qoi.");
            continue;
        }
    }

    // frees
    // file
    destroyFile(fileId);
    // sem
    destroySem(idSem);
    // mem
    for (int i=0; i<nbRes; i++) {
        for (int j=0; j < nbInstances[i]; j++) {
            int memShare = shmget(cleInstance[i][j], sizeRes[i], 0666);
            destroyMem(memShare);
        }
    }
    // tabs
    free(nbInstances);
    for (int i=0; i<nbRes; i++) {
        free(cleInstance[i]);
        free(dispoInstance[i]);
    }
    free(cleInstance);
    free(dispoInstance);

    printf("Romans did salt the earth.\n");

    return 0;
}
