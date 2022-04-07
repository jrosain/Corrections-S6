/*
 * fichier: utilisateur.c
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
#include <sys/wait.h>
#include <signal.h>

#define DEMANDE 2
#define RENDU 1

const char* fichierCle = "fileCtrl.c";
const int numCle = 250;
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
    
    if (argc < 3) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s [nb-forks] [nb-opérations]\n", argv[0]);
        exit(0);
    }

    const int nbForks = atoi(argv[1]);
    const int nbOpe = atoi(argv[2]);
    const int nbRes = 3;

    srand((unsigned)25);

    // se connecter au sémaphore
    int clesem = ftok(fichierCle, numCle);
    int idSem = semget(clesem, nbRes, 0600);
    if(idSem == -1) {
        afficheErreur(20, "erreur connexion sémaphore");
        exit(-1);
    }

    // se connecter à la file
    key_t cleFile = ftok(fichierCle, numCle+1);
    if (cleFile == -1) {
        afficheErreur(0, "Erreur ftok : ");
        exit(2);
    }
    int fileId = msgget(cleFile, 0666);
    if(fileId == -1) {
        afficheErreur(0, "Erreur msgget : ");
        exit(2);
    }
    struct msg message;
    ssize_t res;
    size_t taille = sizeof(message);

    int id = 20;
    // créer les forks
    for (int i=0; i<nbForks; i++) {
        if (fork() != 0) {
            break;
        }
        id++;
    }
    afficheInfo(id, "Je suis le fork qui commence à travailler");
    
    // lancer les opérations
    for (int op=0; op<nbOpe; op++) {
        afficheInfo(id, "Je commence une nouvelle opération");
        int type = rand()%nbRes;
        printf("%s[PROC %i] : Je veux faire une opération sur la %i struct%s\n", COL(id), id, type, FINCOL);
		
        // prendre la ressource dans le sémaphore
        enrobeSemOp(idSem, type, -1);
        afficheInfo(id, "une instance de la struct est disponible");
		
        // envoyer un message demandant l'adresse
        message.etiquette = DEMANDE;
        message.numRes = type;
        message.demandeur = id;
        res = msgsnd(fileId, &message, taille, 0);
        if (res == -1) {
            afficheErreur(id, "erreur msgsnd");
            exit(2);
        }
		
        // attendre un message pour obtenir l'adresse
        res = msgrcv(fileId, &message, taille, id, 0);
        if (res == -1) {
            afficheErreur(id, "erreur msgrcv");
            continue;
        }
        afficheInfo(id, "message reçu de la part du controleur");
		
        // s'attacher à l'adresse
        int cleRes = message.cleRes;
        int memShare = shmget(cleRes, sizeRes[type], 0666);
        if (memShare == -1){
            afficheErreur(id, "erreur shmget memShare");
            exit(-1);
        }
        afficheInfo(id, "clé mémoire partagée correcte");
		
        // rentrer des valeurs au pif puis se détacher
        if (type == 0) {
            struct Imprimante* instance = (struct Imprimante*)shmat(memShare, NULL, 0);
            instance->id = cleRes;
            instance->contenu[50] = '\0';
            for (int i=0; i<50; i++) {
                char* alpha = "abcdefghijklmnopqrstuvwxyz";
                instance->contenu[i] = alpha[rand()%26];
            }
            if (shmdt(instance) == -1)
                afficheErreur(id, "impossible de se détacher du segment partagé");
        } else if (type == 1) {
            struct Planning* instance = (struct Planning*)shmat(memShare, NULL, 0);
            instance->id = cleRes;
            for (int k=0; k<200; k++) instance->contenu[k] = (long)rand()%100;
            if (shmdt(instance) == -1)
                afficheErreur(id, "impossible de se détacher du segment partagé");
        } else if (type == 2) {
            struct Identifiant* instance = (struct Identifiant*)shmat(memShare, NULL, 0);
            instance->id = cleRes;
            instance->nom[50] = '\0';
            for (int i=0; i<50; i++) {
                char* alpha = "abcdefghijklmnopqrstuvwxyz";
                instance->nom[i] = alpha[rand()%26];
            }
            instance->prenom[25] = '\0';
            for (int i=0; i<25; i++) {
                char* alpha = "abcdefghijklmnopqrstuvwxyz";
                instance->prenom[i] = alpha[rand()%26];
            }
            instance->telephone = (long)rand()%0666666666;
            if (shmdt(instance) == -1)
                afficheErreur(id, "impossible de se détacher du segment partagé");
        }
        afficheInfo(id, "modification et détachement de la mémoire partagée");
		
        // envoyer un message de rendu
        message.etiquette = RENDU;
        message.numRes = type;
        message.demandeur = id;
        res = msgsnd(fileId, &message, taille, 0);
        if (res == -1) {
            afficheErreur(id, "erreur msgsnd");
            exit(2);
        }
        afficheInfo(id, "message de rendu envoyé");
    }

    while(wait(0)!=-1);
    printf("Processus enfants ont terminé, on arrête\n");
    return 0;
} 