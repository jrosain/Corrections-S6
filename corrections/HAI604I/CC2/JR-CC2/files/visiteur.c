/**
 * fichier: visiteur.c
 * auteur: Johann Rosain
 * date: 09/04/2022
 **/
/*
  Programme visiteur à compléter : les zones à compléter sont indiquées et il n'est pas nécessaire d'ajouter de nouvelles traces d'exécution. 
  
 Vous devez expliquer en commentaires : le sens donné au messages echangés et aux étiquettes.
 
  Attention : dans ce programme, il n'y a aucun besoin de simuler un temps de visite. Le temps de visite est géré par le programme bus.
   
*/

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/ipc.h>
#include <sys/msg.h>
#include <stdlib.h>
#include "simulation.h"

#define ERROR -1
#define EMBARQUEMENT 1
#define DEBARQUEMENT 2

/* Envoi du numéro de l'utilisateur lors de chaque action qu'il entreprend. */
struct envoi {
    long mtype;
    int  visiteur;
};

/* Réception du numéro de l'utilisateur pour savoir si, oui ou non sa montée / descente est confirmée */
struct reception {
    long mtype;
    int  confirmation;
};

typedef struct envoi Envoi;
typedef struct reception Reception;

int main(int argc, char * argv[]){
    if (argc!=4) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s monNumero fichier-pour-cle-ipc entier-pour-cle-ipc\n", argv[0]);
        exit(0);
    }
        
    initDefault(50); // ne pas modifier ni déplacer cet appel.
    
    int cle = ftok(argv[2], atoi(argv[3]));
    int idFile = msgget(cle, 0666);

    // j'utilise msgget de sorte a s'assurer que la file existe.
    if (idFile == -1){
        perror("erreur  msgget");
        exit(-1);
    }

    int monNum = atoi(argv[1]);

    // On ajoute le numéro de la dernière étiquette utilisée + 1 pour qu'il n'y ait pas de conflit entre étiquettes.
    int realNum = monNum + DEBARQUEMENT + 1;
    
    printf("Visiteur %d : Id file msg : %d \n", monNum, idFile);
    printf("Visiteur %d: je demande a monter \n", monNum);

    // Envoi de la requête pour monter
    Envoi request = { .mtype = EMBARQUEMENT, .visiteur = realNum };
    ssize_t res = msgsnd(idFile, (const void *)&request, sizeof(int), 0);
    if (res == ERROR) {
        perror("Erreur lors de l'embarquement ");
        exit(EXIT_FAILURE);
    }

    // Réception de la confirmation de montée
    Reception conf;
    res = msgrcv(idFile, (void *)&conf, sizeof(int), realNum, 0);
    if (res == ERROR) {
        perror("Erreur lors de l'autorisation à embarquer ");
        exit(EXIT_FAILURE);
    }
    
    printf("Visiteur %d : je monte ...\n", monNum);
    monterOuDescendre();
    printf("Visiteur %d : je suis a bord et bien installe\n", monNum);
    
    // Envoi qu'on est bien monté
    request.mtype = realNum;
    res = msgsnd(idFile, (const void *)&request, sizeof(int), 0);
    if (res == ERROR) {
        perror("Erreur lors de l'embarquement ");
        exit(EXIT_FAILURE);
    }

    // Attente de savoir que le bus a terminé.
    Reception data;
    res = msgrcv(idFile, (void *)&data, sizeof(int), realNum, 0);
    if (res == ERROR) {
        perror("Erreur lors de la réception du message pour descendre ");
        exit(EXIT_FAILURE);
    }
    printf("Visiteur %d : visite terminee, je descends ...\n", monNum);
    monterOuDescendre();
    printf("Visiteur %d : je suis descendu.\n", monNum);  

    // On est bien descendu.
    request.mtype = DEBARQUEMENT; 
    request.visiteur = realNum;
    res = msgsnd(idFile, (const void *)&request, 0, 0);
    if (res == ERROR) {
        perror("Erreur lors du débarquement ");
        exit(EXIT_FAILURE);
    }
    
    return 0;
}

