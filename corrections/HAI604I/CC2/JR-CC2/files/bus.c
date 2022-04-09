/**
 * fichier: bus.c
 * auteur: Johann Rosain
 * date: 09/04/2022
 **/
/*
  Programme bus � compl�ter. Les zones � compl�ter sont indiqu�es et il n'est pas n�cessaire d'ajouter de nouvelles traces d'ex�cution.
  Vous devez expliquer en commentaires : le sens donn� au messages echang�s et aux �tiquettes.
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

struct envoi {
    long mtype;
    int  visiteur;
};

struct reception {
    long mtype;
    int  confirmation;
};

typedef struct envoi Envoi;
typedef struct reception Reception;

int main(int argc, char * argv[]){
    if (argc!=4) {
        printf("Nbre d'args invalide, utilisation :\n");
        printf("%s nombre-places fichier-pour-cle-ipc entier-pour-cle-ipc\n", argv[0]);
        exit(0);
    }
        
    
    int cle=ftok(argv[2], atoi(argv[3]));
    int idFile = msgget(cle, 0666);

    // j'utilise msgget de sorte a s'assurer que la file existe.
    if (idFile == ERROR){
        perror("erreur  msgget");
        exit(ERROR);
    }

    printf("Bus : Id File msg : %d \n", idFile);
    int nbPlaces = atoi(argv[1]);

    int visiteurs[nbPlaces]; size_t lenVisiteurs = 0;
    
    while(1) {
        
        // les traces d'ex�cution sont � garder inchang�es.
    
        printf("Bus : embarquement immediat, soyez les bienvenus! \n");
        
        int placesRestantes = nbPlaces;
        printf("Bus : attente que le bus soit complet \n");
        while (placesRestantes != 0) {
            // Réception d'une requête pour monter
            Envoi processusRequest;
            ssize_t res = msgrcv(idFile, (void *)&processusRequest, sizeof(processusRequest.visiteur), EMBARQUEMENT, 0);
            if (res == ERROR) {
                perror("Erreur lors de la demande d'embarquement ");
                break;
            }

            // OK, il peut monter
            Reception data = { .mtype = processusRequest.visiteur, .confirmation = 1 };
            res = msgsnd(idFile, (const void *)&data, sizeof(int), 0);
            if (res == ERROR) {
                perror("Erreur lors de l'embarquement d'un passager ");
                break;
            }
            placesRestantes--;
            visiteurs[lenVisiteurs++] = processusRequest.visiteur;

            // Attente qu'il soit bien monté
            res = msgrcv(idFile, (void *)&processusRequest, sizeof(processusRequest.visiteur), processusRequest.visiteur, 0);
            if (res == ERROR) {
                perror("Erreur lors de la demande d'embarquement ");
                break;
            }
        }
    
        printf("Bus : bus complet, la visite commence !\n");
        
        visite(4);
        
        printf("Bus : visite terminee, tout le monde descend !\n"); 
        
        // Demande à tous les visiteurs de bien vouloir quitter le bus.
        for (size_t i = 0; i < lenVisiteurs; ++i) {
            Reception data = { .mtype = visiteurs[i], .confirmation = 1 };
            ssize_t res = msgsnd(idFile, (const void *)&data, sizeof(int), 0);
            if (res == ERROR) {
                perror("Erreur lors de la demande de débarquement d'un visiteur ");
                break;
            }
        }
        
        printf("Bus : attendre que le bus soit vide\n");
        
        while (placesRestantes != nbPlaces) {
            Envoi processusRequest;
            ssize_t res = msgrcv(idFile, (void *)&processusRequest, sizeof(processusRequest.visiteur), DEBARQUEMENT, 0);
            if (res == ERROR) {
                perror("Erreur lors de la demande d'embarquement ");
                break;
            }

            // Vérification que le visiteur ait bien un ticket
            int found = 0;
            for (size_t i = 0; i < lenVisiteurs; ++i) {
                if (visiteurs[i] == processusRequest.visiteur)
                    found = 1;
            }
            if (!found) {
                printf("Erreur: le visiteur %d a demandé est descendu mais n'est jamais monté dans le bus.\n", processusRequest.visiteur);
                break;
            }
            placesRestantes++;
        }
        lenVisiteurs = 0;
    }
    return 0;
}

