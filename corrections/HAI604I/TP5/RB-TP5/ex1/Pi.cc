/*
 * fichier: semClient.c
 * auteur: Robin Boanca
 * date: 03/2022
 */

#include <stdlib.h>
#include <sys/types.h>
#include <iostream>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/msg.h>
#include <stdio.h> 
#include <unistd.h>


#define AUTORISATION 1
#define DEMANDE 2
#define RENDU 3
#define NONE 4
#define PCTRL_DEMANDE 1
#define PCTRL_RENDU 2

using namespace std;

struct bottleInOcean {
    long etiquette_adresse;
    int type_message;
    long etiquette_demandeur;
};

int main(int argc, char * argv[]){

    if (argc != 5) {
        cout << "Nbre d'args invalide, utilisation :" << endl;
        cout << argv[0] << " [fichier-pour-cle-ipc] [entier-pour-cle-ipc] [nb_procs] [nb_travaux]" << endl;
        exit(0);
    }

    key_t cle=ftok(argv[1], atoi(argv[2]));
    int nb_procs = atoi(argv[3]);
    int nb_travaux = atoi(argv[4]);

    if (cle==-1) {
        perror("Erreur ftok : ");
        exit(2);
    }

    cout << "ftok ok" << endl;
        
    int msgid = msgget(cle, 0666);
    if(msgid==-1) {
        perror("erreur msgget : ");
        exit(2);
    }
    
    cout << "msgget ok" << endl;

    struct bottleInOcean myBottle;
    ssize_t res;
    long myId = (long)3;
    size_t taille = sizeof(myBottle); // sizeof(myBottle.type_message) + sizeof(myBottle.etiquette_demandeur);

    while (nb_procs) {
        if (fork() != 0) break;
        myId++;
        nb_procs--;
    }

    for(int i=0; i<nb_travaux; i++) {
        cout << "\033[9" << myId%8 << "mPROC " << myId << " : démarrage sur zone " << i << "\033[0m" << endl;
        // envoyer une demande
        myBottle.etiquette_adresse = (long)PCTRL_DEMANDE;
        myBottle.type_message = (int)DEMANDE;
        myBottle.etiquette_demandeur = myId;
        res = msgsnd(msgid, &myBottle, taille, 0);
        if (res == -1) {
            perror("erreur msgsnd (DEMANDE)");
            exit(2);
        }
        // attente d'une autorisation
        res = msgrcv(msgid, &myBottle, taille, myId, 0);
        if (res == -1) {
            perror("erreur msgrcv (AUTORISATION)");
            exit(2);
        }
        if (myBottle.type_message != AUTORISATION) {
            cout << "\033[9" << myId%8 << "mPROC " << myId << " : j'attendais une autorisation, mais j'ai reçu " << myBottle.type_message << "\033[0m" << endl;
            exit(2);
        }
        /*
        ICI ON FAIT DES CALCULS DE MALADE
        HESITE PAS A RAJOUTER DES ZEROS
        */
        // for (int j=0; j<100000000000; j++);
        // rendre le verrou
        myBottle.etiquette_demandeur = myId;
        myBottle.etiquette_adresse = (long)PCTRL_RENDU;
        myBottle.type_message = (int)RENDU;
        res = msgsnd(msgid, &myBottle, taille, 0);
        if (res == -1) {
            perror("erreur msgsnd (RENDU)");
            exit(2);
        }
        cout << "\033[9" << myId%8 << "mPROC " << myId << " : fin de travail sur zone " << i << "\033[0m" << endl;
    }
    
    cout << "\033[9" << myId%8 << "mPROC " << myId << " : je termine" << "\033[0m" << endl;
    
    while(wait(0)!=-1);  // cette instruction permet d'attendre la fin de l'execution de tous mes fils.
    
    return 0;
}
