/*
 * fichier: Pctrl.cc
 * auteur: Robin Boanca
 * date: 03/2022
 */

#include <stdlib.h>
#include <sys/types.h>
#include <iostream>
#include <sys/ipc.h>
#include <sys/msg.h>
#include <stdio.h>  

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

    if (argc!=3) {
        cout << "Nbre d'args invalide, utilisation :" << endl;
        cout << argv[0] << " fichier-pour-cle-ipc entier-pour-cle-ipc" << endl;
        exit(0);
    }

    key_t cle=ftok(argv[1], atoi(argv[2]));

    if (cle==-1) {
        perror("Erreur ftok : ");
        exit(2);
    }

    cout << "ftok ok" << endl;
        
    int msgid = msgget(cle, IPC_CREAT|0666);
    if(msgid==-1) {
        perror("erreur msgget : ");
        exit(2);
    }
    
    cout << "msgget ok" << endl;

    struct bottleInOcean myBottle;
    ssize_t res;
    long curr_user = NONE;
    size_t taille = sizeof(myBottle); //sizeof(myBottle.type_message) + sizeof(myBottle.etiquette_demandeur);
    cout << taille << " " << sizeof(myBottle)-sizeof(long) << endl;

    while (1) {
        // vérification de l'absence de lock
        if (curr_user != NONE) {
            cout << "le lock appartient à " << curr_user << " alors qu'on entre dans la boucle" << endl;
            exit(2);
        }
        // etiquette PCTRL : premier message disponible qui lui est adressé
        res = msgrcv(msgid, &myBottle, taille, PCTRL_DEMANDE, 0);
        if (res == -1) {
            perror("erreur msgrcv (DEMANDE)");
            continue;
        }
        curr_user = myBottle.etiquette_demandeur;
        cout << "reception: res" << res << " - " << myBottle.etiquette_adresse << " " << myBottle.type_message << " " << myBottle.etiquette_demandeur << endl;
        cout << "Message reçu du Pi " << curr_user << endl;
        if (myBottle.type_message != DEMANDE) {
            cout << "problème, le message lu n'est pas une demande, mais " << myBottle.type_message << endl;
            continue;
        }
        // renvoyer une autorisation
        myBottle.etiquette_adresse = curr_user;
        myBottle.type_message = (int)AUTORISATION;
        res = msgsnd(msgid, &myBottle, taille, 0);
        if (res == -1) {
            perror("erreur msgsnd (AUTORISATION)");
            curr_user = NONE;
            continue;
        }
        cout << "message envoyé" << endl;
        // recevoir le rendu du lock
        res = msgrcv(msgid, &myBottle, taille, PCTRL_RENDU, 0);
        if (res == -1) {
            perror("erreur msgrcv (RENDU)");
            continue;
        }
        if (myBottle.type_message != RENDU) {
            cout << "le message de " << curr_user << " aurait du etre RENDU mais est " << myBottle.type_message << endl;
            continue;
        }
        if (myBottle.etiquette_demandeur != curr_user) {
            cout << "le lock est rendu pas " << myBottle.etiquette_demandeur << " alors qu'il appartient à " << curr_user << endl;
            continue;
        }
        curr_user = NONE;
    }
    
    return 0;
}
