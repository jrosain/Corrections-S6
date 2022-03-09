/*
Author: Robin Boanca
Date: 09/02/2022
*/

#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <string.h>
#include <errno.h>
#include "sendrecvTCP.c"

/* Programme client */

extern int errno;

int main(int argc, char *argv[]) {
    if (argc != 4){
        printf("utilisation : %s ip_serveur port_serveur port_client\n", argv[0]);
        exit(1);
    }
    /* Etape 1 : créer une socket, SOCK_STREAM pour TCP */   
    int ds = creerSocket();
    
    /* Etape 2 : Nommer la socket du client */
    struct sockaddr_in ad = nommerSocket(argv[3], ds);

    //afficher le contenu
    socklen_t size = sizeof(ad);
    getsockname(ds, (struct sockaddr*) &ad, &size);
    printf("%s:%i\n", inet_ntoa(ad.sin_addr), ntohs((short) ad.sin_port));

    /* Etape 3 : Désigner la socket du serveur */
    struct sockaddr_in sockServ;
    sockServ.sin_family = AF_INET;
    int resConvertAddr = inet_pton(AF_INET, argv[1], &(sockServ.sin_addr));
    if(resConvertAddr == 1) {
        printf("Adresse IP correctement convertie\n");
    } else {
        printf("Problème à la conversion de l'adresse IP\n");
        printf("errno: %d , %s\n", errno, strerror(errno));
        exit(1);
    }
    sockServ.sin_port = htons((short)atoi(argv[2]));
    socklen_t lgAdr = sizeof(struct sockaddr_in);

    /* Etape 3.5 : demander la connexion au serveur */
    int resConnexion = connect(ds, (struct sockaddr *)&sockServ, lgAdr);
    if (resConnexion == 0) {
        printf("Connexion réussie\n");
    } else {
        printf("Connexion impossible\n");
        printf("errno: %d , %s\n", errno, strerror(errno));
        exit(-1);
    }

    /* Etape 4 : envoyer un message au serveur  (voir sujet pour plus de détails)*/
    int choix = -1;
    char option[10];
    ssize_t resultat;
    int tailleDesEnvoisDepuisLeDebut = 0;
    // int res;
    while(choix != 0) {
        choix = -1;
        printf("\n-------------------\nChoisir une option:\n");
        printf("a - Quitter\n");
        printf("1 - Envoyer un message\n");
        printf("2 - Envoyer un message en boucle\n");
        printf("Votre choix: ");
        fgets(option, sizeof(option), stdin);
        switch(option[0]) {
            case '1':
                choix = 1;
                break;
            case '2':
                choix = 2;
                break;
            case 'a':
                choix = 0;
                break;
        }
        if(choix != 0 && choix != -1) {
            int taille=0;
            // message
            char msgEnvoi[200];
            printf("Envoyer un message: ");
            fgets(msgEnvoi, sizeof(msgEnvoi), stdin);
            taille = strlen(msgEnvoi)+1; // +1 '\0'
            // envoi en boucle?
            int nbEnvoi = 1;
            if (choix == 2) {
                printf("L'envoyer combien de fois ? ");
                scanf("%i", &nbEnvoi);
            }
            if (nbEnvoi < 1) {
                nbEnvoi = 1;
            }
            // envoi au serveur
            for(int i=0; i<nbEnvoi; i++) {
                // envoyer la taille du message qui doit parvenir au serveur
                resultat = sendTCP(ds, &taille, sizeof(int));
                // envoyer le message
                resultat = sendTCP(ds, msgEnvoi, taille);
                if (resultat == -1) {
                    printf("Problème lors de l'envoi du message\n");
                    printf("errno: %d , %s\n", errno, strerror(errno));
                    continue;
                }
                printf("Message envoyé de longueur %li, taille supposée: %i (appel %i/%i)\n",resultat, taille, i+1, nbEnvoi);
                tailleDesEnvoisDepuisLeDebut += taille;
                printf("Total des envois depuis le lancement du client: %i octets\n", tailleDesEnvoisDepuisLeDebut);
            }
            // reponse du serveur
            // char reponse[10];
            // res=recvTCP(ds, reponse, 10);
            // if(res > 0) {
            //     printf("Réponse reçue : \"%s\"\n",reponse);
            //     // if (atoi(reponse) == taille) {
            //     //     printf("Correspond à la taille du message envoyé\n");
            //     // } else {
            //     //     printf("DIFFERENT DE LA TAILLE DU MESSAGE ENVOYE\n");
            //     // }
            // } else if (res == -1) {
            //     printf("Problème lors de l'attente d'une réponse\n");
            //     printf("errno: %d , %s\n", errno, strerror(errno));
            //     break;
            // } else if (res == 0) {
            //     printf("Connexion fermée côté serveur\n");
            //     break;
            // }
            choix = -1;
        }
    }

    /* Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)*/
    close(ds);
    printf("Client : je termine\n");
    return 0;

}
