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

/* Programme serveur */

extern int errno;

int main(int argc, char *argv[]) {

   if (argc != 2){
      printf("utilisation : %s port_serveur\n", argv[0]);
      exit(1);
   }

   /* Etape 1 : créer une socket */   
   int ds = creerSocket();
   
   /* Etape 2 : Nommer la socket du serveur */
   struct sockaddr_in ad = nommerSocket(argv[1],ds);
   // afficher port
   socklen_t sizeAd = sizeof(ad);
   getsockname(ds, (struct sockaddr*) &ad, &sizeAd);
   printf("port: %i\n",ntohs(ad.sin_port));

   /* Etape 4: se connecter au client */
   struct sockaddr_in sockClient;
   socklen_t lgAdr;
   char str[INET_ADDRSTRLEN];
   char buffer[50000];
   // int sizeBuffer = 50000;
   int nbMaxAttente = 10;
   int res=-1;
   
   //écouter
   int resListen = listen(ds, nbMaxAttente);
   if (resListen == -1) {
      printf("Problème lors de l'écoute\n");
      printf("errno: %d , %s\n", errno, strerror(errno));
      exit(1);    
   }

   int tailleRecuDepuisDebut = 0;
   int nbAppelsRecv = 0;
   int dsClient;
   int parent = 0;
   /* Etape 4.5 : recevoir un message du client (voir sujet pour plus de détails)*/
   while (1) {
      //accepter une connexion
      dsClient = accept(ds, (struct sockaddr*)&sockClient, &lgAdr);

      if (dsClient == -1) {
         printf("Problème lors de la connexion\n");
         printf("errno: %d , %s\n", errno, strerror(errno));
         exit(1);
      } else {
         inet_ntop(AF_INET, &sockClient.sin_addr, str, INET_ADDRSTRLEN);
         printf("Connexion à l'adresse %s\n",str);

         if(fork() == 0) {
            //on est l'enfant
            close(ds);
            while(1) {
               //recevoir une taille de message à lire
               int taille;
               res = recvTCP(dsClient, &taille, sizeof(int));      
               //recevoir un message générique
               res = recvTCP(dsClient, buffer, taille);
               nbAppelsRecv++;
               if (res == -1) {
                  printf("Probleme de réception\n");
                  printf("errno: %d , %s\n", errno, strerror(errno));
                  close(dsClient);
                  continue;
               } else if (res == 0) {
                  printf("Connexion fermée côté client\n");
                  break;
               }
               //message string
               res = strlen(buffer)+1;
               printf("--- Message reçu de longueur %i\n",res);
               tailleRecuDepuisDebut += res;
               printf("Message: %s\n", buffer);
               printf("%i appels à recv (%i octets au total)\n", nbAppelsRecv, tailleRecuDepuisDebut);
            }
            break;

         } else {
            close(dsClient);
            parent = 1;
         }

      }

      
   }
   //fermer le lien à la socket cliente
   printf("Connexion à l'adresse %s fermée. \n", str);
   if (parent == 0) close(dsClient);
   /* Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)*/
   close(ds);
   printf("Serveur : je termine\n");
   return 0;

}
