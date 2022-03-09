/*
Author: Robin Boanca
Date: 10/02/2022
*/

#include <stdio.h>//perror
#include <sys/types.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>//close
#include <stdlib.h>
#include <string.h>
#include "tcp-utils.c"


#define MAX_BUFFER_SIZE 146980


int main(int argc, char *argv[])
{
    /* etape 0 : gestion des paramètres si vous souhaitez en passer */
    if (argc != 2){
        printf("utilisation : %s port_serveur\n", argv[0]);
        exit(1);
    }

    /* etape 1 : creer une socket d'écoute des demandes de connexions*/
    int ds = creerSocket();
    /* etape 2 : nommage de la socket */
    nommerSocket(argv[1],ds);
    /* etape 3 : mise en ecoute des demandes de connexions */
    char str[INET_ADDRSTRLEN];
    char buffer[MAX_BUFFER_SIZE];
    int nbMaxAttente = 10;
    listenTCP(ds, nbMaxAttente);

    /* etape 4 : plus qu'a attendre la demadne d'un client */
    struct sockaddr_in sockClient; 
    socklen_t lgAdr;

    while(1) {
        int dsClient = accept(ds, (struct sockaddr*) &sockClient, &lgAdr);

        if (dsClient == -1) {
            printf("Problème lors de la connexion\n");
            printf("errno: %d , %s\n", errno, strerror(errno));
            exit(1);
        } else {
            inet_ntop(AF_INET, &sockClient.sin_addr, str, INET_ADDRSTRLEN);
            printf("Connexion à l'adresse %s\n",str);

            if(fork() == 0) {

                int totalRecv = 0; // un compteur du nombre total d'octets recus d'un client

                // recevoir le filepath
                int taille = 0;
                recvTCP(dsClient, &taille, sizeof(int));
                char* tmpPath = (char*)malloc(taille);
                char* filepath = (char*)malloc(taille + 15);
                recvTCP(dsClient, tmpPath, taille);
                filepath[0] = '\0';
                strcat(filepath, "./reception/");
                strcat(filepath, tmpPath);
                free(tmpPath);
                printf("Nom du fichier: %s\n", filepath);

                // recevoir la taille du fichier
                int file_size;
                recvTCP(dsClient, &file_size, sizeof(int));
                
                // On ouvre le fichier dans lequel on va écrire
                FILE* file = openFileFTP(filepath, "wb");

                while(totalRecv < file_size) {
                    recvTCP(dsClient, &taille, sizeof(int));
                    totalRecv += recvTCP(dsClient, buffer, taille);
                    int written = fwrite(buffer, sizeof(char), taille, file);
                    if(written < taille) {
                        if(ferror(file) != 0){
                        perror("Serveur : erreur lors de l'écriture du fichier\n");
                        fclose(file);
                        exit(1);
                        } else {
                            printf("Serveur : arrivé a la fin du l'écriture du fichier\n");// fin du fichier
                            break;
                        }
                    }
                }

                printf("Serveur : ecriture dans fichier reussie.\n");
                printf("Serveur : path : %s (taille : %i octets)\n", filepath, file_size);
                // fermeture du fichier
                free(filepath);
                fclose(file);
                close(dsClient);

            } else {
                close(dsClient);
            }
        }
            
        
    }
    printf("Serveur : c'est fini\n");
    close(ds);
}







