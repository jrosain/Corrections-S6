/*
Author: Robin Boanca
Date: 06/02/2022
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

int creerSocket() {
    int ds = socket(PF_INET, SOCK_STREAM, 0);
    if (ds == -1){
        perror("Serveur : pb creation socket :");
        exit(1); 
    }
    printf("Serveur : creation de la socket réussie \n");
    return ds;
}

struct sockaddr_in nommerSocket(char* port, int ds) {
    struct sockaddr_in ad;
    ad.sin_family = AF_INET;
    ad.sin_addr.s_addr = INADDR_ANY;
    if(atoi(port) != -1) {
        ad.sin_port = htons((short) atoi(port));
    }
    int res;
    res = bind(ds, (struct sockaddr*)&ad, sizeof(ad));
    if (res == 0) {
        printf("Socket nommée avec succès\n");
    } else {
        printf("Socket non nommée : %i \n", res);
        printf("errno: %d , %s\n", errno, strerror(errno));
        exit(1);
    }
    return ad;
}

int sendTCP(int sock, void* msg, int sizeMsg) {
    int res;
    int sent=0;
    //boucle d'envoi
    while(sent < sizeMsg) {
        //printf("Reste à envoyer: %i (res %i) envoyé %i\n",sizeMsg-sent, res, sent);
        res = send(sock, msg+sent, sizeMsg-sent, 0);
        sent += res;
        if (res == -1) {
            printf("Problème lors de l'envoi du message\n");
            printf("errno: %d , %s\n", errno, strerror(errno));
            return -1;
        }
    }
    return 1;
}

int recvTCP(int sock, void* msg, int sizeMsg) {
    int res;
    int received=0;
    //boucle de réception
    while(received < sizeMsg) {
        res = recv(sock, msg+received, sizeMsg-received, 0);
        received += res;
        if (res == -1) {
            printf("Problème lors de la réception du message\n");
            printf("errno: %d , %s\n", errno, strerror(errno));
            return -1;
        } else if (res == 0) {
            return 0;
        }
    }
    return 1;
}