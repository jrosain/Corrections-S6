#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <string.h>
#include <errno.h>

void afficheErreur() {
    printf("errno: %d , %s\n", errno, strerror(errno));
}

int creerSocket() {
    int ds = socket(PF_INET, SOCK_STREAM, 0);
    if (ds == -1){
        perror("Serveur : pb creation socket :");
        afficheErreur();
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
        afficheErreur();
        exit(1);
    }
    return ad;
}

struct sockaddr_in designerSocket(char* port, char* ip) {
    struct sockaddr_in sock;
    sock.sin_family = AF_INET;
    int resConvertAddr = inet_pton(AF_INET, ip, &(sock.sin_addr));
    if(resConvertAddr == 1) {
        printf("Adresse IP correctement convertie\n");
    } else {
        printf("Problème à la conversion de l'adresse IP\n");
        afficheErreur();
        exit(1);
    }
    sock.sin_port = htons((short)atoi(port));
    return sock;
}

int connecterTCP(int ds, struct sockaddr_in * sock) {
    socklen_t lgAdr = sizeof(struct sockaddr_in);
    int resConnexion = connect(ds, (struct sockaddr *)sock, lgAdr);
    if (resConnexion == 0) {
        printf("Connexion réussie\n");
    } else {
        printf("Connexion impossible\n");
        afficheErreur();
        exit(-1);
    }
    return resConnexion;
}

int listenTCP(int ds, int nbMaxAttente) {
    int resListen = listen(ds, nbMaxAttente);
    if (resListen == -1) {
        printf("Problème lors de l'écoute\n");
        afficheErreur();
        exit(1);    
    }
    return resListen;
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
            afficheErreur();
            return -1;
        }
    }
    return sent;
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
            afficheErreur();
            return -1;
        } else if (res == 0) {
            return 0;
        }
    }
    return received;
}

int recv2TCP(int sock, void* msg, int sizeMsg) {
    int taille;
    recvTCP(sock, &taille, sizeof(int));
    if (taille > sizeMsg) {
        printf("problème, buffer trop petit!\n");
        return -1;
    }
    return recvTCP(sock, msg, taille);
}

int send2TCP(int sock, void* msg, int sizeMsg) {
    sendTCP(sock, &sizeMsg, sizeof(int));
    return sendTCP(sock, msg, sizeMsg);
}

FILE* openFileFTP(const char* filename, const char* mode) {
    FILE* stream = fopen(filename, mode);
    if (stream == NULL) {
        printf("Problème lors de l'ouverture du fichier %s.\n", filename);
        afficheErreur();
    }
    return stream;
}

size_t readFileFTP(void* buffer, size_t blocSize, size_t blocCount, FILE* stream) {
    size_t lu = fread(buffer, blocSize, blocCount, stream);
    if (blocCount != lu) {
        printf("Problème de lecture des blocs dans le fichier\n");
        afficheErreur();
    }
    return lu;
}

size_t writeFileFTP(void* buffer, size_t blocSize, size_t blocCount, FILE* stream) {
    size_t ecrit = fread(buffer, blocSize, blocCount, stream);
    if (blocCount != ecrit) {
        printf("Problème d'écriture des blocs dans le fichier\n");
        afficheErreur();
    }
    return ecrit;
}