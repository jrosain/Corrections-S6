#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "utils.h"

int createTCPSocket() {
    int sock = socket(PF_INET, SOCK_STREAM, 0);

    if (sock == ERROR) {
        perror("[UTILS] Erreur lors de la création de la socket ");
        exit(EXIT_FAILURE);
    }

    return sock;
}

struct sockaddr_in createIPv4Address(const char *address, short port) {
    if (port != 0 && port < 1024) {
        printf("[UTILS] Erreur : le port fourni est inférieur à 1024 et est un port réservé au système.\n");
        exit(EXIT_FAILURE);
    }

    struct sockaddr_in ad;
    ad.sin_family = AF_INET;

    if (strlen(address) == 0) {
        ad.sin_addr.s_addr = INADDR_ANY;
    }
    else {
        ad.sin_addr.s_addr = inet_addr(address);
    }

    ad.sin_port = htons(port);

    return ad;
}

void bindSocket(int socketDescriptor, struct sockaddr_in *ipv4Address) {
    struct sockaddr *addr = (struct sockaddr *)ipv4Address;
    socklen_t addrLen = sizeof(struct sockaddr_in);
    // Liaison de la socket avec l'adresse.
    if (bind(socketDescriptor, addr, addrLen) == ERROR) {
        perror("[UTILS] Erreur lors de la liaison de la socket ");
        exit(EXIT_FAILURE);
    }

    // Nommage de l'adresse IPv4
    if (getsockname(socketDescriptor, addr, &addrLen) == ERROR) {
        perror("[UTILS] Erreur lors du nommage de l'adresse ");
        exit(EXIT_FAILURE);
    }
}

int acceptConnection(int serverSocket, struct sockaddr_in *ipv4Address) {
    socklen_t clientSockLen = sizeof(*ipv4Address);
    int clientSocket = accept(serverSocket, (struct sockaddr *)ipv4Address, &clientSockLen);

    if (clientSocket == ERROR) {
        perror("[UTILS] Erreur lors de l'acceptation de la connexion d'un client ");
        exit(EXIT_FAILURE);
    }

    return clientSocket;
}

void connectTo(int socketDescriptor, const struct sockaddr_in *serverAddress) {
    if (connect(socketDescriptor, (const struct sockaddr*)serverAddress, sizeof(*serverAddress)) == ERROR) {
        perror("[CLIENT] Erreur lors de la connexion au serveur ");
        exit(EXIT_FAILURE);
    }
}