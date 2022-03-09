/**
 * fichier: serveur.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
#include <netinet/in.h>
#include <stdio.h>
#include <sys/types.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#include "utils.h"

#define MAX_FILENAME_SIZE 8000
#define MAX_CLIENTS 10

/**
 * Protocole de réception d'un message :
 *  1 - Réception de la taille du message ;
 *  2 - Réception du message en lui-même.
 **/
int receiveTCP(int connectedSocket, char *message, size_t maxMessageSize) {
    size_t messageSize;
    ssize_t res = recv(connectedSocket, &messageSize, sizeof(messageSize), 0);

    if (res == ERROR || res == 0) {
        return res;
    }

    size_t totalReceived = 0;
    while (totalReceived < messageSize) {
        // On veut recevoir les messageSize - totalReceived octets du message.
        // Ainsi, on ajoute les octets reçus au pointeur message + totalReceived.
        ssize_t res = recv(connectedSocket, message + totalReceived, messageSize - totalReceived, 0);

        if (res == ERROR || res == 0) {
            return res;
        }

        totalReceived += res;
    }

    return totalReceived;
}

/**
 * Écriture du buffer dans un fichier.
 * Retourne ERROR s'il y a un soucis lors de l'écriture du fichier.
 * Sinon, retourne 0.
 **/
void writeFile(FILE *file, const char *buffer, size_t bufferSize) {
    size_t totalWritten = 0;

    while (totalWritten < bufferSize) {
        size_t written = fwrite(buffer + totalWritten, sizeof(char), bufferSize - totalWritten, file);
        totalWritten += written;
    }
}

/** 
 * Protocole de réception d'un fichier via la socket connectée.
 * Reçoit d'abord le nom du fichier, la taille, puis reçoit les données.
 * L'écrit dans un fichier du dossier de réception.
 **/
void receiveFile(int connectedSocket) {
    // Réception du nom du fichier :
    //  1 - Recevoir la taille du nom ; Pour simplifier le code, on suppose 
    //      que le nom d'un fichier fait moins de MAX_FILENAME_SIZE octets.
    //  2 - Recevoir le nom en lui-même.
    char fileName[MAX_FILENAME_SIZE];
    ssize_t res = receiveTCP(connectedSocket, fileName, MAX_FILENAME_SIZE);

    if (res == ERROR || res == 0) {
        perror("[SERVEUR] Erreur lors de la réception du nom du fichier ");
        return;
    }

    // Création du dossier de réception s'il n'existe pas encore.
    char *filePath = malloc(strlen(fileName) + 30);
    sprintf(filePath, "./reception/client-%i/", getpid());

    // Création du dossier s'il n'existe pas encore (on ne peut pas stat dessus).
    struct stat attributes;
    if (stat(filePath, &attributes) == ERROR && mkdir(filePath, 0700) == ERROR) {
        perror("[SERVEUR] Erreur lors de la création du dossier d'un client ");
        return;
    }

    // Concaténation du nom du fichier avec le dossier de réception.
    strcat(filePath, fileName);
    if (filePath == NULL) {
        printf("[SERVEUR] Erreur lors de la lecture du nom de fichier.\n");
        return;
    }

    // Ouverture du fichier
    FILE* file = fopen(filePath, "wb");
    printf("[SERVEUR] Écriture dans %s\n", filePath);
    if(file == NULL){
        perror("[SERVEUR] Erreur lors de l'ouverture du fichier ");
        return;
    }
    free(filePath);

    // Réception du fichier :
    //  1 - On reçoit la taille du fichier.
    size_t fileSize;
    res = recv(connectedSocket, &fileSize, sizeof(fileSize), 0);
    if (res == ERROR || res == 0) {
        fclose(file);
        return;
    }
    printf("[SERVEUR] Taille du fichier à recevoir : %zu octets\n", fileSize);

    //  2 - On reçoit le fichier en lui-même.
    // Il y a des chances pour que la taille du fichier soit supérieur à la 
    // taille maximale du buffer, il faudra donc boucler pour récupérer le
    // contenu total du fichier.
    size_t totalReceived = 0;
    while (totalReceived < fileSize) {
        char fileContent[MAX_BUFFER_SIZE];
        res = receiveTCP(connectedSocket, fileContent, MAX_BUFFER_SIZE);
        
        if (res == ERROR) {
            perror("[SERVEUR] Erreur lors de la réception du fichier ");
            break;
        }
        if (res == 0) {
            printf("[SERVEUR] Socket client fermée\n");
            break;
        }

        // Écriture dans le fichier.
        writeFile(file, fileContent, res);
        totalReceived += res;
    }

    // Fichier écrit, on le ferme.
    fclose(file);
}

int main(int argc, char *argv[]) {
    // Un serveur peut être configuré pour être lancé sur un port en particulier 
    // et accepter un nombre maximum de clients.
    // Si le port n'est pas donné, il se connectera automatiquement avec un port
    // libre. 
    // Le nombre maximum de clients par défaut est 10.
    // Pour changer le nombre de clients, il faut impérativement indiquer le port. 
    if (argc < 2 || argc > 3) {
        printf("[SERVEUR] Utilisation : %s [port] [nombre_clients_max]\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    
    // Création de la socket serveur qui va écouter les demandes de connexion.
    // Il ne faut pas oublier de la fermer dans les processus enfants créés par les fork.
    int serverSocket = createTCPSocket();

    // Récupération de la structure d'adresse.
    struct sockaddr_in serverSockAddr;
    // Si le port a été renseigné, on essaie de créer la structure avec celui-ci.
    if (argc >= 2) {
        serverSockAddr = createIPv4Address("", (short)atoi(argv[1]));
    }
    // Sinon, on crée la structure automatiquement.
    else {
        serverSockAddr = createIPv4Address("", 0);
    }

    // Liaison de la socket créée avec la structure d'adressage.
    bindSocket(serverSocket, &serverSockAddr);

    // Dans tous les cas, on affiche l'adresse du serveur, avec le port.
    printf("[SERVEUR] Le serveur s'exécute sur %s:%i.\n", 
        inet_ntoa(serverSockAddr.sin_addr), ntohs(serverSockAddr.sin_port));
    
    // Récupération du nombre maximal de clients à écouter.
    int maxClients = MAX_CLIENTS;
    if (argc == 3) {
        maxClients = atoi(argv[2]);
    }

    // Passage de la socket en mode écoute
    if (listen(serverSocket, maxClients) == ERROR) {
        perror("[SERVEUR] Erreur lors de la mise en écoute de la socket ");
        exit(EXIT_FAILURE);
    }
    
    // Accepte la connexion des clients et reçoit des fichiers.
    while (1) {
        struct sockaddr_in clientSockAddr;
        int clientSocket = acceptConnection(serverSocket, &clientSockAddr);

        int pid = fork();

        if (pid == 0) {
            close(serverSocket);
            printf("[SERVEUR] Le client connecté est %s:%i.\n", 
                inet_ntoa(clientSockAddr.sin_addr), ntohs(clientSockAddr.sin_port));

            // Réception du fichier envoyé par le client.
            receiveFile(clientSocket);

            printf("[SERVEUR] Fichier du client reçu. Fermeture de la connexion.\n");
            close(clientSocket);
            // Termine le fork quand le fichier est reçu.
            break;
        }
        close(clientSocket);
    }
        
    close(serverSocket);
    printf("[SERVEUR] Fin de service.\n");
}