/**
 * fichier: client.c
 * auteur: Johann Rosain
 * date: 09/03/2022
 **/
#include <netinet/in.h>
#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <string.h>
#include <sys/stat.h>

#include "utils.h"

/**
 * Protocole de réception d'un message :
 *  1 - Envoie de la taille du message ;
 *  2 - Envoie du message en lui-même.
 **/
int sendTCP(int connectedSocket, char *message, size_t messageSize) {
    ssize_t res = send(connectedSocket, &messageSize, sizeof(messageSize), 0);

    if (res == ERROR || res == 0) {
        return res;
    }

    size_t totalSent = 0;

    while (totalSent < messageSize) {
        // On veut recevoir les messageSize - totalReceived octets du message.
        // Ainsi, on ajoute les octets reçus au pointeur message + totalReceived.
        ssize_t res = send(connectedSocket, message + totalSent, messageSize - totalSent, 0);

        if (res == ERROR || res == 0) {
            return res;
        }

        totalSent += res;
    }

    return totalSent;
}

/**
 * Lit un fichier sur le nombre d'octets demandés.
 * Termine le programme avec un code d'erreur si le fichier n'a pas pu être correctement lu.
 * Retourne 0 s'il n'y a plus rien à lire dans le fichier, sinon, retourne le nombre d'octets lus.
 */
size_t readFile(FILE *file, char *buffer, size_t readSize) {
    size_t read = fread(buffer, sizeof(char), readSize, file);
    if (read == 0) {
        if (ferror(file) != 0){
            perror("[CLIENT] Erreur lors de la lecture du fichier ");
            fclose(file);
            exit(EXIT_FAILURE);
        } 
        else {
            printf("[CLIENT] Fichier totalement lu.\n");
            return 0;
        }
    }
    return read;
}

int main(int argc, char *argv[]) {
    // Un client se connecte automatiquement a un port.
    // Il se connecte à un serveur et lui envoie le fichier désigné par nom_fichier.
    if (argc != 4) {
        printf("[CLIENT] Utilisation : %s ip_serveur port_serveur nom_fichier\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Création de la socket client qui va se connecter avec le serveur.
    int clientSocket = createTCPSocket();
    
    // Connexion avec la socket du serveur, désignée par l'ip et le port donné en paramètre du programme.
    struct sockaddr_in serverAddress = createIPv4Address(argv[1], (short)atoi(argv[2]));
    connectTo(clientSocket, &serverAddress);

    printf("[CLIENT] Connecté au serveur %s:%i.\n", 
        inet_ntoa(serverAddress.sin_addr), ntohs(serverAddress.sin_port));
    
    // Envoie du fichier désigné par nom_fichier

    // 1 - Envoie du nom du fichier
    sendTCP(clientSocket, argv[3], strlen(argv[3]) + 1);

    // 2 - Envoie du contenu du fichier
    //  a) Construction du chemin du fichier
    char *filepath = malloc(strlen(argv[3]) + 12); // ./emission/+nom fichier +\0
    filepath[0] = '\0';
    strcat(filepath, "./emission/");
    strcat(filepath, argv[3]);

    //  b) Lecture du fichier & envoie du contenu.
    printf("[CLIENT] Envoie du fichier %s\n", filepath);

    // Récupération de la taille du fichier à envoyer.
    struct stat attributes;
    if (stat(filepath, &attributes) == ERROR) {
        perror("[CLIENT] Erreur lors de la lecture de la taille du fichier ");
        free(filepath);
        exit(EXIT_FAILURE);
    }
    size_t fileSize = attributes.st_size;
    printf("[CLIENT] Taille du fichier (en octets) : %zu\n", fileSize);

    // Envoie de la taille du fichier
    ssize_t res = send(clientSocket, &fileSize, sizeof(fileSize), 0);
    if (res == ERROR) {
        perror("[CLIENT] Erreur lors de l'envoie de la taille du fichier ");
        exit(EXIT_FAILURE); 
    }
    if (res == 0) {
        printf("[CLIENT] Erreur lors de l'envoie du fichier : la socket est fermée.\n");
        exit(EXIT_FAILURE);
    }

    // Lecture du contenu du fichier
    FILE* file = fopen(filepath, "rb");
    if (file == NULL){
        perror("[CLIENT] Erreur lors de l'ouverture du fichier ");
        free(filepath);
        exit(EXIT_FAILURE);
    }
    free(filepath);

    // On lit le fichier par bloc de MAX_BUFFER_SIZE et on l'envoie au serveur.
    size_t totalRead = 0;
    while (totalRead < fileSize) {
        // Lecture du fichier
        char buffer[MAX_BUFFER_SIZE];
        size_t read = readFile(file, buffer, MAX_BUFFER_SIZE);
        if (read == 0) {
            break;
        }
        totalRead += read;

        // Envoie au serveur distant
        res = sendTCP(clientSocket, buffer, read);

        if (res == ERROR) {
            perror("[CLIENT] Erreur lors de l'envoie du fichier ");
            break;
        }
        if (res == 0) {
            printf("[CLIENT] Socket serveur fermée.\n");
            break;
        }

        // Si tout s'est bien passé, on affiche le nombre d'octets actuellement envoyés au serveur.
        printf("[CLIENT] %zu/%zu octets envoyés\n", totalRead, fileSize);
    }

    // Fermeture du fichier et de la socket
    fclose(file); close(clientSocket);
    
    printf("[CLIENT] Fin de service.\n");
}
