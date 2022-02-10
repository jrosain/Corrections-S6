#include <stdlib.h>
#include <arpa/inet.h>

#include "common.c"
#include "fonctions-serveur.c"

/* Programme serveur */

int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("utilisation : %s port_serveur\n", argv[0]);
        exit(1);
    }

    int success;                        // Variable pour savoir si la dernière fonction a réussi sans erreur
    int ds;                             // Contient le descripteur de fichier de la socket serveur
    struct sockaddr_in socket_serveur;  // Adresse de la socket serveur
    struct sockaddr_in socket_client;   // Adresse du client qui envoie un message
    int octets;                         // Nombre d'octets du message envoyé par le client
    char message[100];                  // Message envoyé par le client (ATTENTION, si le client envoie + de 100 octets, le comportement n'est pas géré)

    // Etape 1 : création de la socket
    success = socket_creation(&ds);
    if (!success)
        perror("Serveur : problème lors de la création de la socket");
    printf("Serveur : création de la socket réussi !\n");

    // Etape 2 : nommage de la socket
    success = socket_named(&ds, &socket_serveur, atoi(argv[1]));
    if (!success)
        perror("Serveur : problème lors du nommage de la socket");
    printf("Serveur : socket serveur nommée avec succès ! (%s:%i)\n", inet_ntoa(socket_serveur.sin_addr), ntohs((short) socket_serveur.sin_port));

    // Etape 3 : attente d'un message du client
    success = wait_message(&ds, &socket_client, &octets, message);
    if (!success)
        perror("Serveur : problème lors de la réception du message");
    printf("Serveur : message arrivé du client (%s:%i)\n", inet_ntoa(socket_client.sin_addr), ntohs((short) socket_client.sin_port));
    printf("\t%s\n", message);
    printf("Serveur : ce message fait %i octets\n", octets);

    // Etape 4 : envoie du nombre d'octet reçu au client
    success = send_message(&ds, &socket_client, &octets);
    if (!success)
        perror("Serveur : problème lors de l'envoi du message au client");
    printf("Serveur : message envoyé avec succès !\n");

    // Etape 5 : fermeture de la socket
    success = close_socket(&ds);
    if (!success)
        perror("Serveur : problème lors de la fermeture de la socket");
    printf("Serveur : socket fermée !\n");
    printf("Serveur : j'ai fini !\n");
    
    return 0;
}
