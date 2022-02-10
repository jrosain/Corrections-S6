#include <stdlib.h>

#include "common.c"
#include "fonctions-client.c"

/* Programme client */

int main(int argc, char *argv[]) {
    /* je passe en paramètre l'adresse de la socket du serveur (IP et
        numéro de port) et un numéro de port à donner à la socket créée plus loin.*/
    if (argc != 4) {
        printf("utilisation : %s ip_serveur port_serveur port_client\n", argv[0]);
        exit(1);
    }

    int success;                        // Variable pour savoir si la dernière fonction a réussi sans erreur
    int ds;                             // Contient le descripteur de fichier de la socket client
    struct sockaddr_in socket_client;   // Adresse de la socket client 
    struct sockaddr_in socket_serveur;  // Adresse du serveur sur lequel le clients  econnecte et envoie un message
    char message[100];                  // Message envoyé par le client (ATTENTION, si le client envoie + de 100 octets, le comportement n'est pas géré)
    int octets;                         // Nombre d'octets du message envoyé par le client, valeur renvoyé par le serveur

    // Etape 1 : création de la socket
    success = socket_creation(&ds);
    if (!success)
        perror("Client : problème lors de la création de la socket");
    printf("Client : création de la socket réussi !\n");

    // Etape 2 : nommage de la socket
    success = socket_named(&ds, &socket_client, atoi(argv[3]));
    if (!success)
        perror("Client : problème lors du nommage de la socket");
    printf("Client : socket client nommée avec succès ! (%s:%i)\n", inet_ntoa(socket_client.sin_addr), ntohs((short) socket_client.sin_port));

    // Etape 3 : désignation de la socket serveur
    success = serveur_connection(&socket_serveur, argv[1], atoi(argv[2]));
    printf("Client : connexion avec le serveur (%s:%i)\n", inet_ntoa(socket_serveur.sin_addr), ntohs((short) socket_serveur.sin_port));

    // Etape 4 : envoie du message au serveur
    success = send_message(&ds, &socket_serveur, message);
    if (!success)
        perror("Client : problème lors de l'envoi du message");
    printf("\nClient : message envoyé au serveur : %s\n", message);

    // Etape 5 : réception du nombre d'octet envoyé
    success = wait_message(&ds, &socket_serveur, &octets);
    if (!success)
        perror("Client : problème lors de la réception du message serveur");
    printf("Client : message reçu du serveur : %i\n", octets);

    // Etape 6 : fermeture de la socket
    success = close_socket(&ds);
    if (!success)
        perror("Client : problème lors de la fermeture de la socket");
    printf("Client : socket fermée !\n");
    printf("Client : j'ai fini !\n");
    
    return 0;
}