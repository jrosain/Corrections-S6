#include <stdlib.h>

#include "common.c"
#include "fonctions-client.c"
#include "fonctions-tests.c"

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

    // Etape 1 : création de la socket
    success = socket_creation(&ds);
    if (!success) {
        perror("Client : problème lors de la création de la socket");
        exit(1);
    }
    printf("Client : création de la socket réussi !\n");
    
    // Etape 2 : nommage de la socket
    success = socket_named(&ds, &socket_client, atoi(argv[3]));
    if (!success) {
        perror("Client : problème lors du nommage de la socket");
        exit(1);
    }
    printf("Client : socket client nommée avec succès ! (%s:%i)\n", inet_ntoa(socket_client.sin_addr), ntohs((short) socket_client.sin_port));

    // Etape 3 : désignation de la socket serveur
    success = serveur_connection(&socket_serveur, argv[1], atoi(argv[2]));
    printf("Client : désignation de la socket le serveur (%s:%i)\n", inet_ntoa(socket_serveur.sin_addr), ntohs((short) socket_serveur.sin_port));

    // Etape 4 : connection au serveur
    success = connect_to_server(&ds, &socket_serveur);
    if (!success) {
        perror("Client : problème lors de connection avec le serveur");
        exit(1);
    }
    printf("Client : connection réussie\n");

    // Exos
    //exo1(&ds)
    //exo2_1_client(&ds);
    //exo2_2_client(&ds);
    //exo2_3_client(&ds);
    //exo2_4_client(&ds);
    exo3_client(&ds);

    // Etape 7 : fermeture de la socket
    success = close_socket(&ds);
    if (!success) {
        perror("Client : problème lors de la fermeture de la socket");
        exit(1);
    }
    printf("Client : socket fermée !\n");
    printf("Client : j'ai fini !\n");
    
    return 0;
}

void exo1(int* ds) {
    char message[100];                  // Message envoyé par le client (ATTENTION, si le client envoie + de 100 octets, le comportement n'est pas géré)
    int octets;                         // Nombre d'octets du message envoyé par le client, valeur renvoyé par le serveur

    // Etape 5 : envoie du message au serveur
    int success = send_message(ds, message);
    if (!success) {
        perror("Client : problème lors de l'envoi du message");
        exit(1);
    }
    printf("\nClient : message envoyé au serveur : %s\n", message);

    // Etape 6 : réception du nombre d'octet envoyé
    success = wait_message(ds, &octets);
    if (!success) {
        perror("Client : problème lors de la réception du message serveur");
        exit(1);
    }
    printf("Client : message reçu du serveur : %i\n", octets);
}
