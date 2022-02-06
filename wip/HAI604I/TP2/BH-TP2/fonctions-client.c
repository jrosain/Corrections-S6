#include <netinet/in.h>
#include <stdio.h> 
#include <arpa/inet.h>
#include <string.h>
#include <sys/socket.h>

/**
 * Connexion au serveur.
 * Cette fonction écrase la valeur de `socket_serveur` pour lui donner la valeur de
 * l'adresse de la socket serveur. Le port et l'adresse sont donnés par l'utilisateur.
 *
 * @param struct sockaddr_in*   OUT     socket_serveur
 * @param char*                 IN      adresse
 * @param int                   IN      port
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int serveur_connection(struct sockaddr_in* socket_serveur, char* adresse, int port) {
    socket_serveur->sin_family = AF_INET;
    socket_serveur->sin_addr.s_addr = inet_addr(adresse);
    socket_serveur->sin_port = htons((short) port);

    return 1;
}

/**
 * Essaie de se connecter à un serveur sur écoute.
 * 
 * @param int*                  IN  ds
 * @param struct sockaddr_in*   IN  socket_serveur
 *
 * @return 0 si une erreur survient, 1 sinon
 */
int connect_to_server(int* ds, struct sockaddr_in* socket_serveur) {
    return connect(*ds, (struct sockaddr*) socket_serveur, sizeof(struct sockaddr_in)) != -1;
}

/**
 * Envoie d'un message au serveur.
 * Cette fonction envoie au serveur le message écris par l'utilisateur sur
 * la sortie standard, le résultat de ce message est contenu dans `message`.
 *
 * @param int*                  IN  ds
 * @param char*                 OUT message
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int send_message(int* ds, char* message) {
    printf("Client : envoyer un message au serveur (100 caractères max): ");
    fgets(message, 100, stdin);

    return send(*ds, message, strlen(message) + 1, 0) != -1;
}

/**
 * Attente du message serveur.
 * Cette fonction attend que le serveur réponde au message. La valeur du message sera mise
 * dans la variable `octets` et représente un entier.
 *
 * @param int*                  IN  ds
 * @param int*                  OUT octets
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int wait_message(int* ds, int* octets) {
    printf("Client : attente du message du serveur...\n");

    return recv(*ds, octets, sizeof(int), 0) != -1;
}