#include <netinet/in.h>
#include <stdio.h> 

/**
 * Attente du message client.
 * Cette fonction écrase la valeur de `socket_client` pour lui donner la
 * valeur de l'adresse du client qui envoie un message au serveur.
 * 
 * Le message envoyé par le client ainsi que sa taille sont reporté dans les
 * variables/paramètres `octets` et `message`.
 *
 * @param int*                  IN/OUT  ds
 * @param struct sockaddr_in*   OUT     socket_client
 * @param int*                  OUT     octets
 * @param char*                 OUT     message
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int wait_message(int* ds, struct sockaddr_in* socket_client, int* octets, char* message) {
    printf("Serveur : attente du message d'un client...\n");

    socklen_t size = sizeof(struct sockaddr_in);
    *octets = recvfrom(*ds, message, sizeof(message), 0, (struct sockaddr*) socket_client, &size);

    return *octets != -1;
}

/**
 * Envoie d'un message au client.
 * Cette fonction envoie au client qui a envoyé un message la taille du message
 * reçu. C'est donc un int qui est envoyé.
 * 
 * Le message envoyé par le client ainsi que sa taille sont reporté dans les
 * variables/paramètres `octets` et `message`.
 *
 * @param int*                  IN/OUT  ds
 * @param struct sockaddr_in*   IN/OUT  socket_client
 * @param int*                  IN/OUT  octets
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int send_message(int* ds, struct sockaddr_in* socket_client, int* octets) {
    return sendto(*ds, octets, sizeof(int), 0, (struct sockaddr*) socket_client, sizeof(struct sockaddr_in)) != -1;
}