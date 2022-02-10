#include <netinet/in.h>
#include <stdio.h> 

/**
 * Met la socket sur écoute pour attendre la connection de client
 * 
 * @param int*      IN/OUT  ds
 * @param int       IN      nombre max de client en file d'attente
 *
 * @return 0 si une erreur survient, 1 sinon
 */
int socket_listen(int* ds, int nb) {
    return listen(*ds, nb) != -1;
}

/**
 * Bloque sur l'attente de la connection d'un client.
 * Lorsqu'un client se connecte, `socket_client` contient l'adresse du client
 * `ds_client` est quant à elle changée pour contenir le descripteur de
 * fichier de la socket connectée avec ce client
 * 
 * @param int*                  IN/OUT  ds
 * @param struct sockaddr_in*   OUT     socket_client
 * @param int*                  OUT     ds_client
 *
 * @return 0 si une erreur survient, 1 sinon
 */
int wait_client(int* ds, struct sockaddr_in* socket_client, int* ds_client) {
    printf("Serveur : attente d'un client...\n");

    socklen_t size = sizeof(struct sockaddr_in);
    *ds_client = accept(*ds, (struct sockaddr*) socket_client, &size);

    return *ds_client != -1;
}

/**
 * Attente du message client.
 * 
 * Le message envoyé par le client ainsi que sa taille sont reporté dans les
 * variables/paramètres `octets` et `message`.
 *
 * @param int*                  IN  ds_client
 * @param int*                  OUT octets
 * @param char*                 OUT message
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int wait_message(int* ds_client, int* octets, char* message) {
    printf("Serveur : attente du message d'un client...\n");

    *octets = recv(*ds_client, message, sizeof(message), 0);

    return *octets != -1;
}

/**
 * Envoie d'un message au client.
 * Cette fonction envoie au client qui a envoyé un message la taille du message
 * reçu. C'est donc un int qui est envoyé.
 *
 * @param int*                  IN/OUT  ds_client
 * @param int*                  IN/OUT  octets
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int send_message(int* ds_client, int* octets) {
    return send(*ds_client, octets, sizeof(int), 0) != -1;
}