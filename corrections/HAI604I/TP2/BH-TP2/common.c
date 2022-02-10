#include <unistd.h>
#include <netdb.h>

/**
 * Création de la socket.
 * Cette fonction écrase la valeur de `ds` pour lui donner la valeur du
 * descripteur de fichier de la socket créée
 *
 * @param int* OUT ds
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int socket_creation(int* ds) {
    *ds = socket(PF_INET, SOCK_STREAM, 0);
    return *ds != -1;
}

/**
 * Nommage de la socket.
 * Cette fonction écrase la valeur de `socket` pour lui donner la valeur de
 * l'adresse de la socket nommée. Le port est donné par l'utilisateur.
 *
 * @param int*                  IN/OUT  ds
 * @param struct sockaddr_in*   OUT     socket
 * @param int                   IN      port
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int socket_named(int* ds, struct sockaddr_in* socket, int port) {
    socket->sin_family = AF_INET;
    socket->sin_addr.s_addr = INADDR_ANY;
    socket->sin_port = htons((short) port);
    int res = bind(*ds, (struct sockaddr*) socket, sizeof(struct sockaddr_in));

    socklen_t size = sizeof(struct sockaddr_in);
    getsockname(*ds, (struct sockaddr*) socket, &size);
    
    return res != -1;
}

/**
 * Fermeture de la socket.
 *
 * @param int* IN/OUT ds
 *
 * @return 0 si une erreur survient, 1 sinon
**/
int close_socket(int* ds) {
    return close(*ds) != -1;
}