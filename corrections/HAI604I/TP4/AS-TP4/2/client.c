#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include<arpa/inet.h>
#include<string.h>
#include "fonctionsTCP.c"

/* Programme client TCP */

int main(int argc, char *argv[]) {

    if (argc != 4){
        printf("utilisation : %s ip_serveur port_serveur port_client\n", argv[0]);
        exit(1);
    }

    /* Etape 1 : créer une socket */   
    int ds = socket(PF_INET, SOCK_STREAM, 0);
    if (ds == -1){
        perror("[Client] : pb creation socket :\n");
        exit(1);
    }
    printf("[Client] : creation de la socket réussie \n");
    /* etape 1.2 : nommage de la socket client */
    struct sockaddr_in sock_clt;
    socklen_t size =sizeof(struct sockaddr_in);
    sock_clt.sin_family = AF_INET;
    sock_clt.sin_addr.s_addr = INADDR_ANY;
    sock_clt.sin_port = htons((short)atoi(argv[3]));
    
    int res = bind(ds, (struct sockaddr*) &sock_clt, size);
    if (res == -1){
        perror("[Client] : pb nommage socket :\n");
        exit(1);
    }
    /* etape 2 : designer la socket du serveur */
    struct sockaddr_in sock_srv;
    sock_srv.sin_family = AF_INET;
    sock_srv.sin_addr.s_addr = inet_addr(argv[1]);
    sock_srv.sin_port = htons(atoi(argv[2]));

    /* etape 3 : demander une connexion */
    int dsConnect = connect(ds, (struct sockaddr*)&sock_srv, sizeof(sock_srv));
    if (dsConnect == -1){
        perror("[Client] : pb connexion serveur :\n");
        exit(1);
    }
    printf("[Client] : connexion réussie\n");
    int tailleMsg = 100000;
    char msg[100000];
    fgets(msg, 100000, stdin);

    int resTaille = sendTCP(ds, &tailleMsg, sizeof(int));
    if (resTaille == 0 || resTaille == -1){
        perror("[Client] : problème envoi taille message :");
        exit(1);
    }
    else
    {
        printf("Message bien envoyé...\n");
    }

    int resMsg = sendTCP(ds, msg, tailleMsg);
    if (resMsg == -1 || resMsg == 0){
        perror("[Client] : problème envoi message :");
        exit(1);
    }
    else
    {
        printf("Message bien envoyé...\n");
    }

    shutdown(ds, SHUT_RDWR);
    /* Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)*/

    printf("[CLIENT] Sortie.\n");
    return 0;
}
