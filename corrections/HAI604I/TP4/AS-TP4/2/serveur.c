#include <netinet/in.h>
#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include<arpa/inet.h>
#include<string.h>
#include "fonctionsTCP.c"
#include <pthread.h>

/* Programme serveur TCP */

struct paramsFonctionThread {
    int idConnexion;
    short sockCltPort;
    struct in_addr sockCltAdr;
};

void * routine (void * params) {
    struct paramsFonctionThread * arg = (struct paramsFonctionThread *) params;
    pthread_t moi = pthread_self();
    printf("Thread : %lu, process %d\n",moi,getpid());
    printf("[SERVEUR] Le client connecté est %s:%i.\n", inet_ntoa(arg->sockCltAdr), ntohs(arg->sockCltPort));    
    int tailleTCP =0;
    int resTailleTCP = recvTCP(arg->idConnexion,&tailleTCP,sizeof(int));
    if (resTailleTCP == -1 || resTailleTCP == 0){
        perror("[Serveur] : pb réception taille msg ou client fermé:\n");
        
    }
    else
    {
        char msgTCP[tailleTCP];
        int resMsgTCP = recvTCP(arg->idConnexion,msgTCP,tailleTCP);
        if (resMsgTCP == -1 || resMsgTCP == 0){
            perror("[Serveur] : pb réception msg ou client fermé :\n");
            pthread_exit(NULL);
        }
        else
        {
            printf("[Serveur] : nombre d'octet : %i, message reçu : %s\n", resTailleTCP, msgTCP);
        }
    }
    close(arg->idConnexion);
    pthread_exit(NULL);
}

int main(int argc, char *argv[]) {
    /* etape 0 : gestion des paramètres si vous souhaitez en passer */
    if (argc != 2) {
        printf("Utilisation : [port_serveur]\n");
        exit(1);
    }
    struct sockaddr_in socket_srv;
    socklen_t size =sizeof(struct sockaddr_in);
    /* etape 1 : creer une socket d'écoute des demandes de connexions*/
    int srv = socket(PF_INET, SOCK_STREAM, 0);
    if (srv == -1) {
        perror("Serveur : problème lors de la création de la socket");
        exit(1);
    }
    printf("Serveur : création de la socket réussi !\n");
    /* etape 2 : nommage de la socket */
    socket_srv.sin_family = AF_INET;
    socket_srv.sin_addr.s_addr = INADDR_ANY;
    socket_srv.sin_port = htons((short)atoi(argv[1]));
    int res = bind(srv, (struct sockaddr *)&socket_srv, sizeof(socket_srv));

    if (res == -1) {
        perror("Serveur : problème lors du nommage de la socket");
        exit(1);
    }

    /* etape 3 : mise en ecoute des demandes de connexions */
    int srvListen = listen(srv, 10);
    if (srvListen == -1) {
        perror("Serveur : problème lors de la mise en écoute de la socket");
        exit(1);
    }
    printf("Serveur : socket serveur sur écoute.\n");

printf("###################  PARTIE SERVEUR ITERATIF ######################\n");
pthread_t threads[3];
int i=0;
while (1) {
    struct sockaddr_in sock_cltTCP;
    int newConnectionTCP = accept(srv, (struct sockaddr*)&sock_cltTCP, &size);
    
    if (newConnectionTCP == -1) {
        perror("[Serveur] : problème lors de la connection d'un client");
    }
    i++;
    struct paramsFonctionThread *args = malloc(sizeof(struct paramsFonctionThread));
    args->idConnexion = newConnectionTCP;
    args->sockCltAdr = sock_cltTCP.sin_addr;
    args->sockCltPort = sock_cltTCP.sin_port;

    if (pthread_create(&threads[i], NULL, routine, args) != 0){
      perror("erreur creation thread");
      exit(1);
    }
    
  }
    close(srv);
    printf("[SERVEUR] Sortie.\n");
    return 0;
}
