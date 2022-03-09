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

#define ERROR -1

/* Fonction qui utilise le protocole défini. */
int sendMessage(int ds, const char *message, const struct sockaddr_in sockServ) {
    const struct sockaddr *serv = (const struct sockaddr *)&sockServ;
    socklen_t addrLen = sizeof(struct sockaddr_in);

    // 1 - Envoie du nombre d'octets du message à envoyer.
    char size[100];
    sprintf(size, "%zu", strlen(message)); 

    // 2 - Envoie au serveur de ce nombre d'octets ainsi que du message.
    if (sendto(ds, size, strlen(size) + 1, 0, serv, addrLen) == ERROR || sendto(ds, message, strlen(message) + 1, 0, serv, addrLen) == ERROR) {
        return ERROR;
    }
    return 0;
}

/* Partie 4 */
int sendIntArray(int ds, const struct sockaddr_in sockServ) {
    const struct sockaddr *serv = (const struct sockaddr *)&sockServ;
    socklen_t addrLen = sizeof(struct sockaddr_in);

    // 1 - Construction du tableau d'entiers
    int array[10];
    for (int i = 0; i < 10; ++i) {
        array[i] = i;
    }

    // 2 - Envoie au serveur de ce nombre d'octets ainsi que du message.
    if (sendto(ds, "10", 10, 0, serv, addrLen) == ERROR || sendto(ds, array, 10, 0, serv, addrLen) == ERROR) {
        return ERROR;
    }
    return 0;
}

/* Programme client */

int main(int argc, char *argv[]) {
    /* je passe en paramètre l'adresse de la socket du serveur (IP et
       numéro de port) et un numéro de port à donner à la socket créée plus loin.*/

    /* Je teste le passage de parametres. Le nombre et la nature des
       paramètres sont à adapter en fonction des besoins. Sans ces
       paramètres, l'exécution doit être arrétée, autrement, elle
       aboutira à des erreurs.*/
    if (argc < 3 || argc > 4) {
        printf("Utilisation : %s ip_serveur port_serveur [port_client]\n", argv[0]);
        exit(1);
    }

    /* Etape 1 : créer une socket */   
    int ds = socket(PF_INET, SOCK_DGRAM, 0);

    /* /!\ : Il est indispensable de tester les valeurs de retour de
       toutes les fonctions et agir en fonction des valeurs
       possibles. Voici un exemple */
    if (ds == ERROR) {
        perror("[CLIENT] Erreur lors de la création de la socket ");
        exit(1); // je choisis ici d'arrêter le programme car le reste
                 // dépendent de la réussite de la création de la socket.
    }
   
    /* J'ajoute des traces pour comprendre l'exécution et savoir
       localiser des éventuelles erreurs */
    printf("[CLIENT] Création de la socket réussie.\n");
   
    // Je peux tester l'exécution de cette étape avant de passer à la
    // suite. Faire de même pour la suite : n'attendez pas de tout faire
    // avant de tester.
   
    /* Etape 2 : Nommer la socket du client */
    struct sockaddr_in ad;
    socklen_t len = sizeof(ad);
    ad.sin_family = AF_INET;            // IPv4
    ad.sin_addr.s_addr = INADDR_ANY;

    // Nommage automatique
    if (argc == 3) {
        ad.sin_port = htons((short)0);
    }
    // Nommage manuel
    else {
        ad.sin_port = htons(atoi(argv[3]));
    }

    int res = bind(ds, (struct sockaddr *)&ad, sizeof(ad));
    if (res == ERROR) {
        perror("[CLIENT] Erreur lors du nommage de la socket ");
        exit(2);
    }

    // Récupération de l'adresse et du numéro de port
    if (getsockname(ds, (struct sockaddr *)&ad, &len) == ERROR) {
        perror("[CLIENT] Erreur lors du nommage automatique de la socket ");
        exit(3);
    }
   
    /* Etape 3 : Désigner la socket du serveur */
    struct sockaddr_in sockServ;
    sockServ.sin_family = AF_INET;
    sockServ.sin_addr.s_addr = inet_addr(argv[1]);
    sockServ.sin_port = htons(atoi(argv[2]));
    
    /* Etape 4 : envoyer un message au serveur */
    char *messageUtilisateur;
    size_t inputSize;
    printf("[CLIENT] Entrez un message à envoyer au serveur : ");
    res = getline(&messageUtilisateur, &inputSize, stdin);
    if (res == ERROR) {
        perror("[CLIENT] Erreur lors de la récupération du message :");
        exit(3);
    }

    len = strlen(messageUtilisateur) - 1;
    // Supprime le \n à la fin de la ligne d'input utilisateur
    if (messageUtilisateur[len] == '\n') {
        messageUtilisateur[len] = '\0';
    }

    if (sendMessage(ds, messageUtilisateur, sockServ) == ERROR) {
        perror("[CLIENT] Erreur lors de l'envoie du message ");
        exit(4);
    }
   
    /* Etape 5 : recevoir un message du serveur (voir sujet pour plus de détails) */
    socklen_t servAdr = sizeof(sockServ);
    char bytesSent[100];
    ssize_t servRes = recvfrom(ds, bytesSent, 100, 0, (struct sockaddr*)&sockServ, &servAdr);

    if (servRes == ERROR) {
        perror("[CLIENT] Erreur lors de la réception du message du serveur ");
        exit(5);
    }
    printf("[CLIENT] %s", bytesSent);
   
    /* Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)*/
    shutdown(ds, SHUT_RDWR); free(messageUtilisateur);
   
    printf("[CLIENT] Sortie.\n");
    return 0;
}
