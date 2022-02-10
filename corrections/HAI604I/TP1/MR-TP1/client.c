#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include<arpa/inet.h>
#include<string.h>

#define ERROR -1

/* Programme client */

int main(int argc, char *argv[]) {

 /* 
  * Je passe en paramètre l'adresse de la socket du serveur (IP et numéro de port) 
    et un numéro de port à donner à la socket créée plus loin.

  * Je teste le passage de parametres. 
  * Le nombre et la nature des paramètres sont à adapter en fonction des besoins. 
  * Sans ces paramètres, l'exécution doit être arrétée, autrement, elle aboutira à des erreurs.
  */
  if (argc != 4){
    printf("Utilisation : %s ip_serveur port_serveur port_client\n", argv[0]);
    exit(1);
  }

  /* 
  Affichage de la saisie
  */
  char* adresseIPServ = argv[1];
  printf("IP du serveur : %s \n", adresseIPServ);

  int numPortServ = atoi(argv[2]);
  printf("Port du serveur : %i \n", numPortServ);

  int numPortClient = atoi(argv[3]);
  printf("Port du client : %i \n", numPortClient);
  

 /* 
  * Etape 1 : créer une socket  
  * ds :  descripteur de socket ou file descriptor qui contient en parametre:
     * PF_INET : se connecter a des adresses ip de type ipV4
     * SOCK_DGRAM : en utilisant le protocole UDP (non connecté)
     * 0 : protocole désiré (ici 0 car inutile de préciser avec le modele TCP/IP )
  * Il permet d'acceder en memoire a des buffers 
  */  
  int ds = socket(PF_INET, SOCK_DGRAM, 0);

 /* 
  * /!\ Il est indispensable de tester les valeurs de retour de toutes les fonctions et agir en fonction des valeurs possibles. /!\ 
  * Voici un exemple 
  */
  if (ds == -1){
   perror("Client : pb creation socket :");
   exit(1);
  }
  
  printf("ds = %i \n",ds);

  /* 
  J'ajoute des traces pour comprendre l'exécution et savoir localiser des éventuelles erreurs 
  */
  printf("Client : creation de la socket réussie \n");
 
  
 /* 
  * Etape 2 : Nommer/lier la socket du client 
  * On a besoin de 3 infos :
     * 1. le descripteur de la socket (ds)
     * 2. une structure de données qui va contenir la paire adresseIP/port
     * 3. la taille de la structure de données
  * Sortie : un entier qui sera l'id de la socket (son nom)
  * On se sert de la structure sockaddr_in (car ipV4) pour nommer/lier notre socketClient avec le ds
  */
  struct sockaddr_in sockClient;
 /* 
  * 3 variables :
     * sin_family : indique la famille d'adresseIp (toujours AF_INET pour nous car on utilise les ipV4)
     * sin_addr : structure de l'adresseIp (INADDR_ANY indique que la socket est associée à toutes les adresseIp de la machine)
     * sin_port : le port du Client 
  * Pourquoi ne pas mettre l'adresseIp du Client à la place de "INADDR_ANY"??
  */
  sockClient.sin_family = AF_INET;
  sockClient.sin_addr.s_addr = INADDR_ANY;
  sockClient.sin_port = htons((short) numPortClient); // argv[3] numPortClient

  /* 
  On effectue la lisaison descripteur de la socket et le couple (adresseIP et Port) en indiquant la taille du couple
  */
  int nomSock = bind(ds, (struct sockaddr*)&sockClient, sizeof(sockClient));

  if (nomSock == -1){
   perror("Client : pb creation liaison :");
   exit(1);
  }

  printf("Nom de la Socket = %i \n",nomSock);

  /* 
  * Etape 3 : Désigner la socket du serveur 
  * Creation de la structure : variable sockServ (cette variable est un objet) 
  */
   struct sockaddr_in sockServ;
   sockServ.sin_family = AF_INET ;
   sockServ.sin_addr.s_addr = inet_addr(argv[1]); // argv[1] adresseIp du Serveur
   sockServ.sin_port = htons((short) numPortServ);     // argv[2] numPortServ

   printf("Serveur : designation de la socket du serveur réussie : \n");

  
 /* 
  * Etape 4 : envoyer un message au serveur (voir sujet pour plus de détails)
  * Important : on a cree la socket en indiquant SOCK_DGRAM,donc on utilise le protocole UDP 
  * Pour UDP, on utilise la fonction sendto pour envoyer des messages 
  * et la fonction recvfrom pour recevoir des messages 
  */
   char msgClientToServ[100];

   printf("Saisir le message a envoyer (max 100 char) :");
   fgets(msgClientToServ, 100, stdin);

  /* 
   * ici, on supprime le retour charriot
   */

   int len = strlen(msgClientToServ) - 1;

   // Supprime le \n à la fin de la ligne d'input utilisateur
   if (msgClientToServ[len] == '\n') {
        msgClientToServ[len] = '\0';
   }
   
   // Pourquoi taille + 1?
   int retourSendto = sendto(ds,msgClientToServ,strlen(msgClientToServ)+1,0,( struct sockaddr*)&sockServ, sizeof(sockServ));

   if (retourSendto == -1) {
      // traitement de l'erreur
      perror("L'envoi du message est en erreur \n");
   }
  
  /* 
   * Etape 5 : recevoir un message du serveur (voir sujet pour plus de détails)
   */

  char msgServToClient[100] ; 
  socklen_t lgAdr = sizeof(sockServ);

  int retourReceive = recvfrom(ds,msgServToClient,sizeof(msgServToClient),0, (struct sockaddr*)&sockServ, &lgAdr );

  if (retourReceive == -1) {
     // traitement de l'erreur
     printf("La reception du message est en erreur \n");
  }

  printf("Le message reçu par le client du serveur: (%s:%i) ",inet_ntoa(sockServ.sin_addr), ntohs((short) sockServ.sin_port));
  printf("est : '%s' de taille : %i \n", msgServToClient, retourReceive);


  /* 
   * Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)
   * La fonction close() permet la fermeture d'un socket. 
   * /!\ IMPORTANT : cela permet au système d'envoyer les données restantes (pour TCP)
   * ici "semble" inutile dans ce TP1 qui utilise UDP 
   * le close ne ferme pas la socket, elle est partagée par d'autres process 
   */
   int close(int ds);

  /* 
   * La fonction shutdown() permet la fermeture d'un socket dans un des deux sens (pour une connexion full-duplex) 
      * SHUT_RD or 0 : ferme les receptions (READ) 
      * SHUT_WR or 1 : ferme les envois (WRITE)
      * SHUT_RDWR or 2 : ferme les receptions (READ) et les envois (WRITE)
   */
   int shutdown(int ds, int SHUT_RDWR);
  
  printf("Client : je termine\n");
  return 0;
}
