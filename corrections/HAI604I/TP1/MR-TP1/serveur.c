#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include<arpa/inet.h>
#include<string.h>

#define ERROR -1

/* Programme serveur */

int main(int argc, char *argv[]) {

 /* 
  * Je passe en paramètre le numéro de port qui sera donné à la socket créée plus loin.
  * Je teste le passage de parametres. 
  * Le nombre et la nature des paramètres sont à adapter en fonction des besoins. 
  * Sans cesparamètres, l'exécution doit être arrétée, autrement, elle aboutira à des erreurs.
  */
  if (argc != 2){
    printf("utilisation : %s port_serveur\n", argv[0]);
    exit(1);
  }

  int numPortServ = atoi(argv[1]);
  printf("Port du serveur : %i \n", numPortServ);

 /* 
  * Etape 1 : créer une socket 
  */   
  int ds = socket(PF_INET, SOCK_DGRAM, 0);

  /* 
  * /!\ Il est indispensable de tester les valeurs de retour de toutes les fonctions et agir en fonction des valeurs possibles. /!\ 
  * Voici un exemple 
  */
  if (ds == -1){
    perror("Serveur : pb creation socket :");
    exit(1); 
  }

  printf("ds = %i \n",ds);
  
 /* 
  * J'ajoute des traces pour comprendre l'exécution et savoir localiser des éventuelles erreurs 
  */
  printf("Serveur : creation de la socket réussie \n");
  
  
 /* 
  * Etape 2 : Nommer la socket du seveur 
  */
  struct sockaddr_in sockServeur;
 /*
  * 3 variables :
  * sin_family : indique la famille d'adresseIp (toujours AF_INET pour nous car on utilise les ipV4) 
  * sin_addr : structure de l'adresseIp (INADDR_ANY indique que la socket est associée à toutes les adresseIp de la machine)
  * sin_port : le port du Serveur 
  */
  sockServeur.sin_family = AF_INET;
  sockServeur.sin_addr.s_addr = INADDR_ANY;
  sockServeur.sin_port = htons((short)numPortServ);

 /*
  * On effectue la lisaison descripteur de la socket et le couple (adresseIP et Port), en indiquant la taille du couple
  */
  int nomSock = bind(ds, (struct sockaddr*)&sockServeur, sizeof(sockServeur));

  if (nomSock == -1){
    perror("Serveur : pb creation liaison :");
    exit(1); 
  }

  printf("nomSock = %i \n",nomSock);
 
 /* 
  * Etape 4 : recevoir un message du client (voir sujet pour plus de détails)
  * Important : on a cree la socket en indiquant SOCK_DGRAM,donc on utilise le protocole UDP 
  * pour UDP, on utilise la fonction sendto pour envoyer des messages 
  * et la fonction recvfrom pour recevoir des messages 
  */
  char msg[100] ;
  struct sockaddr_in sockClient;
  /*
  * On initialise la taille de la structure de la socket client
  * si on ne fait pas ça, on aura 0 dans la structure qui est censé contenir la taille de l'adresse source
  */
  socklen_t lgAdr = sizeof(sockClient);

  int retourReceive = recvfrom(ds,msg,sizeof(msg),0, (struct sockaddr*)&sockClient, &lgAdr );
  if (retourReceive == -1) {
    printf("La reception du message est en erreur \n");
  }
 
  printf("Le message reçu par le serveur du client: (%s:%i) ",inet_ntoa(sockClient.sin_addr), ntohs((short) sockClient.sin_port));
  printf("est : '%s' de taille : %i \n", msg, retourReceive);
  
 /* 
  * Etape 5 : envoyer un message au client (voir sujet pour plus de détails)
  */

  char *msgServToClient;
  size_t tailleMsg;
  int res;
  printf("Saisir le message a envoyer (max 100 char) :");
  res = getline(&msgServToClient, &tailleMsg, stdin);

  if (res == ERROR){
    perror("Erreur lors de l'envoi d'un message au serveur");
    exit(3);
  }

  /* 
  * ici, on supprime le retour charriot 
  */

  int len = strlen(msgServToClient)-1;

  // Supprime le \n à la fin de la ligne d'input utilisateur
  if (msgServToClient[len] == '\n'){
    msgServToClient[len] = '\0';
  }

  int retourSendto = sendto(ds,msgServToClient,strlen(msgServToClient)+1,0,( struct sockaddr*)&sockClient, sizeof(sockClient));
  printf("message = %s \n",msgServToClient);
  printf("retourSendto = %i \n",retourSendto);

  if (retourSendto == -1) {
    // traitement de l'erreur
    perror("L'envoi du message est en erreur \n");
  }
  
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

  printf("Serveur : je termine\n");
  return 0;
}
