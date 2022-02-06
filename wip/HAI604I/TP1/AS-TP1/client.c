#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include<arpa/inet.h>
#include<string.h>

/* Programme client */

int main(int argc, char *argv[]) {

  /* je passe en paramètre l'adresse de la socket du serveur (IP et
     numéro de port) et un numéro de port à donner à la socket créée plus loin.*/

  /* Je teste le passage de parametres. Le nombre et la nature des
     paramètres sont à adapter en fonction des besoins. Sans ces
     paramètres, l'exécution doit être arrétée, autrement, elle
     aboutira à des erreurs.*/
  if (argc != 4){
    printf("utilisation : %s ip_serveur port_serveur port_client\n", argv[0]);
    exit(1);
  }

  /* Etape 1 : créer une socket */   
  int ds = socket(PF_INET, SOCK_DGRAM, 0);

  /* /!\ : Il est indispensable de tester les valeurs de retour de
     toutes les fonctions et agir en fonction des valeurs
     possibles. Voici un exemple */
  if (ds == -1){
    perror("[Client] : pb creation socket :");
    exit(1); // je choisis ici d'arrêter le programme car le reste
	     // dépendent de la réussite de la création de la socket.
  }
  
  /* J'ajoute des traces pour comprendre l'exécution et savoir
     localiser des éventuelles erreurs */
  printf("[Client] : creation de la socket réussie \n");
  
  // Je peux tester l'exécution de cette étape avant de passer à la
  // suite. Faire de même pour la suite : n'attendez pas de tout faire
  // avant de tester.
  
  /* Etape 2 : Nommer la socket du client */
   struct sockaddr_in ad;
   socklen_t len = sizeof(ad);
   ad.sin_family = AF_INET;            // IPv4
   ad.sin_addr.s_addr = INADDR_ANY;
   ad.sin_port = htons(atoi(argv[3])); 
   int res = bind(ds, (struct sockaddr *)&ad, len);
   if (res == -1){
      perror("[Client] : pb nommage socket :");
      exit(1);
  }
  /* Etape 3 : Désigner la socket du serveur */
   struct sockaddr_in srv;
   srv.sin_family = AF_INET;
   srv.sin_addr.s_addr = inet_addr(argv[1]); //91.174.102.81:32768
   srv.sin_port = htons(atoi(argv[2]));

  /* Etape 4 : envoyer un message au serveur  (voir sujet pour plus de détails)*/
   char msgUser[100];

   printf("Entrer un message : ");
   scanf("%s",msgUser);
   ssize_t msg = sendto(ds, msgUser, strlen(msgUser)+1, 0, (struct sockaddr*)&srv,  sizeof(srv));


   if (msg == -1){
      perror("[Client] : pb envoi message :");
      exit(1);
  }
  else
  {
     printf("Message bien envoyé...");
  }
  
   /* Etape 5 : recevoir un message du serveur (voir sujet pour plus de détails) */
   socklen_t servAdr = sizeof(srv);
   char bytesSent[100];
   ssize_t servRes = recvfrom(ds, bytesSent, 100, 0, (struct sockaddr*)&srv, &servAdr);

   if (servRes == -1) {
      perror("[CLIENT] Erreur lors de la réception du message du serveur ");
      exit(5);
   }
   printf("[CLIENT] %s", bytesSent);

   /* Etape 6 : fermer la socket (lorsqu'elle n'est plus utilisée)*/
   shutdown(ds, SHUT_RDWR); //free(msgUser);

   printf("[CLIENT] Sortie.\n");
  return 0;
}
