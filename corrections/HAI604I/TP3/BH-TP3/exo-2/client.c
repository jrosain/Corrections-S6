#include <netinet/in.h>
#include <stdio.h> 
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <string.h>
#include <sys/stat.h>

#define MAX_BUFFER_SIZE 146980

int main(int argc, char *argv[]) {

    if (argc != 4){
        printf("Utilisation : %s ip_serveur port_serveur nom_fichier\nRemarque : le parametre nom_fichier correspond au nom d'un fichier existant dans le répertoire emission\n", argv[0]);
        exit(0);
    }

    /* etape 1 : créer une socket */ 
    int ds = socket(PF_INET, SOCK_STREAM, 0);

    if (ds == -1) {
        perror("Client : erreur création de socket");
        exit(1);
    }
    
    /* etape 2 : designer la socket du serveur */
    struct sockaddr_in sock_serveur;
    sock_serveur.sin_family = AF_INET;
    sock_serveur.sin_addr.s_addr = inet_addr(argv[1]);
    sock_serveur.sin_port = htons((short) atoi(argv[2]));

    /* etape 3 : demander une connexion */
    printf("Client : demande de connexion\n");

    int res_connect = connect(ds, (const struct sockaddr*) &sock_serveur, sizeof(sock_serveur));

    if (res_connect == -1) {
        perror("Client : erreur connection serveur");
        exit(1);
    }

    printf("Client : connexion au serveur\n");
  
    /* etape 4 : envoi de fichier : attention la question est générale. Il faut creuser pour définir un protocole d'échange entre le client et le serveur pour envoyer correctement un fichier */

    /* le bout de code suivant est une lecture de contenu d'un fichier dont le nom est passé en paramètre.
      - pour lire un fichier, il faut l'ouvrir en mode lecture
      - la lecture se fait par blocs d'octets jusqu'à la fin du fichier.
      - la taille d'un bloc est définie par la constante MAX_BUFFER_SIZE que vous pouvez modifier.

      Le code est à compléter pour mettre en place l'envoi d'un fichier.
    */

    // construction du nom du chemin vers le fichier
    char* filepath = malloc(strlen(argv[3]) + 16); // ./emission/+nom fichier +\0
    filepath[0] = '\0';
    strcat(filepath, "./emission/");
    strcat(filepath, argv[3]);

    printf("Client : je vais envoyer %s\n", filepath);

    // obtenir la taille du fichier
    struct stat attributes;
    if (stat(filepath, &attributes) == -1) {
        perror("Client : erreur stat");
        free(filepath);
        exit(1);
    }

    size_t file_size = attributes.st_size; // cette copie est uniquement informer d'où obtenir la taille du fichier. 
    
    printf("Client : taille du fichier : %li octets\n", file_size);
    
    // lecture du contenu d'un fichier
    FILE* file = fopen(filepath, "rb");
    if (file == NULL) {
        perror("Client : erreur ouverture fichier \n");
        free(filepath);
        exit(1);   
    }
    printf("Client : envoie du fichier %s, envoie de %li octets\n", filepath, file_size);
    free(filepath);

    // On commence par envoyer la taille du nom du fichier pour que le serveur puisse le récupérer.
    int name_size = strlen(argv[3]) + 1;
    int res_send = send(ds, &name_size, sizeof(int), 0);

    if (res_send == -1) {
        perror("Client : erreur envoie de la taille du nom du fichier au serveur");
        exit(1);
    }

    // On envoie ensuite le nom du fichier.
    res_send = send(ds, argv[3], name_size, 0);

    if (res_send == -1) {
        perror("Client : erreur envoie du nom du fichier au serveur");
        exit(1);
    }

    // Enfin, on envoie le nombre d'octets du fichier envoyé pour que le serveur s'attende à en recevoir autant.
    res_send = send(ds, &file_size, sizeof(size_t), 0);

    if (res_send == -1) {
        perror("Client : erreur envoie de la taille du fichier au serveur");
        exit(1);
    }

    // Variables pour compter le nombre total d'octets envoyés et de send faits.
    size_t total_sent = 0; 
    size_t nb_send = 0;
    size_t total_lu = 0;
    char buffer[MAX_BUFFER_SIZE];

    while (total_lu < file_size) {
        int read = fread(buffer, sizeof(char), MAX_BUFFER_SIZE, file);
        if (read == 0) {
            if (ferror(file) != 0) {
                perror("Client : erreur lors de la lecture du fichier \n");
                fclose(file);
                exit(1);
            } else {
                printf("Client : arrivé a la fin du la lecture du fichier\n");// fin du fichier
                break;
            }
        }
        printf("Client : j'ai lu un bloc du fichier \n");  
        total_lu += read;

        // On envoie ensuite toutes les données lues par le buffer (puisqu'il sera écrasé par la suite)
        int bytes_send = 0;
        while (bytes_send != read) {
            res_send = send(ds, buffer + bytes_send, read - bytes_send, 0);
            if (res_send == -1) {
                perror("Client : erreur envoie d'un bloc de données");
                exit(1);
            }
            printf("Client : envoie de %i octets au serveur\n", res_send);
            bytes_send += res_send;
            total_sent += res_send;
            nb_send++;
        }
    }

    // fermeture du fichier
    fclose(file); 
    
    printf("Client : j'ai lu au total : %li octets \n", total_lu);
    printf("Client : j'ai envoyé au total : %li octets \n", total_sent);
    printf("Client : j'ai fait un total de %li envois \n", nb_send);

    int res_close = close(ds);

    if (res_close == -1) {
        perror("Client : erreur fermeture de la socket");
        exit(1);
    }
  
    printf("Client : c'est fini\n");
}
