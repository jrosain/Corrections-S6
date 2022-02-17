    #include <stdio.h> 
    #include <unistd.h>
    #include <sys/types.h>
    #include <sys/socket.h>
    #include <netdb.h>
    #include <stdlib.h>
    #include <arpa/inet.h>
    #include <string.h>
    #include <sys/stat.h>
    #include "tcp-utils.c"

    #define MAX_BUFFER_SIZE 146980

    int main(int argc, char *argv[]) {

    if (argc != 4){
        printf("utilisation : client ip_serveur port_serveur nom_fichier\n Remaque : le parametre nom_fichier correspond au nom d'un fichier existant dans le répertoire emission\n");
        exit(0);
    }

    /* etape 1 : créer une socket */   
    int ds = creerSocket();
    /* etape 2 : designer la socket du serveur */
    struct sockaddr_in sockServ = designerSocket(argv[2],argv[1]);
    /* etape 3 : demander une connexion */
    connecterTCP(ds, &sockServ);
    /* etape 4 : envoi de fichier */
    int totalSent = 0; // nombre total d'octet effectivement envoyés au serveur

    //créer filepath
    char* filepath = (char*)malloc(strlen(argv[3]) + 16); // ./emission/+nom fichier +\0
    filepath[0] = '\0';
    strcat(filepath, "./emission/");
    strcat(filepath, argv[3]);

    printf("Client : je vais envoyer %s\n", filepath);

    // obtenir la taille du fichier
    struct stat attributes;
    if(stat(filepath, &attributes) == -1){
        perror("Client : erreur stat");
        free(filepath);
        exit(1);
    }

    int file_size = attributes.st_size; // taille du fichier.
    
    printf("Client : taille du fichier : %d octets\n", file_size);
    
    // lecture du contenu d'un fichier
    FILE* file = openFileFTP(filepath, "rb");

    // envoyer le nom du fichier
    send2TCP(ds, argv[3], strlen(argv[3]));
    free(filepath);

    // envoyer la taille du fichier
    sendTCP(ds, &file_size, sizeof(int));

    int total_lu = 0;
    char buffer[MAX_BUFFER_SIZE];


    while(total_lu < file_size){
        
        size_t read = fread(buffer, sizeof(char), MAX_BUFFER_SIZE, file);
        if(read == 0) {
            if(ferror(file) != 0){
            perror("Client : erreur lors de la lecture du fichier \n");
            fclose(file);
            exit(1);
            } else {
                printf("Client : arrivé a la fin du la lecture du fichier\n");// fin du fichier
                break;
            }
        }

        totalSent += send2TCP(ds, buffer, read);
        total_lu += read;
    }

    // fermeture du fichier
    fclose(file); 
    
    printf("Client : j'ai lu au total : %d octets \n", total_lu);
    printf("Client : j'ai envoyé au total : %d octets \n", totalSent);  
    close(ds);
    printf("Client : c'est fini\n");

}
