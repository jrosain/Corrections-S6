#include <netinet/in.h>
#include <stdio.h>
#include <sys/types.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

#define MAX_BUFFER_SIZE 146980

int main(int argc, char *argv[])
{   
    /* etape 1 : creer une socket d'écoute des demandes de connexions*/
    int ds = socket(PF_INET, SOCK_STREAM, 0);

    if (ds == -1) {
        perror("Serveur : erreur création socket");
        exit(1);
    }
    
    /* etape 2 : nommage de la socket */
    struct sockaddr_in socket_serveur;
    socket_serveur.sin_family = AF_INET;
    socket_serveur.sin_addr.s_addr = INADDR_ANY;
    socket_serveur.sin_port = htons((short) 0);

    int res_bind = bind(ds, (const struct sockaddr*) &socket_serveur, sizeof(socket_serveur));
  
    if (res_bind == -1) {
        perror("Serveur : erreur nommage de la socket");
        exit(1);
    }

    socklen_t len = sizeof(socket_serveur);
    int res_gsn = getsockname(ds, (struct sockaddr*) &socket_serveur, &len);

    if (res_gsn == -1) {
        perror("Serveur : erreur récupération du nom de la socket");
        exit(1);
    }

    printf("Serveur : le port utilisé est %i\n", ntohs(socket_serveur.sin_port));

    /* etape 3 : mise en ecoute des demandes de connexions */
    int res_listen = listen(ds, 10);

    if (res_listen == -1) {
        perror("Serveur : erreur lors de la mise en écoute");
        exit(1);
    }

    printf("Serveur : attente de clients\n");

    /* etape 4 : plus qu'a attendre la demande de clients */
    int parent_pid = getpid();
    int ds_client = 0;

    while (parent_pid != 0) {
        struct sockaddr_in socket_client;
        len = sizeof(socket_client);
        ds_client = accept(ds, (struct sockaddr*) &socket_client, &len);

        parent_pid = fork();

        if (ds_client == -1 && parent_pid == 0) {
            perror("Serveur : erreur lors de la connexion d'un client");
            exit(1);
        }
    }

    printf("Serveur : client %i, connecté\n", ds_client);

    /* etape 5 : discussion avec le client */

    int name_size;
    int res_recv = recv(ds_client, &name_size, sizeof(int), 0);

    // On récupère la taille du nom du fichier.
    if (res_recv == -1) {
        perror("Serveur : erreur réception de la taille du nom du fichier");
        exit(1);
    }
    else if (res_recv == 0) {
        printf("Serveur : client %i déconnecté\n", ds_client);
        exit(1);
    }
    printf("Serveur : %i\n", name_size);

    // On réceptionne ensuite le nom du fichier.
    char filename[name_size];
    res_recv = recv(ds_client, &filename, name_size, 0);

    if (res_recv == -1) {
        perror("Serveur : erreur réception du nom du fichier");
        exit(1);
    }
    else if (res_recv == 0) {
        printf("Serveur : client %i déconnecté\n", ds_client);
        exit(1);
    }

    // Enfin, on réceptionne le nombre d'octets du fichier envoyé par le client.
    size_t file_size;
    res_recv = recv(ds_client, &file_size, sizeof(size_t), 0);

    if (res_recv == -1) {
        perror("Serveur : erreur réception de la taille du fichier");
        exit(1);
    }
    else if (res_recv == 0) {
        printf("Serveur : client %i déconnecté\n", ds_client);
        exit(1);
    }

    // Convertisseur entier -> string
    char ds_client_name[10];
    sprintf(ds_client_name, "%d", ds_client);

    char* filepath = malloc(name_size + strlen(ds_client_name) + 21); // ./emission/client-[num-client]-+nom fichier +\0
    filepath[0] = '\0';
    strcat(filepath, "./reception/client-");
    strcat(filepath, ds_client_name);
    strcat(filepath, "-");
    strcat(filepath, filename);
    
    // On ouvre le fichier dans lequel on va écrire
    FILE* file = fopen(filepath, "wb");
    if (file == NULL) {
        perror("Serveur : erreur ouverture fichier: \n");
        free(filepath);
        exit(1);  
    }
    printf("Serveur : ouverture du fichier %s, attente de la réception de %li octets du client %i\n", filepath, file_size, ds_client);
    free(filepath);

    // Variables pour compter le nombre total d'octets lus et de recv fait.
    // Un compteur du nombre total d'octets recus d'un client
    size_t total_recv = 0;
    size_t nb_recv = 0;
    size_t total_ecrit = 0;
    char buffer[MAX_BUFFER_SIZE];

    while (total_recv < file_size) {
        // On récupère d'abord toutes les données envoyées par le client avant de les mettre dans le fichier
        res_recv = recv(ds_client, buffer, MAX_BUFFER_SIZE, 0);
        if (res_recv == -1) {
            perror("Serveur : erreur réception d'un bloc de données");
            exit(1);
        }
        else if (res_recv == 0) {
            printf("Serveur : client %i déconnecté, impossible de finir le téléversement\\n", ds_client);
            exit(1);
        }
        printf("Serveur : réception de %i octets du client %i\n", res_recv, ds_client);
        total_recv += res_recv;
        nb_recv++;

        int total_write = 0;
        while (total_write != res_recv) {
            int written = fwrite(buffer, sizeof(char), res_recv, file);
            if (written <= 0) {
                perror("Serveur : erreur a l'ecriture du fichier \n");
                fclose(file); 
                exit(1);
            }
            total_write += written;
            total_ecrit += written;

            printf("Serveur : j'ai écrit un bloc dans le fichier (client %i)\n", ds_client);
        }
    }

    printf("Serveur : écriture dans le fichier réussie (client %i). Vous pouvez vérifier la création du fichier et son contenu.\n", ds_client);

    // fermeture du fichier
    fclose(file); 
    
    printf("Serveur : (client %i) j'ai écrit au total : %li octets \n", ds_client, total_ecrit);
    printf("Serveur : (client %i) j'ai reçu au total : %li octets \n", ds_client, total_recv);
    printf("Serveur : (client %i) j'ai fait un total de %li réceptions \n", ds_client, nb_recv);

    int res_close = close(ds_client);

    if (res_close == -1) {
        perror("Serveur : erreur fermeture de la socket client");
        exit(1);
    }
      
    printf("Serveur : déconnexion client %i\n", ds_client);
}

/*
1 073 741 824 octets
11514 réceptions
7306 envois

1 073 835 880 octets envoyés
1 073 754 383 octets reçus
11513 réceptions
7306 envois

427 769 856
427 769 856
*/