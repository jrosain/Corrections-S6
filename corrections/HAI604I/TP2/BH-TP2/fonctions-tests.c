#include <netinet/in.h>
#include <stdio.h> 
#include <arpa/inet.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>

///////////////////////////////////////////////
///// EXO 2 - Partie 1
///////////////////////////////////////////////

void exo2_1_client(int* ds) {
    char message[1500];
    printf("[Exo 2-1] : envoyer un message au serveur (1500 caractères max): ");
    fgets(message, 1500, stdin);
    printf("\n");

    if (send(*ds, message, strlen(message), 0) == -1) {
        perror("[Exo 2-1] : erreur envoi premier message");
    }
    if (send(*ds, message, strlen(message), 0) == -1) {
        perror("[Exo 2-1] : erreur envoi second message");
    }
}

void exo2_1_serveur(int* ds_client) {
    char message[4000];
    // Pour bloquer l'attente
    printf("[Exo 2-1] : Appuyer sur entrée pour mettre le serveur en attente d'un message");
    fgets(message, 1500, stdin);
    printf("[Exo 2-1] : Attente d'un message\n");
    int res = recv(*ds_client, message, 4000, 0);

    if (res == -1) {
        perror("[Exo 2-1] : erreur réception message");
    }
    else if (res == 0) {
        printf("[Exo 2-1] : réception impossible, connection close");
    }
    else {
        message[res] = '\0';
        printf("[Exo 2-1] : nombre d'octet : %i, message reçu : %s\n", res, message);
    }
}

///////////////////////////////////////////////
///// EXO 2 - Partie 2
///////////////////////////////////////////////

void exo2_2_client(int* ds) {
    char message[1500];
    printf("[Exo 2-2] : envoyer un message au serveur (1500 caractères max): ");
    fgets(message, 1500, stdin);
    printf("\n");

    int size_message = strlen(message) + 1;
    if (send(*ds, &size_message, sizeof(int), 0) == -1) {
        perror("[Exo 2-2] : erreur envoi premier entier");
    }
    if (send(*ds, message, strlen(message) + 1, 0) == -1) {
        perror("[Exo 2-2] : erreur envoi premier message");
    }
    if (send(*ds, &size_message, sizeof(int), 0) == -1) {
        perror("[Exo 2-2] : erreur envoi second entier");
    }
    if (send(*ds, message, strlen(message) + 1, 0) == -1) {
        perror("[Exo 2-2] : erreur envoi second message");
    }
}

void exo2_2_serveur(int* ds_client) {
    int size;
    printf("[Exo 2-2] : Attente d'un message\n");

    int res = recv(*ds_client, &size, sizeof(int), 0);

    if (res == -1) {
        perror("[Exo 2-2] : erreur réception entier");
    }
    else if (res == 0) {
        printf("[Exo 2-2] : réception impossible, connection close\n");
    }
    else {
        printf("[Exo 2-2] : taille du prochain message %i octets\n", size);
        char* message = (char*) malloc(size);
        res = recv(*ds_client, message, size, 0);

        if (res == -1) {
            perror("[Exo 2-2] : erreur réception entier");
            free(message);
        }
        else if (res == 0) {
            printf("[Exo 2-2] : réception impossible, connection close\n");
        }

        printf("[Exo 2-2] : nombre d'octet : %i, message reçu : %s\n", res, message);
        free(message);
    }
}

///////////////////////////////////////////////
///// EXO 2 - Partie 3
///////////////////////////////////////////////

void exo2_3_client(int* ds) {
    char message[1500];
    char nbs[4];
    printf("[Exo 2-3] : envoyer un message au serveur (1500 caractères max): ");
    fgets(message, 1500, stdin);
    printf("\n[Exo 2-3] : combien de fois l'envoyer (entre 0 et 999): ");
    fgets(nbs, 4, stdin);
    printf("\n");

    int nb = atoi(nbs);
    int size_message = strlen(message) + 1;

    printf("[Exo 2-3] : taille message envoyé : %i\n", size_message);
    printf("[Exo 2-3] : Envoie de %i fois ce message au serveur\n", nb);

    for (int i = 0; i < nb; ++i) {
        if (send(*ds, &size_message, sizeof(int), 0) == -1) {
            perror("[Exo 2-3] : erreur envoi entier");
        }
        if (send(*ds, message, size_message, 0) == -1) {
            perror("[Exo 2-3] : erreur envoi message");
        }
    }
}

void exo2_3_serveur(int* ds_client) {
    int size;
    printf("[Exo 2-3] : Attente des messages clients\n");

    int i = 1;
    while (1) {
        int res = recv(*ds_client, &size, sizeof(int), 0);

        if (res == -1) {
            perror("[Exo 2-3] : erreur réception entier");
            exit(1);
        }
        else if (res == 0) {
            printf("[Exo 2-3] : réception impossible, connection close\n");
            exit(1);
        }
        else {
            printf("[Exo 2-3] : Message %i, taille %i octets\n", i, size);
            char* message = (char*) malloc(size);
            int octets_restants = size;

            int j = 0;
            while (octets_restants > 0) {
                res = recv(*ds_client, message + (size - octets_restants), octets_restants, 0);
                if (res == -1) {
                    perror("[Exo 2-3] : erreur réception entier");
                    free(message);
                    exit(1);
                }
                else if (res == 0) {
                    printf("[Exo 2-3] : réception impossible, connection close\n");
                    exit(1);
                }

                octets_restants -= res;
                j++;
            }

            printf("[Exo 2-3] : Message reçu après %i réception(s)\n", j);
        }
        i++;
    }
}

///////////////////////////////////////////////
///// EXO 2 - Partie 4
///////////////////////////////////////////////

void exo2_4_client(int* ds) {
    char message[1000000];
    printf("[Exo 2-4] : envoyer un message très long au serveur: ");
    fgets(message, 1000000, stdin);
    printf("\n");

    int size_message = strlen(message) + 1;

    printf("[Exo 2-4] : taille message envoyé : %i\n", size_message);

    if (send(*ds, &size_message, sizeof(int), 0) == -1) {
        perror("[Exo 2-4] : erreur envoi entier");
    }
    if (send(*ds, message, size_message, 0) == -1) {
        perror("[Exo 2-4] : erreur envoi message");
    }
}

void exo2_4_serveur(int* ds_client) {
    int size;
    printf("[Exo 2-4] : Attente du long message client\n");

    int res = recv(*ds_client, &size, sizeof(int), 0);

    if (res == -1) {
        perror("[Exo 2-4] : erreur réception entier");
        exit(1);
    }
    else if (res == 0) {
        printf("[Exo 2-4] : réception impossible, connection close\n");
        exit(1);
    }
    else {
        printf("[Exo 2-4] : taille du long message : %i octets\n", size);
        char* message = (char*) malloc(size);
        int octets_restants = size;

        int j = 0;
        while (octets_restants > 0) {
            res = recv(*ds_client, message + (size - octets_restants), octets_restants, 0);
            if (res == -1) {
                perror("[Exo 2-4] : erreur réception entier");
                free(message);
                exit(1);
            }
            else if (res == 0) {
                printf("[Exo 2-4] : réception impossible, connection close\n");
                exit(1);
            }

            octets_restants -= res;
            j++;
        }

        printf("[Exo 2-4] : Message reconstruit après %i réception(s)\n", j);
    }
}

///////////////////////////////////////////////
///// EXO 3
///////////////////////////////////////////////

int sendTCP(int sock, void* msg, int sizeMsg) {
    int remaining = sizeMsg;

    while (remaining > 0) {
        printf("Send remaining : %i\n", remaining);
        int res = send(sock, msg + sizeMsg - remaining, remaining, 0);
        if (res <= 0) {
            return res;
        }
        remaining -= res;
    }

    return 1;
}

int recvTCP(int sock, void* msg, int sizeMsg) {
    int remaining = sizeMsg;

    while (remaining > 0) {
        printf("Receive remaining : %i\n", remaining);
        int res = recv(sock, msg + sizeMsg - remaining, remaining, 0);
        if (res <= 0) {
            return res;
        }
        remaining -= res;
    }

    return 1;
}

void exo3_client(int* ds) {
    char message[7000000];
    printf("[Exo 3] : envoyer un message au serveur: ");
    fgets(message, 7000000, stdin);
    printf("\n");

    int size_message = strlen(message) + 1;

    printf("[Exo 3] : taille message envoyé : %i\n", size_message);

    for (int i = 0; i < 2; ++i) {
        int res = sendTCP(*ds, &size_message, sizeof(int));

        if (res == -1) {
            perror("[Exo 3] : erreur envoi entier");
            return;
        }
        else if (res == 0) {
            printf("[Exo 3] : envoi entier impossible, connection close\n");
            return;
        }
        
        res = sendTCP(*ds, message, size_message);
        
        if (res == -1) {
            perror("[Exo 3] : erreur envoi message");
            return;
        }
        else if (res == 0) {
            printf("[Exo 3] : envoi message impossible, connection close\n");
            return;
        }

        printf("\n");
    }
}

void exo3_serveur(int* ds_client) {
    int size;
    printf("[Exo 3] : Attente du message client\n");

    for (int i = 0; i < 2; ++i) {
        int res = recvTCP(*ds_client, &size, sizeof(int));

        if (res == -1) {
            perror("[Exo 3] : erreur réception entier");
            return;
        }
        else if (res == 0) {
            printf("[Exo 3] : réception impossible, connection close\n");
            return;
        }

        char* message = (char*) malloc(size);
        res = recvTCP(*ds_client, message, size);

        if (res == -1) {
            perror("[Exo 3] : erreur réception message");
            return;
        }
        else if (res == 0) {
            printf("[Exo 3] : réception message impossible, connection close\n");
            return;
        }

        printf("\n");
    }

    printf("[Exo 3] : Le message fait %i octets\n", size);
}