/**
 * fichier: Pi.c
 * auteur: Johann Rosain
 * date: 23/03/2022
 **/
#include <stdio.h>
#include <stdlib.h>
#include <sys/ipc.h>
#include <sys/msg.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>

#include "shared.h"

int main(int argc, char **argv) {
    // Récupération du numéro de processus.
    pid_t nproc = getpid();

    if (nproc < EnumSize) {
        printf("Erreur : le processus ne produit pas une étiquette unique.\n");
        exit(EXIT_FAILURE);
    }

    // Récupération de la file de message.

    // Clé
    key_t key = ftok("./pourCle.txt", 128);
    if (key == ERROR) {
        perror("Erreur lors de la création de la clé ");
        exit(EXIT_FAILURE);
    }

    // File de message
    ipc_id stackid = msgget(key, IPC_CREAT|0666);
    if (stackid == ERROR) {
        perror("Erreur lors de l'accès à la file de message ");
        exit(EXIT_FAILURE);
    }

    printf("ID de la file de message : %i\n", stackid);

    // Tant que l'utilisateur veut envoyer des messages, il peut les saisir.
    while (1) {
        printf("Entrez un message svp (q pour quitter) : ");
        char message[MAX_MSG_SIZE];
        fgets(message, MAX_MSG_SIZE, stdin);

        if (strlen(message) == 2 && message[0] == 'q')
            break;

        // Demande d'accès à la variable de messages
        const AccessRequest request = (AccessRequest){.mtype = RequestAccess, .nproc = nproc};
        ssize_t res = msgsnd(stackid, (const void *)&request, sizeof(request.nproc), 0);
        if (res == ERROR) {
            perror("Erreur lors de la demande d'accès de la variable partagée ");
            exit(EXIT_FAILURE);
        }

        // Réception de la variable partagée
        SharedData data;
        res = msgrcv(stackid, (void *)&data, sizeof(data.message), nproc, 0);
        if (res == ERROR) {
            perror("Erreur lors de la réception de la variable partagée ");
            exit(EXIT_FAILURE);
        }
        printf("Variable partagée: %s\n", data.message);

        strcpy(data.message, message);
        data.mtype = ReturnData;
        res = msgsnd(stackid, (const void *)&data, strlen(data.message), 0);
        if (res == ERROR) {
            perror("Erreur lors de la modification de la variable partagée ");
            exit(EXIT_FAILURE);
        }

        printf("Variable partagée: %s\n", message);
    }
    
    printf("Fin de l'application.\n");
    return 0;
}