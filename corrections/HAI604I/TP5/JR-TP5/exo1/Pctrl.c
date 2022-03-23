/**
 * fichier: Pctrl.c
 * auteur: Johann Rosain
 * date: 23/03/2022
 **/
#include <stdio.h>
#include <stdlib.h>
#include <sys/ipc.h>
#include <sys/msg.h>
#include <string.h>
#include <signal.h>

#include "shared.h"

ipc_id stackid;

void destructAndExit() {
    if (msgctl(stackid, IPC_RMID, NULL) == ERROR) {
        perror("Erreur fatale lors de l'exécution du processus ");
    }
    exit(EXIT_FAILURE);
}

void sigHandler(int signum) {
    /*if (msgctl(stackid, IPC_RMID, NULL) == ERROR) {
        perror("SIGINT: erreur fatale lors de l'exécution du processus ");
        exit(EXIT_FAILURE);
    }*/
}

int main(int argc, char **argv) {
    if (argc != 2) {
        printf("Utilisation : %s message\n", argv[0]);
        exit(EXIT_FAILURE);
    }

    // Enregistrement du sigHandler pour ctrl+c le programme et détruire l'IPC
    signal(SIGINT, sigHandler);

    char message[MAX_MSG_SIZE];
    strcpy(message, argv[1]);

    printf("Message utilisateur: %s\n", message);

    // Création de la file de message.

    // Clé
    key_t key = ftok("./pourCle.txt", 128);
    if (key == ERROR) {
        perror("Erreur lors de la création de la clé ");
        exit(EXIT_FAILURE);
    }

    // File de message
    stackid = msgget(key, IPC_CREAT|0666);
    if (stackid == ERROR) {
        perror("Erreur lors de la création ou l'accès de la file de message ");
        exit(EXIT_FAILURE);
    }

    // Boucle qui attend la demande de la ressource partagée
    while (1) {
        // Attente d'une demande d'accès
        AccessRequest processusRequest;
        ssize_t res = msgrcv(stackid, (void *)&processusRequest, sizeof(processusRequest.nproc), RequestAccess, 0);
        if (res == ERROR) {
            perror("Erreur lors de la demande d'accès à la variable partagée ");
            // Destruction de la file et au revoir.
            destructAndExit();
        }

        printf("Accès donné au processus %i\n", processusRequest.nproc);

        // Envoie de la donnée au processus
        SharedData dataSent = (SharedData){.mtype = processusRequest.nproc};
        strcpy(dataSent.message, message);
        res = msgsnd(stackid, (const void *)&dataSent, sizeof(dataSent.message), 0);
        if (res == ERROR) {
            perror("Erreur lors de l'envoie du message dans la file de messages ");
            destructAndExit();
        }

        printf("Variable envoyée.\n");

        // Attente de la réception de la « finition » de la consultation ou modification du message.
        SharedData dataReceived;
        res = msgrcv(stackid, (void *)&dataReceived, sizeof(dataReceived.message), ReturnData, 0);
        if (res == ERROR) {
            perror("Erreur lors de la récupération de la variable partagée ");
            // Destruction de la file et au revoir.
            destructAndExit();
        }

        // Copie dans la variable locale de message
        strcpy(message, dataReceived.message);
        printf("Message: %s\n", message);
    }

    printf("Fin de l'application.\n");
    return 0;
}