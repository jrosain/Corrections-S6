#include <string.h>
#include <stdio.h>
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include "calcul.h"

struct paramsFonctionThread {
    int idThread;
    int waitTime;
};

void* fonctionThread(void* params){
    struct paramsFonctionThread* args = (struct paramsFonctionThread*) params;
    printf("Id thread %lu : %i\n", pthread_self(), args->idThread);
    printf("Début calcul thread %i\n", args->idThread);

    calcul(args->waitTime);

    printf("Fin calcul thread %i\n", args->idThread);

    int* ret = malloc(sizeof(int));
    *ret = args->idThread;
    pthread_exit(ret);
}

int main(int argc, char * argv[]) {
    if (argc < 2 ) {
        printf("utilisation: %s nombre_threads\n", argv[0]);
        return 1;
    }
  
    pthread_t threads[atoi(argv[1])];
    struct paramsFonctionThread params[atoi(argv[1])];
  
    for (int i = 0; i < atoi(argv[1]); i++) {
        params[i].idThread = i;
        params[i].waitTime = i;
        printf("Entrée boucle thread %i\n", i);

        if (pthread_create(&threads[i], NULL, fonctionThread, &params[i]) != 0){
            perror("erreur creation thread");
            exit(1);
        }

        printf("Sortie boucle thread %i\n", i);
    }

    int res;
    int* ret;
    for (int i = 0; i < atoi(argv[1]); i++) {
        if ((res = pthread_join(threads[i], (void**) &ret)) != 0) {
            printf("Erreur %i durant join thread %i\n", res, i);
        }
        printf("Le résultat du thread %i est %i\n", i, *ret);
        free(ret);
    }

    printf("Cette ligne doit être la dernière ligne du programme\n");

    return 0;
}
