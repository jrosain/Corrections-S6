#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include "calcul.h"


struct predicatRdv {
// regroupes les données partagées entres les threads participants aux RdV :
  int waitingThread;
  pthread_mutex_t* lock;
  pthread_cond_t* cond;

};

struct params {
  // structure pour regrouper les paramètres d'un thread. 
  int idThread; // un identifiant de thread, de 1 à N (N le nombre total de theads secondaires)
  int num;
  struct predicatRdv* sharedVar;

};

// fonction associée a chaque thread participant au RdV.
void * participant (void * p){ 

  struct params * args = (struct params *) p;
  struct predicatRdv * predicat = args -> sharedVar;

  printf("[Thread %i] : je me mets en attente du verrou\n", args->idThread);
  pthread_mutex_lock(predicat->lock);
  printf("[Thread %i] : je vérouille le verrou\n", args->idThread);

  int wait = 1;

  printf("[Thread %i] : début calcul, duration : %is\n", args->idThread, wait*3);
  calcul(wait);
  printf("[Thread %i] : fin calcul\n", args->idThread);

  if (++(predicat->waitingThread) == args->num) {
      printf("[Thread %i] : dernier thread je réveille tout le monde !\n", args->idThread);
      pthread_cond_broadcast(predicat->cond);
  }

  // RdV 
  while (predicat->waitingThread != args->num) {  // attention : le dernier arrivé ne doit pas attendre. Il doit réveiller tous les autres.
    printf("[Thread %i] : je dors et je libère le verrou\n", args->idThread);
    pthread_cond_wait(predicat->cond, predicat->lock);
    printf("[Thread %i] : je me réveille et vérouille le verrou\n", args->idThread);
    
  }

  wait = 2;
  pthread_mutex_unlock(predicat->lock);
  printf("[Thread %i] : je libère le verrou\n", args->idThread);
  
  // reprise et poursuite de l'execution.
  printf("[Thread %i] : début calcul final, duration : %is\n", args->idThread, wait*3);
  calcul(wait);
  printf("[Thread %i] : fin calcul final\n", args->idThread);

  pthread_exit(NULL); // fortement recommandé.
}


int main(int argc, char * argv[]){
  
  if (argc != 2) {
      printf("argument requis\n");
      printf("%s nombre_Threads\n", argv[0]);
      exit(1);
  }

  // initialisations 
  pthread_t threads[atoi(argv[1])];
  struct params tabParams[atoi(argv[1])];


  srand(atoi(argv[1]));  // initialisation de rand pour la simulation de longs calculs

  struct predicatRdv predicat;
  predicat.waitingThread = 0;

  pthread_mutex_t lock;
  pthread_cond_t cond;
  pthread_mutex_init(&lock, NULL);
  pthread_cond_init(&cond, NULL);

  // création des threards 
  for (int i = 0; i < atoi(argv[1]); i++){
    tabParams[i].idThread = i + 1;
    tabParams[i].sharedVar = &predicat;
    tabParams[i].num = atoi(argv[1]);
    predicat.lock = &lock;
    predicat.cond = &cond;

  }
  for (int i = 0; i < atoi(argv[1]); i++){
      tabParams->idThread = i;
      if (pthread_create(&threads[i], NULL, participant, tabParams) != 0){
        perror("erreur creation thread");
        exit(1);
      }
  }

  // Attente de la fin des threads. Partie obligatoire 
  for (int i = 0; i < atoi(argv[1]); i++) {
      pthread_join(threads[i], NULL);
  }

  printf("[Thread principal] : fin de tous les threads secondaires\n");
  
  // terminer "proprement".
  pthread_mutex_destroy(&lock);
  pthread_cond_destroy(&cond);
}