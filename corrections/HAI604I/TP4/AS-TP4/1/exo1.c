#include <string.h>
#include <stdio.h>//perror
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include "calcul.h"


struct paramsFonctionThread {
  int idThread;
  long unsigned int* data;
};


void * fonctionThread (void * params){

  struct paramsFonctionThread * arg = (struct paramsFonctionThread *) params;
  pthread_t moi = pthread_self();
  printf("Thread : %lu, process %d\n",moi,getpid());
  arg->data[arg->idThread] = moi;
  //printf("Calcul... \n");
  //calcul(1);
  printf("Le thread %lu dans le process %d a terminé\n",moi,getpid());
  pthread_exit(NULL);

    
}


int main(int argc, char * argv[]){

  if (argc < 2 ){
    printf("utilisation: %s  nombre_threads  \n", argv[0]);
    return 1;
  }

  pthread_t threads[atoi(argv[1])];
  // création des threards
  long unsigned int chaine[atoi(argv[1])];
  struct paramsFonctionThread ids;
  ids.idThread =0;
  ids.data = chaine;
  for (int i = 0; i < atoi(argv[1]); i++){
    ids.idThread = i;
    if (pthread_create(&threads[i], NULL, fonctionThread, &ids) != 0){
      perror("erreur creation thread");
      exit(1);
    }
  }

  for (int i = 0; i < atoi(argv[1]); i++) {
    pthread_join(threads[i], NULL);
  }

  return 0;
 
}
 
