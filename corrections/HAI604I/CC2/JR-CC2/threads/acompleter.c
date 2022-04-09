/**
 * fichier: acompleter.c
 * auteur: Johann Rosain
 * date: 09/04/2022
 **/

/*
 Programme ronde avec un thread bus et des threads visiteurs. 
 Les zones � compl�ter sont indiqu�es en commentaires.
 
 Les traces fournies sont suffisantes.
 
 Vous avez � votre disposition test/zoo qui est un ex�cutable vous illustrant le comportement attendu.
 
*/

#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simulation.h"

#define COND_EMBARQUEMENT 0
#define COND_DEBARQUEMENT 1

struct varPartagees {
  // structure regroupant toutes le varables partag�es entre threads
  
    int nbPlaces; // nombre total de places dans le bus
    int restantes;
    
    pthread_mutex_t lock;
    pthread_cond_t  conds[2];
};


struct params {
    // structure pour regrouper les param�tres d'un thread. 
    int idThread; // un identifiant de visiteur, de 1 � N (N le nombre total de visiteurs)
    
    struct varPartagees * varP;
};

// pour le thread bus
void * bus (void * p) {
    struct params * args = (struct params *) p;
    struct varPartagees * varP  = args -> varP;
    
    while(1) {
        // Appel à l'embarquement
        afficher('b', "embarquement immediat, soyez les bienvenus!", 0);

        pthread_mutex_lock(&varP->lock);
        // Attente que le bus soit plein.
        while (varP->restantes > 0) {
            afficher('b', "attente que le bus soit complet", 0);
            pthread_cond_wait(&varP->conds[COND_EMBARQUEMENT], &varP->lock);
        }
        pthread_mutex_unlock(&varP->lock);
        afficher('b',"bus complet, la visite commence !", 0); 

        visite(4); // vous pouvez changer la valeur du param�tre (voir .h)

        pthread_mutex_lock(&varP->lock);
        // Appel à la descente du bus
        afficher('b',"visite terminee, tout le monde descend !", 0);
        pthread_cond_broadcast(&varP->conds[COND_DEBARQUEMENT]);

        // Attente que tout le monde soit descendu.
        while (varP->restantes != varP->nbPlaces) {
            afficher('b', "attente que tout le monde descende", 0);
            pthread_cond_wait(&varP->conds[COND_DEBARQUEMENT], &varP->lock);
        }
        // Nouvel appel à la montée 
        pthread_cond_broadcast(&varP->conds[COND_EMBARQUEMENT]);
        pthread_mutex_unlock(&varP->lock);    
    }

    pthread_exit(NULL); 
}


// pour le thread visiteur
void * visiteur (void * p) {
    struct params * args = (struct params *) p;
    struct  varPartagees * varP = args -> varP;
    
    afficher('v', "je demande a monter", args -> idThread);

    // Mise en place de la montée
    pthread_mutex_lock(&varP->lock);
    while (varP->restantes == 0) {
        afficher('v', "pas de place, j'attends", args -> idThread);
        pthread_cond_wait(&varP->conds[COND_EMBARQUEMENT], &varP->lock);
    }
    varP->restantes--;
    pthread_mutex_unlock(&varP->lock);
    
    // simulation mont�e du visiteur
    afficher('v', "je monte ...", args -> idThread);
    pthread_mutex_lock(&varP->lock);
    monterOuDescendre();
    pthread_mutex_unlock(&varP->lock);
    afficher('v', "je suis a bord et bien installe !", args -> idThread);
    pthread_mutex_lock(&varP->lock);
    pthread_cond_broadcast(&varP->conds[COND_EMBARQUEMENT]);
    pthread_mutex_unlock(&varP->lock);
    
    // ici se produit automatiquement la visite qui est g�r�e par le bus
    pthread_mutex_lock(&varP->lock);
    afficher('v', "j'attends la fin de la visite", args -> idThread);
    pthread_cond_wait(&varP->conds[COND_DEBARQUEMENT], &varP->lock);
    pthread_mutex_unlock(&varP->lock);
    
    afficher('v', "visite terminee, je descends ...", args -> idThread);
    // .. zone qui pourrait �ventuellement vous �tre utile
    monterOuDescendre();
    pthread_mutex_lock(&varP->lock);
    varP->restantes++;
    afficher('v', "je suis descendu !", args -> idThread);
    pthread_cond_broadcast(&varP->conds[COND_DEBARQUEMENT]);
    pthread_mutex_unlock(&varP->lock);
    
    pthread_exit(NULL); 
}


int main(int argc, char * argv[]){  
    if (argc!=3) {
        printf(" argument requis \n %s nombres_places_bus nombre_visiteurs\n", argv[0]);
        exit(1);
    }

    initDefault(atoi(argv[2])); // ne pas modifier cet appel ni le d�placer.
    
    // initialisations 
    pthread_t threads[atoi(argv[2])+1];
    struct params tabParams[atoi(argv[2])+1];
    
    struct varPartagees varP = (struct varPartagees) { .nbPlaces = atoi(argv[1]), .restantes = atoi(argv[1]) };

    int err;
    if ((err = pthread_mutex_init(&varP.lock, NULL)) != 0) {
        printf("Erreur lors de l'initialisation du mutex: %s\n", strerror(err));
        exit(EXIT_FAILURE);
    }
    for (size_t i = COND_EMBARQUEMENT; i <= COND_DEBARQUEMENT; ++i) {
        if ((err = pthread_cond_init(&varP.conds[i], NULL)) != 0) {
            printf("Erreur lors de la création de la condition: %s\n", strerror(err));
            exit(EXIT_FAILURE);
        }
    }
    
    // cr�ation des threads
    tabParams[0].idThread = 0;
    tabParams[0].varP = &varP; 
    if (pthread_create(&(threads[0]), NULL, bus, &(tabParams[0])) != 0){
        perror("erreur creation thread bus");
        exit(1);
    }  

    for (int i = 1; i < atoi(argv[2])+1; i++){
        tabParams[i].idThread = i;
        tabParams[i].varP = &varP; 
        if (pthread_create(&threads[i], NULL, visiteur, &(tabParams[i])) != 0){
            perror("erreur creation thread visiteur");
            exit(1);
        }
    }

    // attente de la fin des  threads. 
    for (int i = 0; i < atoi(argv[2])+1; i++)
        if (pthread_join(threads[i], NULL) != 0){
        perror("erreur attente thread");
        exit(1);
    }
        
    // Destruction du mutex et des conditions
    if ((err = pthread_mutex_destroy(&varP.lock)) != 0) {
        printf("Erreur lors de la destruction du mutex: %s\n", strerror(err));
        exit(EXIT_FAILURE);
    }
    for (size_t i = COND_EMBARQUEMENT; i <= COND_DEBARQUEMENT; ++i) {
        if ((err = pthread_cond_destroy(&varP.conds[i])) != 0) {
            printf("Erreur lors de la création de la condition: %s\n", strerror(err));
            exit(EXIT_FAILURE);
        }
    }
    
    return 0;
}
 
