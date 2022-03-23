/**
 * fichier: shared.h
 * auteur: Johann Rosain
 * date: 23/03/2022
 **/
#define ERROR -1
#define MAX_MSG_SIZE 1000

enum Tag {
    RequestAccess = 1,
    ReturnData,
    EnumSize,
};

typedef int ipc_id;

typedef struct access_request {
    long mtype;
    int nproc;
} AccessRequest;

typedef struct shared_data {
    long mtype;
    char message[MAX_MSG_SIZE];
} SharedData;