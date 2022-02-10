#define ERROR -1
#define MAX_BUFFER_SIZE 146980

/**
 * Crée une socket TCP IPv4.
 * S'il y a une erreur lors de la création de la socket, termine automatiquement
 * le programme en affichant l'erreur (perror) avec un retour d'erreur (EXIT_FAILURE).
 * Sinon, renvoie le descripteur de fichier correspondant à la socket.
 **/
int createTCPSocket();

/**
 * Crée une adresse IPv4.
 * Pour un nommage automatique, fournir une adresse vide et un port égal à 0.
 * Si le port est différent de 0, et inférieur à 1024, sort du programme avec
 * un retour d'erreur en affichant le problème : le port est réservé.
 **/
struct sockaddr_in createIPv4Address(const char *address, short port);

/**
 * Lie la socket `socketDescriptor` à l'adresse IPv4 fournie.
 * Termine le programme automatiquement sur une erreur (à la liaison ou au nommage).
 */
void bindSocket(int socketDescriptor, struct sockaddr_in *ipv4Address);

/**
 * Accepte la connexion d'un client, et met à jour l'adresse ipv4 passée en paramètre.
 * S'il y a un problème lors de la connexion, affiche l'erreur et termine le programme.
 **/
int acceptConnection(int serverSocket, struct sockaddr_in *ipv4Address);

/**
 * Essaie de connecter un client à l'adresse d'un serveur.
 * Termine le programme avec un code d'erreur s'il y a un problème.
 **/
void connectTo(int socketDescriptor, const struct sockaddr_in *serverAddress);