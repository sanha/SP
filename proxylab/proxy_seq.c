/*
 * proxy.c - CS:APP Web proxy
 *
 * Student ID: 2013-11415
 *         Name: Sanha Lee
 * 
 * IMPORTANT: Give a high level description of your code here. You
 * must also provide a header comment at the beginning of each
 * function that describes what that function does.
 */ 

#include "csapp.h"

/* needed to use tm structure during logging */
#include <time.h>

/* The name of the proxy's log file */
#define PROXY_LOG "proxy.log"

/* Undefine this if you don't want debugging output */
#define DEBUG

/*
 * Functions to define
 */
void *process_request(void* vargp);
int open_clientfd_ts(char *hostname, int port, sem_t *mutexp);
ssize_t Rio_readn_w(int fd, void *ptr, size_t nbytes);
ssize_t Rio_readlineb_w(rio_t *rp, void *usrbuf, size_t maxlen);
void Rio_writen_w(int fd, void *usrbuf, size_t n);

/*
 * Function added
 */
int parse_client (char *buf, char **host, char **port, char **msg);
void logging (char *IP, int port, size_t size, char *msg);

/*
 * Global variables
 */
int bytecnt = 0;
int proxy_port = 0;

/*
 * main - Main routine for the proxy program
 */
int main(int argc, char **argv)
{
	/* Check arguments */
	if (argc != 2) {
        	fprintf(stderr, "Usage: %s <port number>\n", argv[0]);
	        exit(0);
	}

	/* Protect thread from terminated because of close1d fd */
	Signal (SIGPIPE, SIG_IGN);

	int port = atoi(argv[1]);
	proxy_port = port;
	struct sockaddr_in clientaddr;
	int clientlen = sizeof (clientaddr);
	pthread_t tid; 

	int listenfd = open_listenfd(port);
	while (1) {
        	int *connfdp = Malloc (sizeof (int));
	        struct hostent *hp;
        	char *haddrp;
	        int client_port;

	        *connfdp = Accept(listenfd, (SA *) &clientaddr, &clientlen);
        	/* determine the domain name and IP address of the client */
	        hp = Gethostbyaddr((const char *)&clientaddr.sin_addr.s_addr, 
        		sizeof(clientaddr.sin_addr.s_addr), AF_INET);

		/* Have to protect race from ntoa ntohs */
	        haddrp = inet_ntoa (clientaddr.sin_addr);
        	client_port = ntohs (clientaddr.sin_port);

	        printf("Proxy server connected to %s (%s), port %d\n",
        		hp->h_name, haddrp, client_port);	// TODO: CHECK

		/* Sequential proxy, acting like client */
		char buf[MAXLINE];
		size_t n;
		rio_t rio_client, rio_server;

		Rio_readinitb (&rio_client, *connfdp);		// Initialize client robust I/O //TODO: check
		while ((n = Rio_readlineb_w (&rio_client, buf, MAXLINE)) != 0) {	// reading msg from client
			char *host;
			char *port;
			char *msg;
			int clientfd;

			bytecnt += n;	// TODO: thread!

			printf ("Main while loop received %d bytes (%d total)\n", (int) n, bytecnt);	// TODO:

			/* parsing client's input */
			if (parse_client (buf, &host, &port, &msg) < 0) {
				char *err = "proxy usage: <host> <port> <message>\n";
				printf ("%s", err);	// TODO:
				Rio_writen_w (*connfdp, err, strlen (err));
				continue;
			}

			/* make port to integer */
			unsigned int port_num = (unsigned int) atoi (port);

			/* Destination port have to be differ from proxy's port */
                        if (port_num == proxy_port) {
                                char *err = "connecting server port have to be different with proxy's\n";
                                Rio_writen_w (*connfdp, err, strlen (err));
                                continue;
                        }


			/* open clientfd as a proxy client */
			if ((clientfd = open_clientfd (host, port_num)) < 0) {
				char *err = "proxy couldn't open clientfd\n";
				printf ("%s", err);	// TODO:
				Rio_writen_w (*connfdp, err, strlen (err));
				continue;
			}	

			printf ("Client request is: Host %s, Port %d, Msg %s", host, port_num, msg);

			/* interact with real server: msg sending and receiving, logging */
			Rio_readinitb (&rio_server, clientfd);		// initialize server robust I/O
			Rio_writen_w (clientfd, msg, strlen (msg));	// sending message
			if ((n = Rio_readlineb_w (&rio_server, buf, MAXLINE)) == 0) {
				char *err = "proxy couldn't receive msg from server\n";
				printf ("%s", err);	// TODO:
				Rio_writen_w (*connfdp, err, strlen (err));				
				continue;
			}
			else {
				logging (haddrp, client_port, n, buf);	// logging
				Rio_writen_w (*connfdp, buf, strlen (buf));	// serve recieved contents
				Close (clientfd);
			}
		}
		Close (*connfdp);
//	        Pthread_create(&tid, NULL, echo_thread, connfdp);
	}   
	exit(0);
}

/*
 * parse_client: parsing client message into host, port, message.
 * strtok function in string.h is used. If there is any problem, return -1.
 * strtok is locked by semaphore, so this function is thread-safe.
 */
int parse_client (char *buf, char **host, char **port, char **msg) {
        char *input = buf;
        char *split = " \n\t";  // break input by space, tab or \n character.

        /* parse input into 3 strings */
        if ((*host = strtok (input, split)) == NULL) {
		return -1;
	}
    	else if ((*port = strtok (NULL, split)) == NULL) {
		return -1;
	}
	else if ((*msg = strtok (NULL, "")) == NULL) {
		return -1;
	}
	
	return 0;
}

/*
 * logging: log the data what proxy server did.
 * Use struct tm to identify the time, and semafore to make this function thread-safe.
 * Return -1 if it have open file problem. Else, return 0;
 */
void logging (char *IP, int port, size_t size, char *msg) {
	time_t timer;
	char sport[MAXLINE];
	char ssize[MAXLINE];

	/* file descriptor for logging with rio_write */
	int fd = Open ("./proxy.log", O_WRONLY | O_CREAT | O_APPEND, 0644);

	/* i to a */
	sprintf (sport, "%d", port);
	sprintf (ssize, "%d", size);

	/* get tm structure from time function */
	time (&timer);
	char *date = strtok (ctime (&timer), "\n");	// get Date information without \n
	Rio_writen_w (fd, date, strlen (date));
	Rio_writen_w (fd, " KST: ", 6);
	Rio_writen_w (fd, IP, strlen (IP));
	Rio_writen_w (fd, " ", 1);
	Rio_writen_w (fd, sport, strlen (sport));
	Rio_writen_w (fd, " ", 1);
	Rio_writen_w (fd, ssize, strlen (ssize));
	Rio_writen_w (fd, " ", 1);
	Rio_writen_w (fd, msg, strlen (msg));
	
} 



/*
 * open_clientfd_ts: Thread-safe function that opening client file descriptor.
 * Use semaphore to lock-and-copy.
 */
int open_clientfd_ts(char *hostname, int port, sem_t *mutexp) {
	int clientfd;
    	struct hostent *hp;
	struct sockaddr_in serveraddr;

	if ((clientfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        	return -1; /* check errno for cause of error */

	/* Fill in the server's IP address and port */
	P (mutexp);	// semaphore lock
	if ((hp = gethostbyname(hostname)) == NULL) {
	    	V (mutexp);
        	return -2; /* check h_errno for cause of error */
	}
	V (mutexp);
	bzero((char *) &serveraddr, sizeof(serveraddr));
	serveraddr.sin_family = AF_INET;
	bcopy((char *)hp->h_addr_list[0], 
 	       (char *)&serveraddr.sin_addr.s_addr, hp->h_length);
	serveraddr.sin_port = htons(port);

	/* Establish a connection with the server */
	if (connect(clientfd, (SA *) &serveraddr, sizeof(serveraddr)) < 0)
        	return -1; 
	return clientfd;
}

/*
 * Rio_readn_w: Wrapper function for rio_readn.
 * It doesn not terminate process but just display error msg
 * and return 0 when it encouter read failure.
 */
ssize_t Rio_readn_w(int fd, void *ptr, size_t nbytes) {
	size_t n = rio_readn (fd, ptr, nbytes);
	
	if (n < 0) {
		printf ("Rio_readn_w: rio_readn failure\n");
		return 0;
	}
	return n;
}

/*
 * Rio_readlineb_w: Wrapper function for rio_readline_w.
 * Like Rio_readn_w, it only print warning msg and return 0
 * when it encounter read failure.
 */
ssize_t Rio_readlineb_w(rio_t *rp, void *usrbuf, size_t maxlen) {
	size_t n = rio_readlineb (rp, usrbuf, maxlen);

	if (n < 0) {
		printf ("Rio_reandlineb_w: rio_readlineb failure\n");
		return 0;
	}
	return n;
}

/*
 * Rio_writen_w: Wrapper function for rio_writen.
 * It print warning when writen fail, but the return
 * is just void.
 */
void Rio_writen_w(int fd, void *usrbuf, size_t n) {
	size_t wn = rio_writen (fd, usrbuf, n);
	
	if (wn < 0) printf ("Rio_writen_w: rio_writen failure\n");
	return ;
}

