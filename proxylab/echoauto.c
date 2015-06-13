/*
 * echoauto.c - An echo client
 */
/* $begin echoclientmain */
#include "csapp.h"

int main(int argc, char **argv) 
{
    int clientfd, port;
    char *host, buf[MAXLINE];
    char *anum, *destport;
    rio_t rio;

    if (argc != 5) {
	fprintf(stderr, "usage: %s <host> <port> <destport> <autonum>\n", argv[0]);
	exit(0);
    }
    host = argv[1];
    port = atoi(argv[2]);
    anum = argv[4];
    destport = argv[3];

    char tmphost[MAXLINE];
    strcpy (tmphost, host);

    clientfd = Open_clientfd(host, port);
    Rio_readinitb(&rio, clientfd);
    
    	unsigned int count = 0;

    //printf("type:"); fflush(stdout);
    for (count = 0; count < 50000; count ++) {
	strcpy (tmphost, host);
	sprintf (buf, " %s Auto num: %s Conunt %d\n", destport, anum, count);
	strcat (tmphost, buf);
	
	Rio_writen(clientfd, tmphost, strlen(tmphost));
	Rio_readlineb(&rio, buf, MAXLINE);
	printf("echo:");
	Fputs(buf, stdout);
	fflush(stdout);
    }
    Close(clientfd);
    exit(0);
}
/* $end echoclientmain */
