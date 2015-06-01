/* echo client */
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/socket.h>

#define SIZE 100

int main (int argc, char **argv) {
	int sock;
	char msg[SIZE];
	struct sockaddr_in server_addr;

	sock = socket (PF_INET, SOCK_STREAM, 0);
	if (sock < 0) {
		printf ("socket construction failed\n");
		exit(1);
	}

	server_addr.sin_family = AF_INET;
	server_addr.sin_port = htons(8123);
	server_addr.sin_addr.s_addr = inet_addr ("127.0.0.1");

	if (connect (sock, (struct sockaddr*)&server_addr, sizeof(server_addr)) < 0) {
	    	printf ("connection failed\n");
		exit (1);
	}

	printf ("Connected to server. If you want to get out, just type quit\n");

	while (1) {
		printf ("Please write your message: ");
		gets (msg);

		if (strcmp (msg, "quit") == 0) break;
		if (send (sock, msg, strlen(msg), 0) < 0) {
			puts ("sending failed\n");
			exit (1);
		}
		if (recv (sock, msg, SIZE-1, 0) < 0) {
			puts ("recieving failed\n");
			exit (1);
		}

		printf ("Reply: %s\n", msg);
	}

	close (sock);
	return 0;
}
