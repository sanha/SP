#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/socket.h>

#define SIZE 100 

int main(int argc, char **argv) {
        int server_sock;                                
        int clnt_sock;                                  
        int len;                                        
        int addr_size;                                  
        char msg[SIZE];                                 
        struct sockaddr_in server_addr;                 
        struct sockaddr_in clnt_addr;                   


        server_sock = socket(PF_INET, SOCK_STREAM, 0);     
        if(server_sock < 0) {
                printf("constructing socket failed\n");    
                exit(1);
        }

        server_addr.sin_family  = AF_INET;                 
        server_addr.sin_port = htons(8123);       
	server_addr.sin_addr.s_addr = INADDR_ANY;   
    
        if (bind (server_sock, (struct sockaddr*)&server_addr, sizeof(server_addr)) < 0) {
                printf("binding failed!\n");
                exit(1);
        }
    
        if(listen(server_sock, 5) < 0) {
                printf("listening failed\n");
                exit(1);
        }

	addr_size = sizeof (clnt_addr);
	clnt_sock = accept (server_sock, (struct sockaddr* )&clnt_addr, &addr_size);
	if (clnt_sock < 0) {
		printf ("acception failed\n");
		exit (1);
	}

	while ((len = recv (clnt_sock, msg, SIZE, 0)) > 0) {
		if (send (clnt_sock, msg, len, 0) < 0) {
			puts ("sending to client failed \n");
			exit (1);
		}
		write (1, msg, len);
		printf ("\n");
	}

	close (clnt_sock);

	return 0;
}
