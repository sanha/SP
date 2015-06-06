#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int main(){
	int fd;
	char c;

	fd = open("foo.txt", O_RDONLY);
	if (fork() == 0) {
		read (fd, &c, 1);
		exit (0);
	}
	wait (NULL);
	read (fd, &c, 1);
	printf ("c = %c\n", c);
	return;

}

