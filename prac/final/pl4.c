#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int main(){
	int fd1;
	int s = getpid() & 0x1;
	char c1, c2;
	char *fname = "foo.txt";
	fd1 = open (fname, O_RDONLY);

	read (fd1, &c1, 1);
	if (fork()) {
		sleep(s);
		read(fd1, &c2, 1);
		printf ("Parent: c1 = %c, c2 = %c\n", c1, c2);
	}
	else {
		sleep (1-s);
		read(fd1, &c2, 1);
		printf ("Child: c1 = %c, c2 = %c\n", c1, c2);
	}
	return 0;
}

