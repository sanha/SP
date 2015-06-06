#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int main(){
	int fd1, fd2;
	char c;

	fd1 = open("foo.txt", O_RDONLY);
	fd2 = open("foo.txt", O_RDONLY);
	read(fd1, &c, 1);
	read(fd2, &c, 1);
	printf ("c = %c\n", c);
	return;

}

