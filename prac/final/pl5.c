#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int main(){
	int fd1, fd2, fd3;
	char *fname = "foo.txt";
	fd1 = open("foo.txt", O_TRUNC | O_RDWR, S_IRUSR | S_IWUSR);
	write (fd1, "pqrs", 4);
	fd3 = open("foo.txt", O_APPEND | O_WRONLY, 0);
	write (fd3, "jklmn", 5);
	fd2 = dup(fd1);
	write (fd2, "wxyz", 4);
	write (fd3, "ef", 2);
	return 0;
}

