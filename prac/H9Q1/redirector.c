#include <fcntl.h>
#include <unistd.h>

#include <stdio.h>

int main (int argc, char *argv[]) {
	char *fname = argv[2];
	int fd = open (fname, O_WRONLY | O_TRUNC | O_CREAT, S_IRUSR | S_IRGRP | S_IWGRP | S_IWUSR);
//	close (stdout);
//	dup (fd);
//	close (fd);
//	dup2(fd, 0);
	dup2 (fd, stdout);

	close (fd);

	execl (argv[1], argv[1], NULL);

	return 0;
}
