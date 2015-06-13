#include <string.h>
#include <stdio.h>

int main (){
	char string[] = "forum falinux com";
	char *tmp;

	tmp = strtok (string, " ");
	printf ("tmp is %s\n", tmp);
	tmp = strtok (NULL, "");
	printf ("tmp2 is %s\n", tmp);

	return 0;
}
