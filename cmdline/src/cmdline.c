// Copyright [2020] <Puchkov Kyryll>
#include <sys/prctl.h>
#include <errno.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int update_argv() {
    size_t _size = 10;
    char *ptr = (char*) calloc(1 + _size, sizeof(char));

    if (prctl(PR_SET_MM, PR_SET_MM_ARG_START, ptr, 0, 0) < 0) {
        fprintf(stderr, "PR_SET_MM_ARG_START failed: %s\n", strerror(errno));
        free(ptr);
        return -1;
    } else {
        if (prctl(PR_SET_MM, PR_SET_MM_ARG_END, ptr + _size, 0, 0) < 0) {
            fprintf(stderr, "PR_SET_MM_ARG_END failed: %s\n", strerror(errno));
            free(ptr);
            return -1;
        }
    }
    free(ptr);
    return 1;
}

int main(int argc, char *argv[]) {
    // show pid to find the right process
    pid_t pid = getpid();
    printf("pid = %d\n", pid);

    if (argv[1] != NULL) {
        if (update_argv() == 1) {
            sleep(1000);
        } else {
            return EXIT_FAILURE;
        }
    }

    return 0;
}
