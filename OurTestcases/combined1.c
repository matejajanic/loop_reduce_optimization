#include <stdio.h>

#define MAX (100)

int main() {
    int niz[MAX];
    int x = 1, n = 5;
    int a = 3, b = 2;

    for (int i = 0; i < n; i++) {
       niz[a * i] = 4;
    }

    return 0;
}