#include <stdio.h>

int main() {
    int x = 1, n = 5;
    int a = 3, b = 2;

    for (int i = 0; i < n; i++) {
       x = a * i + b;
    }

    return 0;
}