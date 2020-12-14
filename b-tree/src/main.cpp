// Copyright [2020] <Puchkov Kyryll>
#include <b-tree.hpp>
#include <ctime>

int main(void) {
    size_t t = 3;
    srand((uint)time(0));
    int key = rand() % 1000;
    Btree tree(t, key);

    for (int i = 2; i < 25; ++i) {
        key = rand() % 1000;
        tree.add(key);
    }
    tree.print_gv();

    return EXIT_SUCCESS;
}
