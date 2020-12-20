// Copyright [2020] <Puchkov Kyryll>
#include <ctime>
#include <b-tree.hpp>

int main(void) {
    size_t t = 3;
    srand((uint)time(0));
    int key = rand() % 1000;
    Btree tree(t, key);

    for (int i = 2; i < 25; ++i) {
        key = rand() % 1000;
        tree.add(key);
        if (i % 10 == 0) {
            tree.delete_key(key);
        }
    }

    std::ofstream paint("res/b-tree.gv");
    if (paint.is_open() == 1) {
        tree.print_gv(paint);
    } else {
        std::cout << "Cannot open file res/test.gv for writing!";
    }
    paint.close();

    return EXIT_SUCCESS;
}
