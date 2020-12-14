// Copyright [2020] <Puchkov Kyryll>
#include <b-tree.hpp>

Btree* make_tree(const size_t& t, const size_t& key) {
    Btree *tree = new Btree(t, key);
    std::cout << "B-tree with parameter " << t << " and first key "
        << key << " succesfully made." << std::endl << std::endl;
    return tree;
}

void add(const int& i, Btree* tree) {
    std::cout << "Adding " << i << std::endl;
    tree->add(i);
}

void search(Btree *tree, const int& key) {
    std::cout << "Searching for the key: " << key << " in the B-tree"
        << std::endl;
    tree->find(key);
    std::cout << std::endl;
}

void delete_key(Btree* tree, const int& key) {
    std::cout << "Deleting element " << key << std::endl;
    tree->delete_key(key);
    std::cout << std::endl;
}

void test_tree() {
    size_t t = 3;
    srand((uint)(time(0)));
    int key = rand() % 1000;
    Btree *tree = make_tree(t, key);

    for (int i = 2; i < 20; ++i) {
        key = rand() % 1000;
        add(key, tree);
        tree->print();
    }
    delete(tree);
}

int main(void) {
    test_tree();
    /* Подробное тестирование 
    size_t t = 3;
    int key = 1;
    Btree *tree = make_tree(t, key);

    for (int i = 2; i < 10; ++i) {
        add(i, tree);
        tree->print();
    }

    key = 5;
    search(tree, key);
    key = 11;
    search(tree, key);

    key = 6;
    delete_key(tree, key);
    key = 11;
    delete_key(tree, key);

    tree->print();

    delete(tree); */
    return EXIT_SUCCESS;
}
