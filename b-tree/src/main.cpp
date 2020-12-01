// Copyright [2020] <Puchkov Kyryll>
#include <iostream>
#include <vector>

// template <class T = int>
struct unit {
    int value;
    bool deleted;

    unit(): value(-1), deleted(false) {}
    explicit unit(int _value): value(_value) {
        deleted = false;
    }
    // unit(int _value, bool _deleted): value(_value), deleted(_deleted) {}
    unit(const unit& other) {
        value = other.value;
        deleted = other.deleted;
    }

    unit& operator=(const unit& other) {
        value = other.value;
        deleted = other.deleted;
        return *this;
    }

    ~unit() {}
};

struct Node {
    // Параметр дерева
    size_t t;
    // Ключи в узле
    std::vector<unit> keys;
    int n_keys = keys.size();
    size_t max_keys/* = 2*t - 1*/;
    size_t min_keys/* = t - 1*/;

    std::vector<Node*> children;

    bool is_leaf;
    bool is_root;

    /*// непонятное присваивание
    Node(size_t parameter, std::vector<unit> units, bool _leaf, bool _root):
        t(parameter), keys(units), leaf(_leaf), root(_root) {
        if (_root == false) {
            max_keys = 2*t - 1;
            min_keys = t - 1;
        } else {
            max_keys = t - 1;
            min_keys = 1;
        }

        n_keys = units.size();

        if (_leaf == false) {
            for (int i = 0; i < n_keys + 1; ++i) {
                children.push_back(nullptr);
            }
        }
    }*/

    // Конструкторы
    // Создание пустого узла
    explicit Node(size_t parameter): t(parameter) {
        unit Key;
        keys.push_back(Key);
    }

    // Создание узла по значению
    Node(size_t parameter, int key, bool _root, bool _leaf):
        t(parameter), is_root(_root), is_leaf(_leaf) {
        unit Key(key);
        keys.push_back(Key);

        if (is_root == true) {
            max_keys = t - 1;
            min_keys = 1;
        } else {
            max_keys = 2*t - 1;
            min_keys = t - 1;
        }
    }

    // Деструктор
    ~Node() {}

    /*Node& operator=(const Node& other) {
        t = other.t;
        keys = other.keys;
        n_keys = other.n_keys;
        max_keys = other.max_keys;
        min_keys = other.min_keys;
        children = other.children;
        is_leaf = other.is_leaf;
        is_root = other.is_root;
        return *this;
    }

    //--------------------------------------

    int Node::find(int key) {
        bool found = false;
        while (found == false) {

        }
    }*/

    void add(int key) {
        if (n_keys <= max_keys) {
            unit Key(key);
            keys.push_back(Key);
        }
    }

    int search(const int& key, uint16_t* level) {
        // std::cout << "Searching at the level " << *level << std::endl;

        for (const auto& i : this->keys) {
            // Индекс первого превышающего элемента
            // По этому индексу в дочернем векторе ищем элемент
            int index = &i - &(*std::begin(this->keys));
            // std::cout << "Index is " << index << std::endl;
            int _value = i.value;
            bool _leaf = this->is_leaf;

            if (_value == key) {
                // Нашли элемент — вывели его индекс
                return index;
            } else if ((key < _value) && (_leaf == false)) {
                // Спускаемся на уровень ниже
                ++(*level);
                return this->children[index]->search(key, level);
            } else if (_leaf == true) {
                // Спустились в самый низ дерева
                if (key < _value) {
                    // Не нашли нужного элемента в листе
                    return -1;
                } else if (key > _value) {
                    // Искомый элемент больше всех в данном листе
                    if (index == this->n_keys - 1) {
                        return -1;
                    }
                    // Иначе ищем дальше
                }
            }
        }
    }

    void print() {
        for (auto i : keys) {
            std::cout << i.value << " ";
        }
        std::cout << std::endl;

        for (auto i : children) {
            i->print();
            std::cout << "\t | \t";
        }
    }
};

struct Btree {
    size_t t;
    Node* root;

    // Конструкторы
    // Явный конструктор по параметру дерева
    explicit Btree(size_t parameter) {
        root = new Node(parameter);
        root->max_keys = parameter - 1;
        root->min_keys = 1;
        root->is_root = true;
        root->is_leaf = true;
    }

    // Конструктор по первому значения и параметру дерева
    Btree(size_t parameter, int key) {
        root = new Node(parameter, key, true, true);

        std::cout << "B-tree with parameter " << parameter << " and first key " << key
            << " succesfully made." << std::endl;
    }

    // Деструктор
    ~Btree() {
        delete(root);
    }

    //--------------------------------------

    void add(int key) {
        root->add(key);
    }

    void find(const int& key) {
        std::cout << "Searching for the key: " << key << " in the B-tree" << std::endl;

        uint16_t level = 0;

        int index = root->search(key, &level);
        if (index == -1) {
            std::cout << "Couldn't find key " << key << std::endl;
        } else {
            std::cout << "Found at level " << level << " by index " << index << std::endl;
        }
    }

    void print() {
        // TODO(puchkovki): implement function print
        root->print();
    }
};

int main(void) {
    size_t t = 3;
    Btree tree(t, 10);

    tree.find(10);
    tree.find(1);
    tree.print();

    tree.add(3);
    tree.print();

    return EXIT_SUCCESS;
}