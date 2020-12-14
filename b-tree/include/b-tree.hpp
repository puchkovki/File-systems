// Copyright [2020] <Puchkov Kyryll>
#ifndef  B_TREE_INCLUDE_B_TREE_HPP_
#define  B_TREE_INCLUDE_B_TREE_HPP_

#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
#include <utility>

struct Node;

struct Unit {
    // Пара — ключ, указатель на ребенка,
    // в котором будут храниться значения больше данного
    // TODO(puchkovki): заменить вектор пар на две простые переменные
    int64_t value;
    Node* child;
    // Маркер удаления
    bool deleted;

    // Явный конструктор
    explicit Unit(int64_t, Node*, bool);
    // Деструктор
    ~Unit();
};


// Явный конструктор
Unit::Unit(int64_t _value = -1, Node* _child = nullptr, bool _deleted = false)
    : value(_value), child(_child), deleted(_deleted) {}

Unit::~Unit() {}

//--------------------------------------

struct Node {
    // Параметр дерева
    size_t t;
    // Пары <ключ, указатель на ребенка "побольше"> в узле
    /* < -1, child_1> | <value_1, child_2> | ... | <value_n, child_{n+1}>
    *               Структура узла:
    *   -1 | value_1  |  ...  |  value_n
    *       /       \           /       \
    *   child_1  child_2...child_{n}  child_{n+1}
    */
    std::vector<Unit> keys;
    size_t max_keys;
    size_t min_keys;
    Node* parent;

    // Конструктор по значению ключа
    explicit Node(size_t, int64_t, Node*);
    // Конструктор по значению "ячейки"
    Node(size_t, Unit, Node*);
    // Деструктор
    ~Node();

    // Добавление в ключа в узел
    Node* add_up(const Unit&);
    Node* add_down(const Unit&);
    int32_t find_index(int64_t);
    void insert(const Unit&);
    std::pair<int16_t, Node*> search(const int64_t&);
    // Печать узла
    void print();
    // Поиск узла и вставка маркера удаление
    void delete_key(const int64_t&);
    // Рекурсивно двигаясь по узлам освобождаем динамическую память
    void destroy();
    void print_gv();
};

// Конструктор узла
Node::Node(size_t parameter, int64_t key = -1, Node* _parent = nullptr):
        t(parameter), parent(_parent) {
    // Изначально добавляем фиктивный ключ
    Unit auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Добавляем первый "реальный" ключ
    if (key != -1) {
        Unit Key(key);
        keys.push_back(Key);
    }

    max_keys = t - 1;
    min_keys = 1;
}

Node::Node(size_t parameter, Unit Key, Node* _parent): t(parameter),
        parent(_parent) {
    // Изначально добавляем фиктивный ключ
    Unit auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Теперь добавляем первый "реальный" ключ
    keys.push_back(Key);

    max_keys = t - 1;
    min_keys = 1;
}

Node::~Node() {}

Node* Node::add_down(const Unit& Key) {
    if (this->keys[0].child != nullptr) {
        // Ищем последний элемент меньший поданного
        int32_t index = this->find_index(Key.value);
        // Спускаемся в его дочерний узел
        if ((uint)index < (this->keys.size() - 1)) {
            return this->keys[index].child->add_down(Key);
        } else {
            return this->keys[this->keys.size() - 1].child->add_down(Key);
        }
    } else {
        return this->add_up(Key);
    }
}

// Поиск индекса последнего элемента меньшего переданного
int32_t Node::find_index(int64_t key) {
    // Дихотомия (двоичный поиск) по узлу
    int32_t middle = -1;
    int32_t left = 0, right = (int32_t)this->keys.size() - 1;
    // std::cout << "left: " << left << " right: " << right << std::endl;
    while (left <= right) {
        middle = (left + right) / 2;
        // std::cout << "middle: " << middle << std::endl;
        if (key <= this->keys[middle].value) {
            if (key > this->keys[middle - 1].value) {
                // Возвращаем индекс меньшего элемента
                return --middle;
            } else {
                right = --middle;
            }
        } else {
            left = ++middle;
        }
    }

    /* Не вышли из функции лишь в случае,
     * - когда наш элемент больше всех
     * тогда middle = this->keys.size() - 1
     * - когда наш элемент меньше всех,
     * но такое невозможно, т.к. нулевой элемент
     * каждого узла "-1", а мы добавляем дишь положительные числа
     */

    return middle;
}

Node* Node::add_up(const Unit& Key) {
    // Изначально добавляем элемент
    this->insert(Key);
    if (this->keys.size() - 1 <= this->max_keys) {
        // Не произошло переполнения
        return nullptr;
    } else {
        // Индекс, по которому делим узел
        size_t div_index = this->keys.size() / 2;
        if (Key.value >= this->keys[div_index + 1].value) {
            // Добавляемый член пойдет налево
            if ((div_index < 2)) {
                ++div_index;
            }
        } else if (Key.value < this->keys[div_index - 1].value) {
            if (this->keys.size() - div_index - 1 < 1) {
                --div_index;
            }
        }
        // Элемент, который поднимем наверх
        Unit up = this->keys[div_index];

        // Новый узел с фиктивной вершиной вначале
        Node* new_node = new Node(this->t);
        new_node->keys[0].child = up.child;
        // Добавляем элементы в новый узел
        for (size_t i = div_index + 1; i < keys.size(); ++i) {
            new_node->keys.push_back(this->keys[i]);
        }
        // Удаляем элементы из узла
        this->keys.erase(this->keys.begin() + div_index, this->keys.end());
        /* Узел `up` ссылается на новый узел с ключами
        * больше либо равными keys[div_index]
        */
        up.child = new_node;
        if (new_node->keys[0].child != nullptr) {
            for (auto i : new_node->keys) {
                i.child->parent = new_node;
            }
        }
        // Проверка, в корне ли мы
        if (this->parent == nullptr) {
            Node* new_root = new Node(this->t, up, nullptr);
            new_root->keys[0].child = this;
            this->parent = new_root;
            new_node->parent = new_root;
            return new_root;
        } else {
            new_node->parent = this->parent;
            /*std::cout << "Recursivly adding to the parent: ";
            for (const auto& i : this->parent->keys) {
                std::cout << i.value << " ";
            }
            std::cout << std::endl;*/
            return this->parent->add_up(up);
        }
    }
}

void Node::insert(const Unit& Key) {
    int32_t index = this->find_index(Key.value);
    if ((uint)index < (this->keys.size() - 1)) {
        // Вставляем перед большим элементом либо в конец
        this->keys.emplace(this->keys.begin() + index + 1, Key);
    } else {
        this->keys.push_back(Key);
    }
}

// Рекурсивное удаление узла
void Node::destroy() {
    for (auto i : this->keys) {
        if (i.child != nullptr) {
            i.child->destroy();
        }
        delete(i.child);
    }
}

// Поиск узла и вставка маркера удаление
void Node::delete_key(const int64_t& key) {
    std::pair<uint16_t, Node*> found = this->search(key);
    if (found.second != nullptr) {
        found.second->keys[found.first].deleted = true;
    } else {
        std::cout << "Couldn't delete key " << key
            << " because it's missing in the B-tree" << std::endl;
    }
}

std::pair<int16_t, Node*> Node::search(const int64_t& key) {
    for (const auto& i : this->keys) {
        // Индекс элемента
        // По этому индексу в дочернем векторе ищем элемент
        uint16_t index = (uint16_t) (&i - &(*std::begin(this->keys)));

        int64_t _value = i.value;
        bool is_leaf = this->keys[0].child == nullptr ? true : false;

        if (_value == key) {
            // Передаем индекс ключа в узле и указатель на узел
            return std::make_pair(index, this);
        } else if (is_leaf == false) {
            // Спускаемся на уровень ниже
            if (key < _value) {
                return this->keys[index - 1].child->search(key);
            } else {
                // if (key > value)
                if (index == keys.size() - 1) {
                    return this->keys[index].child->search(key);
                }
            }
        } else if (is_leaf == true) {
            // Спустились в самый низ дерева
            if (key < _value) {
                // Не нашли нужного элемента в листе
                return std::make_pair(-1, nullptr);
            } else if (key > _value) {
                // Искомый элемент больше всех в данном листе
                if (index == keys.size() - 1) {
                    return std::make_pair(-1, nullptr);
                }
                // Иначе ищем дальше
            }
        }
    }

    assert(false);
}

// Печать узла
void Node::print() {
    for (const auto& i : this->keys) {
        // Ключ не был удален
        if (i.deleted == false) {
            std::cout << i.value << " " << std::flush;
        }
    }

    bool is_leaf = this->keys[0].child == nullptr ? true : false;
    // Если узел — не лист, значит спускаемся вниз
    if (is_leaf == false) {
        std::cout << std::endl << "  |\t\t\t \\" << std::endl << std::flush;
        for (const auto& i : this->keys) {
            std::cout << " " << (&i - &(*std::begin(this->keys)))
                << "'s child of " << i.value << ": ";
            i.child->print();
            if ((uint16_t)(&i - &(*std::begin(this->keys)))
                < (this->keys.size() - 1)) {
                std::cout << "\t | \t" << std::flush;
            }
        }
        std::cout << std::endl;
    }
}

// Печать узла
void Node::print_gv() {
    std::cout << "\"" << this << "\" [label = \"";
    for (const auto& i : this->keys) {
        if (i.value != -1) {
            std::cout << i.value << " ";
        }
        if (((&i - &(*std::begin(this->keys)))
            < (int64_t)(this->keys.size() - 1)) &&
            (&i - &(*std::begin(this->keys))) > 0) {
            std::cout << "| ";
        }
    }
    std::cout << "\"];" << std::endl;
    if (this->keys[0].child != nullptr) {
        for (const auto& i : this->keys) {
            std::cout << "\"" << this << "\" -> \"" << i.child << "\";"
                << std::endl;
        }
    }
    if (this->keys[0].child != nullptr) {
        for (const auto& i : this->keys) {
            i.child->print_gv();
        }
    }
}

//--------------------------------------

struct Btree {
    // Параметр дерева
    size_t t;
    // Корневой узел дерева
    Node* root;

    // Явный конструктор по параметру дерева и первому значения ключа
    explicit Btree(size_t, int64_t);
    // Деструктор
    ~Btree();

    /* Добавляет элемент от корня, рукурсивно спускаясь нижу в поисках
     * подходящего места
     * В случае появления нового корня производит замену
     */
    void add(int64_t);
    // Ищет уровень, на котором расположен ключ и его индекс в узле
    void find(const int64_t&);
    // Печатает дерево путем рекурсивного спуска
    void print();
    void print_gv();
    // Удаляет ключ путем рекурсивного спуска и поиска
    void delete_key(const int64_t&);
    Btree* operator*();
};

// Конструктор
Btree::Btree(size_t parameter, int64_t key) {
    // Дерево создается с первого ключа
    root = new Node(parameter, key, nullptr);
}

// Деструктор
Btree::~Btree() {
    root->destroy();
    delete(root);
}

Btree* Btree::operator*() {
    return this;
}

/* Добавляет элемент от корня, рукурсивно спускаясь нижу в поисках
 * подходящего места
 * В случае появления нового корня производит замену
 */
void Btree::add(int64_t key) {
    Unit Key(key);
    Node* new_root = root->add_down(Key);
    if (new_root != nullptr) {
        this->root = new_root;
    }
}

// Ищет уровень, на котором расположен ключ и его индекс в узле
void Btree::find(const int64_t& key) {
    std::pair<int16_t, Node*> found = root->search(key);
    if (found.first == -1) {
        std::cout << "Couldn't find key " << key << std::endl;
    } else {
        std::cout << "Found in the node:";
        for (auto i : found.second->keys) {
            std::cout << i.value << " ";
        }
        std::cout << ", by index " << found.first << std::endl;
    }
}

// Удаляет ключ путем рекурсивного спуска и поиска
void Btree::delete_key(const int64_t& key) {
    root->delete_key(key);
}

// Печатает дерево путем рекурсивного спуска
void Btree::print() {
    std::cout << "Current tree structure is:" << std::endl;
    root->print();
    std::cout <<std::endl;
}

void Btree::print_gv() {
    std::cout << "digraph Tree {" << std::endl;
    root->print_gv();
    std::cout << "}"<< std::endl;
}

#endif  // B_TREE_INCLUDE_B_TREE_HPP_
