// Copyright [2020] <Puchkov Kyryll>
#ifndef  B_TREE_INCLUDE_B_TREE_HPP_
#define  B_TREE_INCLUDE_B_TREE_HPP_

#include <unistd.h>
#include <iostream>
#include <vector>
#include <algorithm>
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
    bool is_root;
    bool is_leaf;
    Node* parent;

    // Конструктор по значению ключа
    explicit Node(size_t, int64_t, bool, Node*);
    // Конструктор по значению "ячейки"
    Node(size_t, Unit, bool, Node*);
    // Деструктор
    ~Node();

    // Добавление в ключа в узел
    Node* add_up(const Unit&);
    Node* add_down(const Unit&);
    int32_t find_index(int64_t);
    void insert(const Unit&);
    int search(const int64_t&, uint16_t*);
    std::pair<uint16_t, Node*> search(const int64_t&);
    // Печать узла
    void print();
    // Поиск узла и вставка маркера удаление
    void delete_key(const int64_t&);
    // Рекурсивно двигаясь по узлам освобождаем динамическую память
    void destroy();
};

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
    // Удаляет ключ путем рекурсивного спуска и поиска
    void delete_key(const int64_t&);
};

#endif  // B_TREE_INCLUDE_B_TREE_HPP_
