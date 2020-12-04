// Copyright [2020] <Puchkov Kyryll>
#ifndef  B_TREE_INCLUDE_B_TREE_HPP_
#define  B_TREE_INCLUDE_B_TREE_HPP_

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
    explicit Unit(int64_t _value, Node* _child, bool _deleted);
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
    explicit Node(size_t parameter, int64_t key, bool _root,
        bool _leaf, Node* _parent);
    // Конструктор по значению "ячейки"
    Node(size_t parameter, Unit Key, bool _root,
        bool _leaf, Node* _parent);
    // Деструктор
    ~Node();

    // Добавление в ключа в узел
    Node* add(const Unit&);
    // Компаратор для сортировки вектора
    static bool cmp(const Unit& a, const Unit& b);

    int search(const int64_t& key, uint16_t* level);
    std::pair<uint16_t, Node*> search(const int64_t& key);
    // Печать узла
    void print();
    // Поиск узла и вставка маркера удаление
    void delete_key(const int64_t& key);
    // Рекурсивно двигаясь по узлам освобождаем динамическую память
    void destroy();
};

struct Btree {
    // Параметр дерева
    size_t t;
    // Корневой узел дерева
    Node* root;

    // Явный конструктор по параметру дерева и первому значения ключа
    explicit Btree(size_t parameter, int64_t key);
    // Деструктор
    ~Btree();

    /* Добавляет элемент от корня, рукурсивно спускаясь нижу в поисках
     * подходящего места
     * В случае появления нового корня производит замену
     */
    void add(int64_t key);
    // Ищет уровень, на котором расположен ключ и его индекс в узле
    void find(const int64_t& key);
    // Печатает дерево путем рекурсивного спуска
    void print();
    // Удаляет ключ путем рекурсивного спуска и поиска
    void delete_key(const int64_t& key);
};

#endif  // B_TREE_INCLUDE_B_TREE_HPP_
