// Copyright [2020] <Puchkov Kyryll>
#ifndef  B_TREE_INCLUDE_B_TREE_HPP_
#define  B_TREE_INCLUDE_B_TREE_HPP_

#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
#include <utility>

struct Node;

// Ключ — элемент узла
struct Key {
    // Значение ключа
    int64_t value;
    // Указатель на ребенка с большими либо равными элементами
    Node* child;
    // Маркер удаления
    bool deleted;

    // Явный конструктор
    explicit Key(int64_t, Node*, bool);
    // Деструктор
    ~Key();
};


// Конструктор ключа по значению
Key::Key(int64_t _value = -1, Node* _child = nullptr, bool _deleted = false)
    : value(_value), child(_child), deleted(_deleted) {}

// Деструктор ключа
Key::~Key() {}

//--------------------------------------

// Узел B-дерева
struct Node {
    // Параметр дерева
    size_t t;
    /* Вектор ключей
     * < -1, child_1> | <value_1, child_2> | ... | <value_n, child_{n+1}>
     *               Структура дерева:
     *   -1 | value_1 |  ...  |  value_n
     *       /       \           /       \
     *   child_1  child_2...child_{n}  child_{n+1}
     *                   ...
     */
    std::vector<Key> keys;
    // Максимальное количество ключей в узле
    size_t max_keys;
    // Указатель на родительский узел
    Node* parent;

    // Явный конструктор по значению ключа
    explicit Node(size_t, int64_t, Node*);
    // Конструктор по объекту Ключ
    Node(size_t, Key, Node*);
    // Деструктор
    ~Node();

    /* Рекурсивное добавление ключа в узел с балансировкой и "подъемом" наверх
     * Возвращаемое значение: указатель на новый корень, если он поменялся
     */
    Node* add_up(const Key&);
    /* Рекурсивное добавление ключа к листу
     * Возвращаемое значение: указатель на новый корень, если он поменялся
     */
    Node* add_down(const Key&);
    // Поиск индекса последнего меньшего ключа методом двоичного поиска
    int32_t find_index(int64_t);
    // Вставка ключа в узел по индексу
    void insert(const Key&);
    /* Поиск ключа по значению
     * Возвращает пару из индекса и указателя на узел:
     * в данном узле по индексу расположен искомый ключ
     */
    std::pair<int16_t, Node*> search(const int64_t&);
    // Печать узла
    void print();
    // Вставка маркера удаление
    void delete_key(const int64_t&);
    // Освобождение динамической памяти в узле и его потомках
    void destroy();
    // Печать узла для отрисовки с помощью graphviz
    void print_gv();
};

// Конструктор узла по значению ключа
Node::Node(size_t parameter, int64_t value = -1, Node* _parent = nullptr):
        t(parameter), parent(_parent) {
    // Создание и добавление "нулевого" фиктивного ключа
    Key auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Добавление первого "реального" ключа в случае необходимости
    if (value != -1) {
        Key unit(value);
        keys.push_back(unit);
    }

    /* В классической реализации в случае, если
     * данный узел не корень, max_keys = 2*t - 1
     */
    max_keys = t - 1;
}

// Конструктор узла по ключу
Node::Node(size_t parameter, Key unit, Node* _parent): t(parameter),
        parent(_parent) {
    // Создание и добавление "нулевого" фиктивного ключа
    Key auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Добавление первого "реального" ключа
    keys.push_back(unit);


    /* В классической реализации в случае, если
     * данный узел не корень, max_keys = 2*t - 1
     */
    max_keys = t - 1;
}

// Деструктор узла
Node::~Node() {}

/* Рекурсивное добавление ключа к листу
 * Возвращаемое значение: указатель на новый корень, если он поменялся
 */
Node* Node::add_down(const Key& unit) {
    // Спускаемся до уровня листов
    if (this->keys[0].child != nullptr) {
        // Находим индекс последнего меньшего ключа
        int32_t index = this->find_index(unit.value);
        // Спускаемся в дочерний узел
        if ((uint)index < (this->keys.size() - 1)) {
            return this->keys[index].child->add_down(unit);
        } else {
            return this->keys[this->keys.size() - 1].child->add_down(unit);
        }
    } else {
        // Рекурсивное добавление ключа в узел с балансировкой
        return this->add_up(unit);
    }
}

// Поиск индекса последнего меньшего ключа методом двоичного поиска
int32_t Node::find_index(int64_t value) {
    // Дихотомия (двоичный поиск) по узлу
    int32_t middle = -1;
    int32_t left = 0, right = (int32_t)this->keys.size() - 1;

    while (left <= right) {
        middle = (left + right) / 2;
        if (value <= this->keys[middle].value) {
            if (value > this->keys[middle - 1].value) {
                // Возвращаем индекс меньшего элемента
                return --middle;
            } else {
                right = --middle;
            }
        } else {
            left = ++middle;
        }
    }

    /* Не вышли из функции лишь в случае:
     * - когда наш элемент больше всех,
     * тогда middle = this->keys.size() - 1
     * - когда наш элемент меньше всех,
     * но такое невозможно, т.к. нулевой элемент
     * каждого узла "-1", а мы добавляем дишь положительные числа
     */

    return middle;
}

/* Рекурсивное добавление ключа в узел с балансировкой и "подъемом" наверх
 * Возвращаемое значение: указатель на новый корень, если он поменялся
 */
Node* Node::add_up(const Key& unit) {
    // Изначально добавляем элемент
    this->insert(unit);
    if (this->keys.size() - 1 <= this->max_keys) {
        // Не произошло переполнения
        return nullptr;
    } else {
        // Индекс, по которому делим узел
        size_t div_index = this->keys.size() / 2;
        if (unit.value >= this->keys[div_index + 1].value) {
            // Добавляемый член пойдет направо
            if ((div_index < 2)) {
                // В левом узле не останется элементов
                ++div_index;
            }
        } else if (unit.value < this->keys[div_index - 1].value) {
            // Добавляемый член пойдет налево
            if (this->keys.size() - div_index - 1 < 1) {
                // В правом узле не останется элементов
                --div_index;
            }
        }
        // Элемент, который добавляем к родительскому узле
        Key up = this->keys[div_index];

        // Новый узел с фиктивной вершиной вначале
        Node* new_node = new Node(this->t);
        /* Фиктивная вершина указывает на дочерний узел поднятого ключа,
         * т.к. элемент после опорного больше их всех
         */
        new_node->keys[0].child = up.child;
        // Добавляем элементы в новый узел
        for (size_t i = div_index + 1; i < keys.size(); ++i) {
            new_node->keys.push_back(this->keys[i]);
        }
        // Удаляем элементы из узла
        this->keys.erase(this->keys.begin() + div_index, this->keys.end());
        /* Узел `up` ссылается на новый узел с ключами
        * больше либо равными `up.value`
        */
        up.child = new_node;
        // Обновляем предков дочерних узлов
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
            return this->parent->add_up(up);
        }
    }
}

// Вставка ключа в узел по индексу
void Node::insert(const Key& unit) {
    int32_t index = this->find_index(unit.value);
    if ((uint)index < (this->keys.size() - 1)) {
        // Вставляем перед большим элементом либо в конец
        this->keys.emplace(this->keys.begin() + index + 1, unit);
    } else {
        this->keys.push_back(unit);
    }
}

// Освобождение динамической памяти в узле и его потомках
void Node::destroy() {
    for (auto i : this->keys) {
        if (i.child != nullptr) {
            i.child->destroy();
        }
        delete(i.child);
    }
}

// Вставка маркера удаление
void Node::delete_key(const int64_t& value) {
    std::pair<uint16_t, Node*> found = this->search(value);
    if (found.second != nullptr) {
        found.second->keys[found.first].deleted = true;
    } else {
        std::cout << "Couldn't delete value " << value
            << " because it's missing in the B-tree" << std::endl;
    }
}

/* Поиск ключа по значению
 * Возвращает пару из индекса и указателя на узел:
 * в данном узле по индексу расположен искомый ключ
 */
std::pair<int16_t, Node*> Node::search(const int64_t& value) {
    for (const auto& i : this->keys) {
        // Индекс текущего элемента вектора
        uint16_t index = (uint16_t) (&i - &(*std::begin(this->keys)));

        int64_t _value = i.value;
        bool is_leaf = this->keys[0].child == nullptr ? true : false;

        if (_value == value) {
            // Нашли совпадение -> передаем индекс и указатель на узел
            return std::make_pair(index, this);
        } else if (is_leaf == false) {
            // Спускаемся на уровень ниже
            if (value < _value) {
                // Спускаемся в дочерний узел меньшего эл-та
                return this->keys[index - 1].child->search(value);
            } else {
                // if (value > _value)
                // Продолжаем поиски большего эл-та
                if (index == keys.size() - 1) {
                    // Эл-т больше всех —> спускаемся в дочерний узел последнего
                    return this->keys[index].child->search(value);
                }
            }
        } else if (is_leaf == true) {
            // Спустились на уровень листов
            if (value < _value) {
                // Не нашли нужного элемента в листе
                return std::make_pair(-1, nullptr);
            } else if (value > _value) {
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

// Печать узла для отрисовки с помощью graphviz
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

    // Явный конструктор по параметру дерева и первому значению ключа
    explicit Btree(size_t, int64_t);
    // Деструктор
    ~Btree();

    /* Добавление элемента к корню, рекурсивно спускаясь в лист
     * В случае появления нового корня производится замена корня
     */
    void add(int64_t);
    // Поиск и печать узла, в котором расположен ключ и его индекса
    void find(const int64_t&);
    // Рекурсивная печать дерева, начиная с корня
    void print();
    // Рекурсивная печать дерева для отрисовки с помощью graphviz
    void print_gv();
    // Удаление ключа путем рекурсивного спуска
    void delete_key(const int64_t&);
    // Определение оператора указателя
    Btree* operator*();
};

// Конструктор дерева по параметру дерева и первому значению ключа
Btree::Btree(size_t parameter, int64_t value) {
    // Дерево создается с первого ключа
    root = new Node(parameter, value, nullptr);
}

// Деструктор дерева
Btree::~Btree() {
    // Рекурсивное удаление узлов, начиная с корня
    root->destroy();
    delete(root);
}

// Определение оператора указателя
Btree* Btree::operator*() {
    return this;
}

/* Добавление элемента к корню, рекурсивно спускаясь в лист
 * В случае появления нового корня производится замена корня
 */
void Btree::add(int64_t value) {
    Key unit(value);
    Node* new_root = root->add_down(unit);
    if (new_root != nullptr) {
        // Появился новый корень
        this->root = new_root;
    }
}

// Поиск и печать узла, в котором расположен ключ и его индекса
void Btree::find(const int64_t& value) {
    std::pair<int16_t, Node*> found = root->search(value);
    if (found.first == -1) {
        std::cout << "Couldn't find value " << value << std::endl;
    } else {
        std::cout << "Found in the node:";
        for (auto i : found.second->keys) {
            std::cout << i.value << " ";
        }
        std::cout << ", by index " << found.first << std::endl;
    }
}

// Удаление ключа путем рекурсивного спуска
void Btree::delete_key(const int64_t& value) {
    root->delete_key(value);
}

// Рекурсивная печать дерева, начиная с корня
void Btree::print() {
    std::cout << "Current tree structure is:" << std::endl;
    root->print();
    std::cout <<std::endl;
}

// Рекурсивная печать дерева для отрисовки с помощью graphviz
void Btree::print_gv() {
    std::cout << "digraph Tree {" << std::endl;
    root->print_gv();
    std::cout << "}"<< std::endl;
}

#endif  // B_TREE_INCLUDE_B_TREE_HPP_
