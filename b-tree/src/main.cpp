// Copyright [2020] <Puchkov Kyryll>
#include <b-tree.hpp>

// Явный конструктор
Unit::Unit(int64_t _value = -1, Node* _child = nullptr, bool _deleted = false)
    : value(_value), child(_child), deleted(_deleted) {
}

Unit::~Unit() {}

//--------------------------------------

// Конструктор узла
Node::Node(size_t parameter = 2, int64_t key = -1, bool _root = true,
    bool _leaf = true, Node* _parent = nullptr)
    : t(parameter), is_root(_root), is_leaf(_leaf), parent(_parent) {
    // Изначально добавляем фиктивный ключ
    Unit auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Добавляем первый "реальный" ключ
    if (key != -1) {
        Unit Key(key);
        keys.push_back(Key);
    }

    if (is_root == true) {
        max_keys = t - 1;
        min_keys = 1;
    } else {
        max_keys = 2 * t - 1;
        min_keys = t - 1;
    }
}

Node::Node(size_t parameter, Unit Key, bool _root, bool _leaf, Node* _parent):
        t(parameter), is_root(_root), is_leaf(_leaf), parent(_parent) {
    // Изначально добавляем фиктивный ключ
    Unit auxiliary_key;
    this->keys.push_back(auxiliary_key);

    // Теперь добавляем первый "реальный" ключ
    keys.push_back(Key);

    if (is_root == true) {
        max_keys = t - 1;
        min_keys = 1;
    } else {
        max_keys = 2*t - 1;
        min_keys = t - 1;
    }
}

Node::~Node() {}

// Добавление в ключа в узел
Node* Node::add(const Unit& Key) {
    // Знак <=, т.к. используем одну фиктивную вершину
    if (this->keys.size() <= this->max_keys) {
        // auto it = keys.emplace
        this->keys.push_back(Key);

        // TODO(puchkovki): изменить сортировку на вставку в нужную позицию
        // Для соблюдения упорядоченности сортируем
        std::sort(this->keys.begin(), this->keys.end(), this->cmp);
        return nullptr;
    } else {
        /* Индекс, по которому делим старый узел — n / 2,
         * где n — количество вершин с фиктивной
         * n = 2k -> index = k
         * n = 2k + 1 -> index = k + 1
         */
        size_t div_index = this->keys.size() / 2;
        // Элемент, который поднимем наверх
        Unit up = this->keys[div_index];

        // Новый узел с фиктивной вершиной вначале
        Node* new_node = new Node();
        new_node->is_root = false;
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

        // Данный узел не корень
        if (this->parent != nullptr) {
            // Родительский узел общий с "делимым узлом"
            new_node->parent = this->parent;
            // Добавляем элемент к родительскому узлу
            this->parent->add(up);
            if (up.value <= Key.value) {
                new_node->add(Key);
            } else {
                this->add(Key);
            }
            return nullptr;
        } else {
            Node* root = new Node(this->t, up, true, false, nullptr);
            // Самый левый ребенок теперь должен указывать на предыдущую вершину
            root->keys[0].child = this;

            // Привязываем новых детей к корню
            this->parent = root;
            new_node->parent = root;

            if (up.value <= Key.value) {
                new_node->add(Key);
            } else {
                this->add(Key);
            }
            return root;
        }
    }
}

// Компаратор для сортировки вектора
bool Node::cmp(const Unit& a, const Unit& b) {
    return a.value < b.value;
}

int Node::search(const int64_t& key, uint16_t* level) {
    for (const auto& i : keys) {
        // Индекс первого превышающего элемента
        // По этому индексу в дочернем векторе ищем элемент
        uint16_t index = (uint16_t) (&i - &(*std::begin(keys)));
        int64_t _value = i.value;
        bool _leaf = is_leaf;

        if (_value == key) {
            // Нашли элемент — вывели его индекс
            return index;
        } else if (_leaf == false) {
            // Спускаемся на уровень ниже
            ++(*level);
            if (key < _value) {
                return keys[index - 1].child->search(key, level);
            } else {
                // if (key > value)
                if (index == keys.size() - 1) {
                    return keys[index].child->search(key, level);
                }
            }
        } else if (_leaf == true) {
            // Спустились в самый низ дерева
            if (key < _value) {
                // Не нашли нужного элемента в листе
                return -1;
            } else if (key > _value) {
                // Искомый элемент больше всех в данном листе
                if (index == keys.size() - 1) {
                    return -1;
                }
                // Иначе ищем дальше
            }
        }
    }
    // Что-то пошло не так
    return -1;
}

std::pair<uint16_t, Node*> Node::search(const int64_t& key) {
    for (const auto& i : this->keys) {
        // Индекс элемента
        // По этому индексу в дочернем векторе ищем элемент
        uint16_t index = (uint16_t) (&i - &(*std::begin(this->keys)));

        int64_t _value = i.value;
        bool _leaf = is_leaf;

        if (_value == key) {
            // Передаем индекс ключа в узле и указатель на узел
            return std::make_pair(index, this);
        } else if (_leaf == false) {
            // Спускаемся на уровень ниже
            if (key < _value) {
                return this->keys[index - 1].child->search(key);
            } else {
                // if (key > value)
                if (index == keys.size() - 1) {
                    return this->keys[index].child->search(key);
                }
            }
        } else if (_leaf == true) {
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
    // Что-то пошло не так
    return std::make_pair(-1, nullptr);
}

// Печать узла
void Node::print() {
    for (const auto& i : this->keys) {
        // Ключ не был удален
        if (i.deleted == false) {
            std::cout << i.value << " ";
        }
    }

    // Если узел — не лист, значит спускаемся вниз
    if (is_leaf == false) {
        std::cout << std::endl << "  |\t\t\t \\" << std::endl;
        for (const auto& i : this->keys) {
            i.child->print();
            uint16_t index = (uint16_t) (&i - &(*std::begin(this->keys)));
            if (index < this->keys.size() - 1) {
                std::cout << "\t | \t";
            }
        }
    }
}

// Поиск узла и вставка маркера удаление
void Node::delete_key(const int64_t& key) {
    std::pair<uint16_t, Node*> found = this->search(key);
    found.second->keys[found.first].deleted = true;
}

// Рекурсивное удаление узла
void Node::destroy() {
    for (const auto& i : this->keys) {
        if (i.child->keys[0].child != nullptr) {
            /* Если ребенок данного узла не лист
             * Рекурсивно запускаем удаление от ребенка
             */
            i.child->destroy();
        } else {
            // Внуков не существует -> пора удалять детей
            for (auto& j : i.child->keys) {
                delete(j.child);
            }
            // После уборки ребенка убираем "ключ", на него ссылающийся
            delete(i.child);
            return;
        }
    }
}

//--------------------------------------
// Конструктор
Btree::Btree(size_t parameter, int64_t key = -1) {
    /* Дерево создается с первого ключа
     * узел, соответственно, и корень, и лист
     */
    root = new Node(parameter, key, true, true);
    std::cout << "B-tree with parameter " << parameter << " and first key "
        << key << " succesfully made." << std::endl;
}

// Деструктор
Btree::~Btree() {
    root->destroy();
}

/* Добавляет элемент от корня, рукурсивно спускаясь нижу в поисках
 * подходящего места
 * В случае появления нового корня производит замену
 */
void Btree::add(int64_t key) {
    std::cout << "Adding " << key << std::endl;
    Unit Key(key);
    Node* new_root = root->add(Key);
    if (new_root != nullptr) {
        this->root = new_root;
    }
}

// Ищет уровень, на котором расположен ключ и его индекс в узле
void Btree::find(const int64_t& key) {
    std::cout << "Searching for the key: " << key << " in the B-tree"
        << std::endl;
    uint16_t level = 0;

    int index = root->search(key, &level);
    if (index == -1) {
        std::cout << "Couldn't find key " << key << std::endl;
    } else {
        std::cout << "Found at level " << level << " by index " << index
            << std::endl;
    }
}

// Печатает дерево путем рекурсивного спуска
void Btree::print() {
    std::cout << "Current tree structure is:" << std::endl;
    root->print();
    std::cout << std::endl;
}

// Удаляет ключ путем рекурсивного спуска и поиска
void Btree::delete_key(const int64_t& key) {
    std::cout << "Deleting element " << key << std::endl;
    root->delete_key(key);
}

//--------------------------------------

int main(void) {
    size_t t = 3;
    Btree tree(t, 10);

    tree.find(10);
    tree.find(11);
    tree.print();

    std::cout << std::endl;

    tree.add(11);
    tree.add(5);
    tree.find(11);
    tree.print();
    tree.delete_key(11);
    tree.print();

    return EXIT_SUCCESS;
}
