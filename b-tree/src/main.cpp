// Copyright [2020] <Puchkov Kyryll>
#include <b-tree.hpp>

// Явный конструктор
Unit::Unit(int64_t _value = -1, Node* _child = nullptr, bool _deleted = false)
    : value(_value), child(_child), deleted(_deleted) {
}

Unit::~Unit() {}

//--------------------------------------

// Конструктор узла
Node::Node(size_t parameter, int64_t key = -1, bool _leaf = true,
    Node* _parent = nullptr) : t(parameter), is_leaf(_leaf), parent(_parent) {
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

Node::Node(size_t parameter, Unit Key, bool _leaf, Node* _parent):
        t(parameter), is_leaf(_leaf), parent(_parent) {
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
        // Есть куда спускаться вниз
        int32_t index = this->find_index(Key.value);
        if (index != -1) {
            return this->keys[index].child->add_down(Key);
        } else {
            return this->keys[this->keys.size() - 1].child->add_down(Key);
        }
    } else {
        return this->add_up(Key);
    }
}

int32_t Node::find_index(int64_t key) {
    int32_t index = -1;
    for (const auto& i : this->keys) {
        // Индекс первого превышающего элемента
        // По этому индексу спускаемся в дочерний вектор
        if (key <= i.value) {
            // Выхода за границы массива не будет из-за фиктивной вершины
            index = (int16_t) (&i - &(*std::begin(this->keys))) - 1;
            return index;
        }
    }

    return index;
}

void Node::insert(const Unit& Key) {
    int32_t index = this->find_index(Key.value);
    if (index != -1) {
        // Вставляем перед большим элементом либо в конец
        this->keys.emplace(this->keys.begin() + index, Key);
    } else {
        this->keys.push_back(Key);
    }
}


Node* Node::add_up(const Unit& Key) {
    if (this->keys.size() <= this->max_keys) {
        // Есть место для добавления
        this->insert(Key);
        return nullptr;
    } else {
        // Индекс, по которому делим узел
        size_t div_index = this->keys.size() / 2 + 1;
        // Элемент, который поднимем наверх
        Unit up = this->keys[div_index];

        // Новый узел с фиктивной вершиной вначале
        Node* new_node = new Node(this->t);
        new_node->keys[0].child = up.child;
        if (new_node->keys[0].child != nullptr) {
            new_node->is_leaf = false;
        }
        // Добавляем элементы в новый узел
        for (size_t i = div_index + 1; i < keys.size(); ++i) {
            new_node->keys.push_back(this->keys[i]);
        }
        // Удаляем элементы из узла
        this->keys.erase(this->keys.begin() + div_index, this->keys.end());
        // Добавляем новый элемент
        if (up.value <= Key.value) {
            new_node->insert(Key);
        } else {
            this->insert(Key);
        }
        /* Узел `up` ссылается на новый узел с ключами
        * больше либо равными keys[div_index]
        */
        up.child = new_node;
        // Проверка, в корне ли мы
        if (this->parent == nullptr) {
            Node* new_root = new Node(this->t, up, false, nullptr);
            new_root->keys[0].child = this;
            this->parent = new_root;
            new_node->parent = new_root;
            if (new_node->is_leaf == false) {
                for (auto i : new_node->keys) {
                    i.child->parent = new_node;
                }
            }
            return new_root;
        } else {
            // Не меняются предки 5 и 7
            // Все также указывают на -1 2 4
            new_node->parent = this->parent;
            return this->parent->add_up(up);
        }
    }
}

int Node::search(const int64_t& key, uint16_t* level) {
    for (const auto& i : this->keys) {
        // Индекс первого превышающего элемента
        // По этому индексу в дочернем векторе ищем элемент
        uint16_t index = (uint16_t) (&i - &(*std::begin(this->keys)));
        int64_t _value = i.value;
        bool _leaf = this->is_leaf;

        if (_value == key) {
            // Нашли элемент — вывели его индекс
            return index;
        } else if (_leaf == false) {
            // Спускаемся на уровень ниже
            ++(*level);
            if (key < _value) {
                return this->keys[index - 1].child->search(key, level);
            } else {
                // if (key > value)
                if (index == keys.size() - 1) {
                    return this->keys[index].child->search(key, level);
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
        bool _leaf = this->is_leaf;

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
            std::cout << i.value << " " << std::flush;
        }
    }

    // Если узел — не лист, значит спускаемся вниз
    if (this->is_leaf == false) {
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

// Поиск узла и вставка маркера удаление
void Node::delete_key(const int64_t& key) {
    std::pair<uint16_t, Node*> found = this->search(key);
    found.second->keys[found.first].deleted = true;
}

// Рекурсивное удаление узла
void Node::destroy() {
    if (this->keys[0].child->keys[0].child != nullptr) {
        // Есть внуки — пусть пока живет
        for (auto i : this->keys) {
            i.child->destroy();
            delete(i.child);
        }
    } else {
        // Нет внуков — убиваем детей
        for (auto i : this->keys) {
            delete(i.child);
        }
    }
}

//--------------------------------------
// Конструктор
Btree::Btree(size_t parameter, int64_t key = -1) {
    /* Дерево создается с первого ключа
     * узел, соответственно, и корень, и лист
     */
    root = new Node(parameter, key, true, nullptr);
    std::cout << "B-tree with parameter " << parameter << " and first key "
        << key << " succesfully made." << std::endl;
}

// Деструктор
Btree::~Btree() {
    root->destroy();
    delete(root);
}

/* Добавляет элемент от корня, рукурсивно спускаясь нижу в поисках
 * подходящего места
 * В случае появления нового корня производит замену
 */
void Btree::add(int64_t key) {
    std::cout << "Adding " << key << std::endl;
    Unit Key(key);
    Node* new_root = root->add_down(Key);
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
    Btree tree(t, 1);

    for (int i = 2; i < 10; ++i) {
        tree.add(i);
        tree.print();
    }
    tree.find(5);
    tree.find(11);

    tree.delete_key(6);
    tree.print();

    return EXIT_SUCCESS;
}
