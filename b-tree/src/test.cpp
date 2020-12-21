// Copyright [2020] <Puchkov Kyryll>
#include <ctime>
#include <set>
#include <fstream>
#include <queue>
#include <b-tree.hpp>

enum Command {
    Add,
    Find,
    Delete
};

Command chooseCommand(int64_t newCommand) {
    if (newCommand % 2 == 0) {
        return Add;
    } else if (newCommand % 3 == 0) {
        return Delete;
    }

    return Find;
}

void find_key(int64_t* key, std::queue <int64_t>* to_find) {
    if ((*key % 100) > 50) {
        if (to_find->size() > 100) {
            to_find->pop();
        }
        to_find->push(*key);
        *key = to_find->front();
    }
}

int main(void) {
    size_t t = 10;
    srand((uint)time(0));
    int64_t key = rand();
    Btree tree(t, key);
    std::multiset<int64_t> set_tree = {key};
    std::queue <int64_t> queue_find;

    for (int64_t i = 0; i < 10000; ++i) {
        int64_t commandKey = rand();
        Command newCommand = chooseCommand(commandKey);

        key = rand();
        switch (newCommand) {
        case Add: {
            bool error_occured = false;
            tree.add(key);

            auto multiset_result = set_tree.insert(key);
            if (multiset_result == set_tree.end()) {
                error_occured = true;
            }

            assert((error_occured == false)
                && "Adding to the b-tree went wrong!");
            find_key(&key, &queue_find);
            break;
        }
        case Find: {
            bool results_are_equal = true;
            find_key(&key, &queue_find);
            std::pair<int32_t, Node*> tree_result = tree.find(key);

            auto multiset_result = set_tree.find(key);
            if ((multiset_result != set_tree.end())
                && (tree_result.second == nullptr)) {
                std::cout << "Couldn't find " << key << " in the tree!"
                    << std::endl;
                results_are_equal = false;
            }
            if ((multiset_result == set_tree.end())
                && (tree_result.second != nullptr)) {
                results_are_equal = false;
                std::cout << "Couldn't find " << key << " in the set!"
                    << std::endl;
            }
            assert((results_are_equal == true)
                && "Searching in the b-tree went wrong!");
            break;
        }
        case Delete: {
            bool error_occured = false;
            std::pair<int32_t, Node*> tree_result = tree.delete_key(key);

            if ((set_tree.find(key) != set_tree.end())
                && (tree_result.second == nullptr)) {
                // Элемент существует существует в set
                set_tree.erase(key);
                    // Но в дереве его нет
                    error_occured = true;
                    std::cout << "Key" << key
                        << "had been removed from the the multiset, "
                        << "but couldn't be removed from the b-tree"
                        << std::endl;
            }
            if ((set_tree.find(key) == set_tree.end())
                && (tree_result.second != nullptr)) {
                error_occured = true;
                std::cout << "Key" << key << "had been removed from the b-tree"
                        << ", but couldn't be removed from the multiset"
                        << std::endl;
            }

            assert((error_occured == false)
                && "Deleting from the b-tree went wrong!");
            break;
        }
        default:
            assert(false && "New command appeared!");
            break;
        }
    }

    std::ofstream out("res/test.txt");
    if (out.is_open() == 1) {
        for (const auto& i : set_tree) {
            out << i << " ";
        }
        out << std::endl;
        tree.DFS_print(out);
    } else {
        std::cout << "Cannot open file res/test.txt for writing!";
    }

    std::ifstream in("res/test.txt");
    std::string test_set, test_tree;
     if (in.is_open() == 1) {
        std::getline(in, test_set);
        std::getline(in, test_tree);
        if ((out.is_open() == 1) && (test_set == test_tree)) {
            out << "Structures are equal! Algorythm has worked correctly!"
                << std::endl;
        } else {
            out << "Structures aren't equal! Algorythm has worked wrong!"
                << std::endl;
        }
    } else {
        std::cout << "Cannot open file res/test.txt for reading!";
    }

    in.close();
    out.close();

    return EXIT_SUCCESS;
}
