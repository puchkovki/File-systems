// Copyright [2020] <Puchkov Kyryll>
#include "lsof.hpp"

namespace fs = std::experimental::filesystem;

Processes::Processes(std::string process_id, std::vector<std::string> refers)
    : pid(process_id),
    links(refers) {}

Processes::~Processes() {}

void Processes::setPid(std::string process_id) {
    pid = process_id;
}

void Processes::getPid(void) {
    std::cout << pid;
    printIndent(pid.size());
}

void Processes::setLinks(std::vector<std::string> refers) {
    links = refers;
}

std::vector<std::string> Processes::getLinks(void) {
    return links;
}

void Processes::Print(void) {
    std::vector<std::string> refers = Processes::getLinks();

    if (refers.size() != 0) {
        for (auto& i : refers) {
            Processes::getPid();
            std::cout << i << std::endl;
        }
    }
}


int main(void) {
    return lsof();
}

// lsof-analog
int lsof(void) {
    const std::string proc = "/proc";

    printIntro();
    for (auto& p : fs::directory_iterator(proc)) {
        if (isDigit(p.path())) {
            std::string pid = readPid(p.path().string());

            std::string map_files = p.path().string() + "/map_files";
            std::vector<std::string> links{};
            for (auto& link : fs::directory_iterator(map_files,
                fs::directory_options::skip_permission_denied)) {
                links.push_back((link.path().string()));
            }
            makeUnique(links);

            Processes proccess(pid, links);
            proccess.Print();
        }
    }
    return EXIT_SUCCESS;
}

// Prints columns' titles
void printIntro() {
    std::string pid = "PID";
    std::cout << "PID";
    printIndent(pid.size());
    std::cout << "NAME";

    std::cout << std::endl;
}

// Return true in case the string is a number
bool isDigit(const std::string& s) {
    if (s.find_first_of("0123456789") != std::string::npos) {
        return true;
    } else {
        return false;
    }
}

// Prints the indent to make a better appearance
void printIndent(size_t size) {
    size_t Indent = 8;
    if (Indent > size) {
        for (size_t i = 0; i < (Indent - size); ++i) {
            std::cout << " ";
        }
    }
}

// Gets the PID of the proccess
std::string readPid(std::string path) {
    std::string pid = "?";
    size_t slash = path.find_last_of("/");

    if (slash != std::string::npos) {
        pid = path.substr(slash + 1);
    }

    return pid;
}

// Reads the symbolic link
std::string doReadLink(std::string const& path) {
    char buff[1024];
    ssize_t len = readlink(path.c_str(), buff, sizeof(buff)-1);

    if (len != -1) {
      buff[len] = '\0';
      return std::string(buff);
    } else {
        perror("readlink");
        return "?";
    }
}

// Makes a vector without the repetetive elements
void makeUnique(std::vector<std::string> links) {
    sort(links.begin(), links.end());
    links.resize(unique(links.begin(), links.end()) - links.begin());
}
