// Copyright [2020] <Puchkov Kyryll>
#include <experimental/filesystem>
#include <fstream>
#include <iostream>

namespace fs = std::experimental::filesystem;
#define Indent 8

class Processes {
 public:
    std::string pid;
    std::string cmd;
    std::string tty;
    char state;

    Processes(std::string process_id, std::string process_cmd,
    char process_state, std::string process_tty)
        : pid(process_id),
        cmd(process_cmd),
        tty(process_tty),
        state(process_state) {}

    Processes()
        : pid(0), cmd("process's_cmd"), tty("0"), state('X') {}

    ~Processes() {}

    //////////////////////////////////////////////

    void setPid(std::string process_id) {
        pid = process_id;
    }

    void getPid(void) {
        std::cout << pid;
        int size = pid.size();
        for (int i = 0; i < (Indent - size); ++i) {
            std::cout << " ";
        }
    }

    void setCmd(std::string process_cmd) {
        cmd = process_cmd;
    }

    void getCmd(void) {
        std::cout << cmd;
        int size = cmd.size();
    }

    void setTty(std::string process_tty) {
        tty = process_tty;
    }

    void getTty(void) {
        std::cout << tty;
        int size = tty.size();
        for (int i = 0; i < (Indent - size); ++i) {
            std::cout << " ";
        }
    }

    void setState(char process_state) {
        state = process_state;
    }

    void getState(void) {
        std::cout << state;
        int size = 1;
        for (int i = 0; i < (Indent - size); ++i) {
            std::cout << " ";
        }
    }

    void Print(void) {
        getPid();
        getState();
        getTty();
        getCmd();
        std::cout << std::endl;
    }
};

// Return true in case the string is a number
bool isDigit(const std::string& s) {
    if (s.find_first_of("0123456789") != std::string::npos) {
        return true;
    } else {
        return false;
    }
}

std::vector<std::string> ReadStat(std::string path) {
    std::vector<std::string> lines;
    std::ifstream f(path);
    std::string line;
    while (std::getline(f, line, ' ')) {
        lines.push_back(line);
    }
    return lines;
}

Processes ProccessInfo(const std::vector<std::string>& stat) {
    Processes proccess(stat[0], stat[1], stat[2][0], stat[6]);
    return proccess;
}

void PrintIntro() {
    std::string pid = "PID";
    std::string comm = "CMD";
    std::string tty = "TTY";
    std::string state = "STATE";

    std::cout << pid;
    int size = pid.size();
    for (int i = 0; i < (Indent - size); ++i) {
        std::cout << " ";
    }

    std::cout << tty;
    size = tty.size();
    for (int i = 0; i < (Indent - size); ++i) {
        std::cout << " ";
    }

    std::cout << state;
    size = state.size();
    for (int i = 0; i < (Indent - size); ++i) {
        std::cout << " ";
    }

    std::cout << comm;
    size = comm.size();
    std::cout << std::endl;
}

int ps(void) {
    const std::string proc = "/proc";
    std::string tmp;
    std::vector<std::string> args;

    PrintIntro();
    for (auto& p : fs::directory_iterator(proc)) {
        if (isDigit(p.path())) {
            args = ReadStat(p.path().string() + "/stat");
            Processes proccess = ProccessInfo(args);
            proccess.Print();
        }
    }
    return EXIT_SUCCESS;
}

int main(void) {
    return ps();
}
