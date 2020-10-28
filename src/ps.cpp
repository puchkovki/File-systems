// Copyright [2020] <Puchkov Kyryll>
#include <experimental/filesystem>
#include <fstream>
#include <iostream>
#include <string>

namespace fs = std::experimental::filesystem;

// Counts the real tty
void MakeRealTty(std::string* strTty);

// Return true in case the string is a number
bool isDigit(const std::string& s);

// Takes the [PID]/stat file apart
std::vector<std::string> ReadStat(std::string path);

// Prints the indent to make a better appearance
void PrintIndent(size_t size);

// Prints columns' titles
void PrintIntro();

// ps-analog
int ps(void);

//////////////////////////////////////////////////////////////////////////

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
        PrintIndent(pid.size());
    }

    void setCmd(std::string process_cmd) {
        cmd = process_cmd;
    }

    void getCmd(void) {
        std::cout << cmd;
        PrintIndent(cmd.size());
    }

    void setTty(std::string process_tty) {
        tty = process_tty;
    }

    void getTty(void) {
        std::cout << tty;
        PrintIndent(tty.size());
    }

    void setState(char process_state) {
        state = process_state;
    }

    void getState(void) {
        std::cout << state;
        PrintIndent(1);
    }

    void Print(void) {
        getPid();
        getState();
        getTty();
        getCmd();
        std::cout << std::endl;
    }
};


int main(void) {
    return ps();
}

// ps-analog
int ps(void) {
    const std::string proc = "/proc";
    std::vector<std::string> args;

    PrintIntro();
    for (auto& p : fs::directory_iterator(proc)) {
        if (isDigit(p.path())) {
            args = ReadStat(p.path().string() + "/stat");
            MakeRealTty(&args[6]);
            Processes proccess(args[0], args[1], args[2][0], args[6]);
            proccess.Print();
        }
    }
    return EXIT_SUCCESS;
}

// Prints columns' titles
void PrintIntro() {
    std::string pid = "PID";
    std::string comm = "CMD";
    std::string tty = "TTY";
    std::string state = "STATE";

    std::cout << pid;
    PrintIndent(pid.size());

    std::cout << state;
    PrintIndent(state.size());

    std::cout << tty;
    PrintIndent(tty.size());

    std::cout << comm;
    std::cout << std::endl;
}

// Prints the indent to make a better appearance
void PrintIndent(size_t size) {
    size_t Indent = 8;
    if (Indent > size) {
        for (size_t i = 0; i < (Indent - size); ++i) {
            std::cout << " ";
        }
    }
}

// Return true in case the string is a number
bool isDigit(const std::string& s) {
    if (s.find_first_of("0123456789") != std::string::npos) {
        return true;
    } else {
        return false;
    }
}

// Takes the [PID]/stat file apart
std::vector<std::string> ReadStat(std::string path) {
    std::vector<std::string> lines;
    std::ifstream f(path);
    std::string line;

    while (std::getline(f, line, ' ')) {
        lines.push_back(line);
    }

    return lines;
}


// Counts the real tty
void MakeRealTty(std::string* strTty) {
    /* Есть такие префиксы:
     * tty, pts/, ttyUSB, ttyACM, pts/ptmx
     * Им соответствуют major 4, 136, 188, 166, 5
     * В последнем случае минор не важен 
     * В остальных для получения реального tty требуется
     * сложить minor и major*/

    uint32_t tty;
    try {
        tty = stoll(*strTty);
    }
    catch (std::invalid_argument) {
         std::cerr << "No conversion could be performed!" << std::endl;
    }
    catch (std::out_of_range) {
        std::cerr << "The converted value would fall out of the"
            << " range of the result type!" << std::endl;
    }

    int major = 0;
    int minor = 0;
    int bit = 0;
    for (int i = 0; i < 32; ++i) {
        if ((i < 8) || (i > 15)) {
            // i-ый бит minor
            bit = (tty >> i) & 1;

            minor | bit;
            minor << 1;
        } else {
            // i-ый бит major
            bit = (tty >> i) & 1;

            major | bit;
            major << 1;
        }
    }

    std::string result;
    switch (major) {
        case '5':
            result = "pts/ptmx";
        case '4':
            result = "tty/" + std::to_string(minor);
        case '136':
            result = "pts/" + std::to_string(minor);
        case '188':
            result = "ttyUSB/" + std::to_string(minor);
        case '166':
            result = "ttyACM/" + std::to_string(minor);
        default:
            result = std::to_string(minor);
    }

    *strTty = result;
}
