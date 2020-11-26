// Copyright [2020] <Puchkov Kyryll>
#include "ps.hpp"

namespace fs = std::experimental::filesystem;

Processes::Processes(std::string process_id, std::string process_cmd,
char process_state, std::string process_tty)
    : pid(process_id),
    cmd(process_cmd),
    tty(process_tty),
    state(process_state) {}

Processes::Processes()
    : pid(0), cmd("process's_cmd"), tty("0"), state('X') {}

Processes::~Processes() {}

void Processes::setPid(std::string process_id) {
    pid = process_id;
}

void Processes::getPid(void) {
    std::cout << pid;
    PrintIndent(pid.size());
}

void Processes::setCmd(std::string process_cmd) {
    cmd = process_cmd;
}

void Processes::getCmd(void) {
    std::cout << cmd;
    PrintIndent(cmd.size());
}

void Processes::setTty(std::string process_tty) {
    tty = process_tty;
}

void Processes::getTty(void) {
    std::cout << tty;
    PrintIndent(tty.size());
}

void Processes::setState(char process_state) {
    state = process_state;
}

void Processes::getState(void) {
    std::cout << state;
    PrintIndent(1);
}

void Processes::Print(void) {
    Processes::getPid();
    Processes::getState();
    Processes::getTty();
    Processes::getCmd();
    std::cout << std::endl;
}


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
            CountRealTty(&args[6]);
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
void CountRealTty(std::string* strTty) {
    /* Есть префиксы:
     * tty, pts/, ttyUSB, ttyACM, pts/ptmx
     * Им соответствуют major 4, 136, 188, 166, 5
     * В последнем случае минор не важен 
     * В остальных для получения реального tty требуется
     * сложить minor и major*/

    uint32_t tty = EXIT_FAILURE;
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

    int32_t major = (tty & (255 << 8)) >> 8;
    int32_t minor = (tty & 255) + ((tty & (65535 << 16)) >> 8);

    std::string result;
    if (tty == EXIT_FAILURE) {
        result = "?";
    } else {
        switch (major) {
            case 4:
                result = "tty" + std::to_string(minor);
                break;
            case 5:
                result = "pts/ptmx";
                break;
            case 136:
                result = "pts/" + std::to_string(minor);
                break;
            case 166:
                result = "ttyACM" + std::to_string(minor);
                break;
            case 188:
                result = "ttyUSB" + std::to_string(minor);
                break;
            case 247:
                result = "ttyHSL0";
                break;
            case 248:
                result = "ttyHSL0";
                break;
            default:
                result = "?";
                break;
        }
    }

    *strTty = result;
}
