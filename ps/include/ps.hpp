// Copyright [2020] <Puchkov Kyryll>
#ifndef  PS_INCLUDE_PS_HPP_
#define  PS_INCLUDE_PS_HPP_

#include <experimental/filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace fs = std::experimental::filesystem;

// Counts the real tty
void CountRealTty(std::string* strTty);

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

class Processes {
 public:
    std::string pid;
    std::string cmd;
    std::string tty;
    char state;

    Processes(std::string process_id, std::string process_cmd,
    char process_state, std::string process_tty);

    Processes();

    ~Processes();

    void setPid(std::string process_id);
    void getPid(void);

    void setCmd(std::string process_cmd);
    void getCmd(void);

    void setTty(std::string process_tty);
    void getTty(void);

    void setState(char process_state);
    void getState(void);

    void Print(void);
};

#endif  // PS_INCLUDE_PS_HPP_
