// Copyright [2020] <Puchkov Kyryll>
#ifndef LSOF_HPP_
#define LSOF_HPP_

#include <unistd.h>
#include <experimental/filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>

namespace fs = std::experimental::filesystem;

// Makes a vector without the repetetive elements
void makeUnique(std::vector<std::string> links);

// Prints the indent to make a better appearance
void printIndent(size_t size);

// Prints columns' titles
void printIntro();

// Reads the symbolic link
std::string doReadLink(std::string const& path);

// Gets the PID of the proccess
std::string readPid(std::string path);

// Return true in case the string is a number
bool isDigit(const std::string& s);

// lsof-analog
int lsof(void);

class Processes {
 private:
    std::string pid;
    std::vector<std::string> links;

 public:
    Processes(std::string process_id, std::vector<std::string> refers);

    ~Processes();

    void setPid(std::string process_id);
    void getPid(void);

    void setLinks(std::vector<std::string> refers);
    std::vector<std::string> getLinks(void);

    void Print(void);
};

#endif  // LSOF_HPP_
