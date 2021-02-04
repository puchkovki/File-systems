FLAGS = -I include -Wall -Wextra -pedantic -O3 -Wshadow -Wformat=2 \
-Wfloat-equal -Wconversion -Wcast-qual -Wcast-align -D_GLIBCXX_DEBUG \
-D_GLIBCXX_DEBUG_PEDANTIC -fsanitize=address,undefined \
-fno-sanitize-recover=all -fstack-protector

all: debug draw test

.PHONY: clean
clean:
	rm -rf res || echo "rm previous res directory: done"
	rm -rf build || echo "rm previous build directory: done"

build: clean
	mkdir -p res build

debug: build
	g++ $(FLAGS) -c -o build/debug.o src/debug.cpp
	g++ $(FLAGS) -o build/debug build/debug.o 
	./build/debug > res/debug.txt

test: build
	g++ $(FLAGS) -c -o build/test.o src/test.cpp
	g++ $(FLAGS) -o build/test build/test.o 
	./build/test
	
draw: build
	g++ $(FLAGS) -c -o build/main.o src/main.cpp
	g++ $(FLAGS) -o build/tree build/main.o
	./build/tree
	dot res/b-tree.gv -y -Tpng -o res/b-tree.png
