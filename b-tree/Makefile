FLAGS = -I include -Wall -Wextra -pedantic -O3 -Wshadow -Wformat=2 \
-Wfloat-equal -Wconversion -Wcast-qual -Wcast-align -D_GLIBCXX_DEBUG \
-D_GLIBCXX_DEBUG_PEDANTIC -fsanitize=address,undefined \
-fno-sanitize-recover=all -fstack-protector

all: print

build:
	mkdir -p build

build/main.o: build
	g++ $(FLAGS) -c -o build/main.o src/main.cpp
	g++ $(FLAGS) -c -o build/debug.o src/debug.cpp

res:
	rm -rf ./res/ || echo "rm previous res file: done"
	mkdir res

execute: build/main.o res
	g++ $(FLAGS) -o build/tree build/main.o
	./build/tree > res/b-tree.gv
	g++ $(FLAGS) -o build/debug build/debug.o 
	./build/debug > res/test.txt

print: execute
	dot res/b-tree.gv -y -Tpng -o res/b-tree.png 
