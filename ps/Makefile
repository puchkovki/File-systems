FLAGS = -I include -Wall -Wextra -pedantic -O3 -Wshadow -Wformat=2 \
-Wfloat-equal -Wconversion -Wcast-qual -Wcast-align -D_GLIBCXX_DEBUG \
-D_GLIBCXX_DEBUG_PEDANTIC -fsanitize=address,undefined \
-fno-sanitize-recover=all -fstack-protector

all: build build/main.o res test 
	./build/test > res/ps.txt

build:
	mkdir -p build

build/main.o: build
	g++ $(FLAGS) -c -o build/main.o src/ps.cpp -lstdc++fs

test: build build/main.o
	g++ $(FLAGS) -o build/test build/main.o -lstdc++fs

res:
	rm res/ps.txt || echo "rm previous res file: done"
	mkdir -p res