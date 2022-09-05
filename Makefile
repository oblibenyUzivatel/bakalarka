# Makefile pro preklad c++ kodu pomoci programu g++
# Autor: Ondřej Polanský
# FIT VUT
# Brno 17.05.2020
# Vytvori spustitelny program bakalarka, nasledne se da spustit napriklad prikazem: ./bakalarka -d <"cesta k automatu"

C++FLAGS=-std=c++17 -pedantic -Wall -Wextra -O3

all: bakalarka

bakalarka: bakalarka.cpp
	g++ bakalarka.cpp -o bakalarka $(C++FLAGS)

clean:
	rm -f bakalarka
