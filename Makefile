
ARCH:=unix
TARGET = vchash

COMPILE = gcc
CPPCOMPILE = g++

LIBS += -ldl -lpthread -lm -lstdc++\
		-laprutil-1\
		-lapr-1
	

OBJS_LIB =  ./lib/oryx_list.o\
			./lib/oryx_ipc.o\
			./lib/oryx_assert.o\
			./lib/oryx_rbtree.o

OBJS_LOCAL = oryx_cvhash.o\
			$(OBJS_LIB)

CFLAGS_LOCAL := -std=gnu99 -W -Wall -Wunused-parameter -g -O3\
			-I ./lib/\
			-I ./lib/third_party/apr/apr\
			-I ./lib/third_party/apr/apr/arch/$(ARCH)\
			-I ./lib/third_party/apr/apr-util

.PHONY: compile clean


$(TARGET): $(OBJS_LOCAL) 
	$(COMPILE) -o $@ $(OBJS_LOCAL) $(LIBS)

$(OBJS_LOCAL): %.o : %.c
	$(COMPILE) $(CFLAGS_LOCAL) -c $< -o $@

$(CPP_OBJS_LOCAL): %.o : %.cpp
	$(CPPCOMPILE) $(CFLAGS_LOCAL) -c $< -o $@

clean:
	rm -rf $(OBJS_LOCAL) $(CPP_OBJS_LOCAL) $(TARGET) 


