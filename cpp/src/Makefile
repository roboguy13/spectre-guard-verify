
# TOOLNAME = sg-verify  #the name of your tool's executable

# SOURCES := SetExpr.cpp ConstraintGenerator.cpp  #the Clang source files you want to compile

# # include $(CLANG_LEVEL)/../../Makefile.config

# LINK_COMPONENTS := $(TARGETS_TO_BUILD) asmparser bitreader support mc option

# USEDLIBS = clangFrontend.a clangSerialization.a clangDriver.a \
#            clangTooling.a clangParse.a clangSema.a \
#            clangAnalysis.a clangRewriteFrontend.a clangRewriteCore.a \
#            clangEdit.a clangAST.a clangLex.a clangBasic.a

LIBS = -lclangFrontend -lclangSerialization -lclangDriver \
           -lclangTooling -lclangParse -lclangSema \
           -lclangAnalysis -lclangRewriteFrontend \
           -lclangEdit -lclangAST -lclangLex -lclangBasic -lz3


LLVM_LIBS := $(shell llvm-config --libs --system-libs --ldflags)

CXX=clang

DEPS=SetExpr.h ConstraintGen.h Z3Gen.h
LLVM_LIB_DIR=/usr/local/opt/llvm/lib
CXXFLAGS=-I/usr/local/opt/llvm/include -L$(LLVM_LIB_DIR) -std=c++17

OBJS=SetExpr.o ConstraintGen.o Z3Gen.o Verify.o
DEBUG=-g

EXE=sg-verify

all: sg-verify

sg-verify: $(OBJS)
	$(CXX) $(DEBUG) $(LIBS) $(OBJS) -o $(EXE) $(LIBDIR) $(LLVM_LIBS) $(LLVM_LIB_DIR)/*.dylib

%.o: %.cpp $(DEPS)
	$(CXX) $(DEBUG) -c -o $@ $< $(CXXFLAGS)

clean:
	rm -f *.o $(EXE)



# include $(CLANG_LEVEL)/Makefile
