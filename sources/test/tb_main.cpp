#include "verilated.h"
#include "verilated_cov.h"

// Verilator will pass -DTOP_CLASS=Vtb_fifo (or Vtb_cpu) from the Makefile.
// Stringify helper
#define STR_HELPER(x) #x
#define STR(x) STR_HELPER(x)

// Include the generated header for TOP_CLASS
#include STR(TOP_CLASS.h)

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->traceEverOn(true);

    const std::unique_ptr<TOP_CLASS> top{new TOP_CLASS{contextp.get()}};

    while (!contextp->gotFinish()) {
        top->eval();
        contextp->timeInc(1);
    }

    VerilatedCov::write("build/sims/coverage.dat");
    VL_PRINTF("Coverage written to build/sims/coverage.dat\n");
    return 0;
}
