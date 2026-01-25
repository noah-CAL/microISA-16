#include "Vtb_fifo.h"
#include "verilated.h"
#include "verilated_cov.h"

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->traceEverOn(true);
    
    const std::unique_ptr<Vtb_fifo> top{new Vtb_fifo{contextp.get()}};
    
    while (!contextp->gotFinish()) {
        top->eval();
        contextp->timeInc(1);  // Increment time
    }
    
    VerilatedCov::write("build/sims/coverage.dat");
    printf("Coverage written to build/sims/coverage.dat\n");
    
    return 0;
}
