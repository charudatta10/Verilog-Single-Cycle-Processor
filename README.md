# Single Cycle Processor

## Design Objective
The objective is to design and implement a single cycle MIPS computer in Verilog that supports MIPS assembly instructions including:
- Memory-reference instructions load word ```lw``` and store word ```sw```
- Arithmetic-logical instructions ```add```, ```addi```, ```sub```, ```and```, ```andi```, ```or```, and ```slt```
- Jumping instructions branch-equal ```beq``` and jump ```j```

A rough schematic description of the single cycle computer is available here: ![Single Cycle Schematics](http://undergrad.hxing.me/VE370/Single+Cycle+Schematics.png?x-source=github) However, the picture is **NOT an exhaustive** description of the architecture we designed.

## MIPS Instructions
32 lines of MIPS instructions are hard-coded into the program. More specifically, into the Instruction-Memory module.

```MIPS
Imemory[0] = 32'b00100000000010000000000000100000; //addi $t0, $zero, 32 
Imemory[1] = 32'b00100000000010010000000000110111; //addi $t1, $zero, 55 
Imemory[2] = 32'b00000001000010011000000000100100; //and $s0, $t0, $t1 
Imemory[3] = 32'b00000001000010011000000000100101; //or $s0, $t0, $t1 
Imemory[4] = 32'b10101100000100000000000000000100; //sw $s0, 4($zero) 
Imemory[5] = 32'b10101100000010000000000000001000; //sw $t0, 8($zero) 
Imemory[6] = 32'b00000001000010011000100000100000; //add $s1, $t0, $t1 
Imemory[7] = 32'b00000001000010011001000000100010; //sub $s2, $t0, $t1 
Imemory[8] = 32'b00010010001100100000000000001001; //beq $s1, $s2, error0 
Imemory[9] = 32'b10001100000100010000000000000100; //lw $s1, 4($zero) 
Imemory[10]= 32'b00110010001100100000000001001000; //andi $s2, $s1, 48 
Imemory[11] =32'b00010010001100100000000000001001; //beq $s1, $s2, error1 
Imemory[12] =32'b10001100000100110000000000001000; //lw $s3, 8($zero) 
Imemory[13] =32'b00010010000100110000000000001010; //beq $s0, $s3, error2 
Imemory[14] =32'b00000010010100011010000000101010; //slt $s4, $s2, $s1 (Last) 
Imemory[15] =32'b00010010100000000000000000001111; //beq $s4, $0, EXIT 
Imemory[16] =32'b00000010001000001001000000100000; //add $s2, $s1, $0 
Imemory[17] =32'b00001000000000000000000000001110; //j Last
Imemory[18] =32'b00100000000010000000000000000000; //addi $t0, $0, 0(error0) 
Imemory[19] =32'b00100000000010010000000000000000; //addi $t1, $0, 0 
Imemory[20] =32'b00001000000000000000000000011111; //j EXIT
Imemory[21] =32'b00100000000010000000000000000001; //addi $t0, $0, 1(error1) 
Imemory[22] =32'b00100000000010010000000000000001; //addi $t1, $0, 1 
Imemory[23] =32'b00001000000000000000000000011111; //j EXIT
Imemory[24] =32'b00100000000010000000000000000010; //addi $t0, $0, 2(error2) 
Imemory[25] =32'b00100000000010010000000000000010; //addi $t1, $0, 2 
Imemory[26] =32'b00001000000000000000000000011111; //j EXIT
Imemory[27] =32'b00100000000010000000000000000011; //addi $t0, $0, 3(error3) 
Imemory[28] =32'b00100000000010010000000000000011; //addi $t1, $0, 3 
Imemory[29] =32'b00001000000000000000000000011111; //j EXIT
```

You are, of course, free to use any other MIPS assembly instructions within 32 lines and using only the instructions described in the ```Design Objective``` section. 

## Compilation & Testing
The verilog code was complied with software
```
Xilinx ISE 10.1
```

and tested on hardware
```FPGA
Model: Digilent NEXYS2
Family: Spartan3E
Device: XC3s1200E
Package: FG320
Speed: -4
```

with an executable BIT file generated **specifically** for the hardware listed above. Download BIT file [here](http://undergrad.hxing.me/VE370/single_cycle.bit?x-source=github).

Digilent NEXYS2 hardware [PIN assignment](http://undergrad.hxing.me/VE370/PIN+Assignment.png?x-source=github) is based on [Digilent Nexys2 FPGA Board Manual](http://undergrad.hxing.me/VE270/Digilent+Nexys2+Manual.pdf?x-source=github-project=ve370singlecycle).

## Manual & Report
The code is designed for a school project.
- [Project Manual](http://undergrad.hxing.me/VE370/Project+II+Manual.pdf?x-source=github)
- [Project Report](http://undergrad.hxing.me/VE370/Project+II+Report.pdf?x-source=github)

## Two Versions
We have two Verilog files in the repo. Both are designed for the same objectives.
- ```single_cycle_v11_demo.v``` is compiled to generate executable files for FPGA board demo. This version contains a clock divider that slows a 5M Hz hardware clock to 1 Hz.
- ```single_cycle_v11_sim.v``` is reserved for Xilinx software simulations only. This version sets clock divider to expect a significantly slower clock input. We also left an extra 32-bit ```reg_read_data_1``` port open for diagnostic purposes.

## Pipeline Processor
A pipeline version was designed to execute the same MIPS instructions. Source code for that project is available on [GitHub](https://github.com/hxing9974/Verilog-Pipeline-Processor.git).

## Credits
This project is executed in a three-person team. Junqi Qian and Xinyue Ou are among the best engineers I have worked with. I could not have done it without them.

## Additional Resources
For projects just like this one, please visit my website at [http://www.hxing.me/academics](http://www.hxing.me/academics).
