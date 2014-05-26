This contains source code for enumerating permutations avoiding the 1324 pattern,
as described in 
  On 1324-avoiding permutations
  Andrew R. Conway and Anthony J. Guttmann
 
The language is scala, tested in versions 2.10 and 2.11.
Libraries are needed in order to get it to compile and run
  - junit4 (to compile ZZZ_Signature, a test case). 
  - gnu trove (hash map). Tested with version 3.0.3

The main program is avoid1324.DoCount. It can be run with command line options:
  - first an integer between 0 and 9 which will determine what prime everything is done modulo.
  - second the number of terms desired to count.
  
There is a threaded version, avoid1324.DoCountThreaded. It adds an extra parameter, 
the number of threads to use, in between the above two parameters.
  
There is also a whole lot of debugging code, diagnostics and test
code.