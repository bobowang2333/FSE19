The set of C programs were used as benchmarks in the following paper:

@inproceedings{wang2019mitigating,
  title={Mitigating power side channels during compilation},
  author={Wang, Jingbo and Sung, Chungha and Wang, Chao},
  booktitle={Proceedings of the 2019 27th ACM Joint Meeting on European Software Engineering  Conference and Symposium on the Foundations of Software Engineering},
  pages={590--601},
  year={2019}
}

@inproceedings{barthe2015verified,
  title={Verified proofs of higher-order masking},
  author={Barthe, Gilles and Bela{\"\i}d, Sonia and Dupressoir, Fran{\c{c}}ois and Fouque, Pierre-Alain and Gr{\'e}goire, Benjamin and Strub, Pierre-Yves},
  booktitle={Annual International Conference on the Theory and Applications of Cryptographic Techniques},
  pages={457--485},
  year={2015},
  organization={Springer}
}


Each benchmark consists of 2 input files. The first input file is the *.c or *.cpp file representing the source code.

The second file - "input.txt" specifies the types of all the input variables: "KEY" denotes secret input, "CONSTANT" denotes the public input, "RAND" stands for the random input.





