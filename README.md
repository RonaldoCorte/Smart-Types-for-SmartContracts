# Smart-Types-for-SmartContracts

This repository holds multiple tools for Smart Contracts development and validation. You can write a Smart Contract with MiniFS, a calculus that models the core features
of Solidity. Then, you can also parse it to the input format of the Model Checker Cubicle and use it to automaticaly verify safety properties about the written Smart Contract.


## Methodology 
To use this tool, you can start by cloning this repository. In this one you have two folders, cubicle and parser. 

In cubicle folder you have some cubicle examples of use. In parser you can access the main tools of this project.

- First, in "minifs.ml" you can write (in the end of the file) a Smart Contract in MiniFS. To do it, you can access to its grammar in the beginning of the file and use 
the main function "typecheck contract" to check if it is well typed.

- Then you can copy that implementation to the "MiniCubParser.ml" file and use the main function "parse_contract" to parse the contract from MINIFS to MiniCub. To run this file,
you have to execute the following commands "ocamlopt -c types.ml", "ocamlopt -c minicubParser.ml", "ocamlopt -o parser types.cmx minicubParser.cmx" and finally "./parser".

- After this, you can use the main function "parse_contract" of the file "cubParser.ml" and parse the minicub version of the Smart Contract to Cubicle's input format. To run this file
you simply need to execute the following commands "ocamlopt -c types.ml", "ocamlopt -c minicubParser.ml", "ocamlopt -c cubParser.cmx",
"ocamlopt -o parser types.cmx minicubParser.cmx cubParser.cmx" and finally, "./parser".

- The last step will generate a file called "${contract_name}_parsed.cub" and finally, you can inspect this cubicle file and if you want, you can also add some extra safety conditions that you may want to verify.
  To model check this contract you simply have to execute this command "cubicle contract_parsed.cub".
  
  ## Examples
  In all of these files you the following examples of use:
  - Bank example
  - [Simple Marketplace](https://github.com/Azure-Samples/blockchain/tree/master/blockchain-workbench/application-and-smart-contract-samples/simple-marketplace)
  - [Digital Locker](https://github.com/Azure-Samples/blockchain/tree/master/blockchain-workbench/application-and-smart-contract-samples/digital-locker)
  - [Telemetry](https://github.com/Azure-Samples/blockchain/tree/master/blockchain-workbench/application-and-smart-contract-samples/refrigerated-transportation)


  
  
