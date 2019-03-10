# Z34Delphi
  The [Z3](https://github.com/Z3Prover/z3) Theorem Prover bindings for Delphi.
  Based on c Binding. [here](https://github.com/Z3Prover/z3/tree/master/src/api).
  
  Ported All Api to Delphi
  
#### Adding Class Wrapper For All Types(Based on [z3++.h](https://github.com/Z3Prover/z3/tree/master/src/api/c%2B%2B) )
* **Z3.Context.pas**
    * Z3_context           
    * Z3_symbol             
    * Z3_params             
    * Z3_ast                
      * Expr               
      * Z3_Sort            
      * Z3_func_decl       
    * Z3_ast_vector         
      * Expr_vector        
      * Sort_vector        
      * Func_decl_vector
*  **Z3.Arr.pas**
    * Z3 Array
*  **Z3.Config.pas**
    * Z3_config
* **Z3.Func.pas**	
    * Common Function for All Module and Emulate Class Operator(not implemened in Delphi Class)
* **Z3.Model.pas**
    * Z3_func_entry  
    * Z3_func_interp    
    * Z3_model 
* **Z3.Par_Desc.pas**
    * Z3_param_descrs
* **Z3.Solver.pas**	
    * Z3_solver
* **Z3.Stats.pas**		
    * Z3_stats
* **Z3.Tactic.pas**
    * Z3_goal 
    * Z3_apply_result
    * Z3_tactic 
	
## examples
* Test for Native Api
* Test for Class wrapper
* Test for opaque predicates in x86 code( original [code](www.zubcic.re)  by  zubcic.tomislav@gmail.com )


## Note
  * If you are not familiar with Z3, you can start [here](https://github.com/Z3Prover/z3/wiki#background).
  * Update Test Project for testing Z3 Native Api and Class Wrapper
  * Test project compiled with Delphi 10.3(Rio)
  
## ToDo  
  * Adding Class for Z3_probe,Z3_optimize,Z3_fixedpoint.
  * Adding Test Function for Class Wrapper
  * Test on x64 and More . Any collaboration is welcome ;) 

