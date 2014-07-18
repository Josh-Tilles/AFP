header "Abstract Syntax Tree"
theory PromelaAST
imports Main
begin

text {* 
  The abstract syntax tree is generated from the handwritten SML parser. 
  This theory only mirrors the data structures from the SML level to make them available in 
  Isabelle.
*}

context
begin

(* Force everything in this context to start with AST. *)
local_setup {*
  Local_Theory.map_naming (Name_Space.mandatory_path "AST")
*} 

datatype_new binOp = 
                 BinOpAdd
               | BinOpSub
               | BinOpMul
               | BinOpDiv
               | BinOpMod
               | BinOpBitAnd
               | BinOpBitXor
               | BinOpBitOr 
               | BinOpGr
               | BinOpLe
               | BinOpGEq
               | BinOpLEq
               | BinOpEq
               | BinOpNEq
               | BinOpShiftL
               | BinOpShiftR
               | BinOpAnd
               | BinOpOr

datatype_new unOp = 
                UnOpComp
              | UnOpMinus
              | UnOpNeg

datatype_new expr = 
                ExprBinOp binOp (*left*) expr (*right*) expr
              | ExprUnOp unOp expr
              | ExprCond (*cond*) expr (*exprTrue*) expr (*exprFalse*) expr
              | ExprLen varRef
              | ExprPoll varRef "recvArg list"
              | ExprRndPoll varRef "recvArg list"
              | ExprVarRef varRef
              | ExprConst integer
              | ExprTimeOut
              | ExprNP
              | ExprEnabled expr
              | ExprPC expr
              | ExprRemoteRef (*name*) String.literal
                              (*num*) "expr option"
                              (*label*) String.literal
              | ExprGetPrio expr
              | ExprSetPrio (*expr*) expr (*prio*) expr
              | ExprFull varRef
              | ExprEmpty varRef
              | ExprNFull varRef
              | ExprNEmpty varRef

   and varRef = VarRef (*name*) String.literal 
                       (*index*) "expr option"
                       (*next*) "varRef option"

   and recvArg = RecvArgVar varRef
               | RecvArgEval expr
               | RecvArgConst integer

datatype_new range = 
                RangeFromTo (*var*) varRef
                            (*from*) expr
                             (*to*)  expr
               | RangeIn (*var*) varRef (*inside*) varRef

datatype_new varType = 
                   VarTypeBit
                 | VarTypeBool
                 | VarTypeByte
                 | VarTypePid
                 | VarTypeShort
                 | VarTypeInt
                 | VarTypeMType
                 | VarTypeChan
                 | VarTypeUnsigned
                 | VarTypeCustom String.literal

datatype_new varDecl = 
                   VarDeclNum  (*name*) String.literal
                               (*size*) "integer option"
                               (*init*) "expr option"
                 | VarDeclChan (*name*) String.literal
                               (*size*) "integer option"
                               (*capacityTypes*) "(integer * varType list) option"
                 | VarDeclUnsigned (*name*) String.literal
                                   (*bits*) integer
                                   (*init*) "expr option"
                 | VarDeclMType (*name*) String.literal
                                (*size*) "integer option"
                                (*init*) "String.literal option"


datatype_new decl = 
                 Decl (*vis*) "bool option"
                     (*sort*) varType
                     (*decl*) "varDecl list"


datatype_new stmnt = 
                 StmntIf "(step list) list"
               | StmntDo "(step list) list"
               | StmntFor range "step list"
               | StmntAtomic "step list"
               | StmntDStep "step list"
               | StmntSelect range
               | StmntSeq "step list"
               | StmntSend varRef "expr list"
               | StmntSortSend varRef "expr list"
               | StmntRecv varRef "recvArg list"
               | StmntRndRecv varRef "recvArg list"
               | StmntRecvX varRef "recvArg list"
               | StmntRndRecvX varRef "recvArg list"
               | StmntAssign varRef expr
               | StmntIncr varRef
               | StmntDecr varRef
               | StmntElse
               | StmntBreak
               | StmntGoTo String.literal
               | StmntLabeled String.literal stmnt
               | StmntPrintF String.literal "expr list"
               | StmntPrintM String.literal
               | StmntRun (*name*) String.literal
                          (*args*) "expr list"
                          (*prio*) "integer option"
               | StmntAssert expr
               | StmntCond expr
               | StmntCall String.literal "varRef list"
        
  and step = StepStmnt stmnt (*unless*) "stmnt option"
           | StepDecl decl
           | StepXR "varRef list"
           | StepXS "varRef list"

datatype_new module = 
                  ProcType (*active*) "(integer option) option"
                           (*name*)   String.literal
                           (*decls*)  "decl list"
                           (*prio*)   "integer option"
                           (*prov*)   "expr option"
                           (*seq*)    "step list"
                | DProcType (*active*) "(integer option) option"
                            (*name*)   String.literal
                            (*decls*)  "decl list"
                            (*prio*)   "integer option"
                            (*prov*)   "expr option"
                            (*seq*)    "step list"
                | Init (*prio*) "integer option" "step list"
                | Never "step list"
                | Trace "step list"
                | NoTrace "step list"
                | Inline String.literal "String.literal list" "step list"
                | TypeDef String.literal "decl list"
                | MType "String.literal list"
                | ModuDecl decl
                | Ltl (*name*) String.literal (*formula*) String.literal

end
end