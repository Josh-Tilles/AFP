(*  Title:      Jinja/JVM/JVMState.thy
    ID:         $Id: JVMState.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* 
  \chapter{Jinja Virtual Machine}\label{cha:jvm}
  \isaheader{State of the JVM} 
*}

theory JVMState imports Objects begin

section {* Frame Stack *}

types 
  pc = nat

  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc"
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

section {* Runtime State *}
types
  jvm_state = "addr option \<times> heap \<times> frame list"  
  -- "exception flag, heap, frames"
  
end
