(*  Title:       Data refinement of representation of a file
    Authors:     Karen Zee <kkz@mit.edu> and Viktor Kuncak <vkuncak@mit.edu>
    Maintainer:  Karen Zee <kkz@mit.edu>
    License:     LGPL
*)

header "Data refinement of representation of a file"
theory FileRefinement imports Main CArrays ResizableArrays begin

text {*
  We describe a file at
  two levels of abstraction: an abstract file, represented as a resizable array, and
  a concrete file, represented using data blocks.
  We consider the following operations:
\begin{verbatim}
makeAFS     :: AFile
afsRead     :: "AFile => nat ~=> byte"
afsWrite    :: "AFile => nat => byte ~=> AFile"
afsFileSize :: "AFile => nat"
\end{verbatim}
*}

typedecl
  -- "unit of file content"
  byte
consts
  -- "value used for padding"
  fillByte :: byte

consts
  blockSize :: nat  -- "in bytes"
  numBlocks :: nat  -- "total number of blocks in the file system"
axioms
  nonZeroBlockSize: "0 < blockSize"
  nonZeroNumBlocks: "0 < numBlocks"

(* ------------------------------------------------------------ *)
subsection {* Abstract File *}

types
  AFile = "byte rArray" -- "abstract file is a resizable array of bytes"

constdefs
  makeAF :: AFile
  -- "initial file has size 0"
  "makeAF == (0, % index. fillByte)"

constdefs
  afSize :: "AFile => nat"
  -- "file size is the length of the resizable array"
  "afSize afile == fst afile"

constdefs
  afRead :: "AFile => nat ~=> byte"
  -- "reading from a file looks up the byte, reporting @{term None} if the index is out of file bounds"
  "afRead afile byteIndex == 
   if byteIndex < fst afile then Some ((snd afile) byteIndex) else None"

constdefs
  afWrite :: "AFile => nat => byte ~=> AFile"
  -- "writing to a file updates the file content and extends the file if there is enough space"
  "afWrite afile byteIndex value == 
   if byteIndex div blockSize < numBlocks then
     Some (raWrite afile byteIndex value fillByte)
   else None"

(* ------------------------------------------------------------ *)
subsection {* Concrete File *}

types
  Block = "byte cArray" -- "array of @{term blockSize} bytes"

record CFile =
  fileSize      :: nat -- "in bytes"
  nextFreeBlock :: nat -- "next block available for allocation"
  data          :: "Block cArray" -- "array of up to @{term numBlocks} blocks"

constdefs
  makeCF :: CFile
  -- "initial file has no allocated blocks"
  "makeCF ==
   (| fileSize      = 0,
      nextFreeBlock = 0,
      data          = makeCArray numBlocks (makeCArray blockSize fillByte)
   |)"

constdefs
  cfSize :: "CFile => nat"
  "cfSize cfile == fileSize cfile"


constdefs
  cfRead :: "CFile => nat ~=> byte"
  -- {* Looks up correct data block and reads its content,
        if byteIndex is within bounds, else returns None. *}
  "cfRead cfile byteIndex ==
   if byteIndex < fileSize cfile then 
     (let i = byteIndex div blockSize in 
       (let j = byteIndex mod blockSize in
         Some (readCArray (readCArray (data cfile) i) j)))
   else None"

subsubsection {* Writing File *}

text {* We first present some auxiliary operations. *}

constdefs
  cfWriteNoExtend :: "CFile => nat => byte => CFile"
  -- {* Writing to a file when
        @{term byteIndex} is within bounds. *}
  "cfWriteNoExtend cfile byteIndex value ==
   let i = byteIndex div blockSize in
     let j = byteIndex mod blockSize in
       let block = readCArray (data cfile) i in
         cfile(| data := 
                 writeCArray (data cfile) i (writeCArray block j value) |)"

constdefs
  cfExtendFile :: "CFile => nat => CFile"
  -- {* Writing to a file when
        @{term byteIndex} is out of bounds.  Involves
        allocating a new block. *}
  "cfExtendFile cfile byteIndex ==
     cfile(| fileSize := Suc byteIndex,
             nextFreeBlock := Suc (byteIndex div blockSize) |)"

text {* The main file write operation. *}

constdefs
  cfWrite :: "CFile => nat => byte ~=> CFile"
  -- {* Writes the file at byte location byteIndex, automatically extending
   the file to that byte location if byteIndex is not within bounds.  *}
  "cfWrite cfile byteIndex value ==
     if byteIndex div blockSize < numBlocks then
       if byteIndex < fileSize cfile then
         Some (cfWriteNoExtend cfile byteIndex value)
       else
         Some (cfWriteNoExtend (cfExtendFile cfile byteIndex) byteIndex value)
     else None"

(* ---------------------------------------------------------------*)
subsection {* Reachability Invariants for Concrete File *}

constdefs
  nextFreeBlockInvariant :: "CFile => bool"
  "nextFreeBlockInvariant state ==
   (fileSize state + blockSize - 1) div blockSize = nextFreeBlock state"

constdefs
  unallocatedBlocksInvariant :: "CFile => bool"
  -- {* This invariant of the implementation is needed to prove
   writeExtendCorrect. It says that any unallocated block contains
   fillByte's. *}
  "unallocatedBlocksInvariant state ==
   ALL blockNum i . 
     ~ blockNum < nextFreeBlock state & blockNum < numBlocks & i < blockSize 
     --> data state blockNum i = fillByte"

constdefs
  lastBlockInvariant :: "CFile => bool"
  "lastBlockInvariant state ==
   ALL index .
     ~ index < fileSize state & nextFreeBlock state = index div blockSize + 1
     --> data state (index div blockSize) (index mod blockSize) = fillByte"

constdefs
  reachabilityInvariant :: "CFile => bool"
  "reachabilityInvariant cfile == 
      nextFreeBlockInvariant cfile &
      unallocatedBlocksInvariant cfile &
      lastBlockInvariant cfile"

(* ---------------------------------------------------------------*)
subsection {* Initial File Satisfies Invariants *}

text {* We prove each invariant individually and then summarize. *}

lemma nextFreeBlockInvariant1:
  "nextFreeBlockInvariant makeCF"
apply (simp add: nextFreeBlockInvariant_def makeCF_def)
apply (simp add: nonZeroBlockSize)
done

lemma unallocatedBlocksInvariant1:
  "unallocatedBlocksInvariant makeCF"
apply (simp add: unallocatedBlocksInvariant_def makeCF_def)
apply (simp add: makeCArray_def)
done

lemma lastBlockInvariant1:
  "lastBlockInvariant makeCF"
by (simp add: lastBlockInvariant_def makeCF_def)

lemma makeCFpreserves: "reachabilityInvariant makeCF"
by (simp add: reachabilityInvariant_def
              nextFreeBlockInvariant1
              unallocatedBlocksInvariant1
              lastBlockInvariant1)

(* ---------------------------------------------------------------*)
subsection {* Properties of Concrete File Operations *}

lemma cfWriteNoExtendPreservesFileSize:
  "[| index < fileSize cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> 
   fileSize cfile2 = fileSize cfile1"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp add: cfWriteNoExtend_def Let_def)
apply force
done

lemma cfWriteExtendFileSize:
  "[| ~ index < fileSize cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> fileSize cfile2 = Suc index"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
done

lemma fileSizeIncreases:
  "cfWrite cfile1 index value = Some cfile2
   ==> fileSize cfile1 <= fileSize cfile2"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
apply force
done

lemma nextFreeBlockIncreases:
  "[| nextFreeBlockInvariant cfile1;
      cfWrite cfile1 index value = Some cfile2
   |] ==> nextFreeBlock cfile1 <= nextFreeBlock cfile2"
apply (simp add: cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply force
apply (simp add: nextFreeBlockInvariant_def)
apply auto
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (subgoal_tac "Suc (index div blockSize) = 
  (index + blockSize) div blockSize", simp)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) <= 
  (index + blockSize)", simp add: div_le_mono)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) < 
  (fileSize cfile1 + blockSize)", simp)
apply (simp_all add: div_add_self2 nonZeroBlockSize)
done


(* ---------------------------------------------------------------*)
subsection {* Concrete File Operations Preserve Invariants *}

text {* There is only one top-level concrete operation: write, and we
show that it preserves all reachability invariants. *}

lemma cfWritePreservesNextFreeBlockInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2
    |] ==> nextFreeBlockInvariant cfile2"
apply (simp add: reachabilityInvariant_def
                 cfWrite_def
                 nextFreeBlockInvariant_def)
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply auto
apply (simp add: div_add_self2 nonZeroBlockSize)
done

lemma modInequalityLemma:
  "(a::nat) ~= b & a mod c = b mod c ==> a div c ~= b div c"
apply auto
apply (insert mod_div_equality [of "a" "c"])
apply (insert mod_div_equality [of "b" "c"])
apply simp
done

lemma mod_round_lt:
  "[| 0 < (c::nat);
      a < b
   |] ==> a div c < (b + c - 1) div c"
apply (subgoal_tac "a <= b - 1")
apply (subgoal_tac "a div c <= (b - 1) div c")
apply (insert div_add_self2 [of c "b - 1"])
apply (simp)
apply (simp add: div_le_mono)
apply (insert less_Suc_eq_le [of a "b - 1"])
apply simp
done

lemma blockNumNELemma:
  "!!blockNum i.
       [| nextFreeBlockInvariant cfile1;
          cfile1
          (| data :=
               writeCArray (data cfile1) (byteIndex div blockSize)
                (writeCArray
                  (readCArray (data cfile1) (byteIndex div blockSize))
                  (byteIndex mod blockSize) value) |) =
          cfile2;
          ~ blockNum < nextFreeBlock cfile2; blockNum < numBlocks;
          i < blockSize; byteIndex div blockSize < numBlocks;
          byteIndex < fileSize cfile1 |]
       ==> blockNum ~= byteIndex div blockSize"
apply (simp add: nextFreeBlockInvariant_def)
apply (subgoal_tac "byteIndex div blockSize < nextFreeBlock cfile1")
apply force
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (insert mod_round_lt)
apply force
done

lemma cfWritePreservesUnallocatedBlocksInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2
    |] ==> unallocatedBlocksInvariant cfile2"
apply (simp add: reachabilityInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 <= nextFreeBlock cfile2")
apply (simp add: unallocatedBlocksInvariant_def cfWrite_def)
apply auto
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def cfExtendFile_def Let_def)
apply (simp_all add: writeCArray_def readCArray_def)
apply (subgoal_tac "blockNum ~= byteIndex div blockSize")
apply force
apply (simp add: blockNumNELemma)
apply (subgoal_tac "~ blockNum < nextFreeBlock cfile1")
apply (subgoal_tac "blockNum ~= byteIndex div blockSize")
apply auto
apply (simp add: nextFreeBlockIncreases)
done

lemma cfWritePreservesLastBlockInvariant:
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2 |] ==> 
    lastBlockInvariant cfile2"
apply (simp add: reachabilityInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 <= nextFreeBlock cfile2")
apply (simp add: cfWrite_def)
apply (simp (no_asm) add: lastBlockInvariant_def)
apply auto
apply (case_tac "byteIndex div blockSize < numBlocks", simp_all)
apply (case_tac "byteIndex < fileSize cfile1", simp_all)
apply (simp_all add: cfWriteNoExtend_def Let_def cfExtendFile_def)
apply (simp_all add: writeCArray_def readCArray_def)
apply (simp add: lastBlockInvariant_def)
apply (subgoal_tac "index ~= byteIndex")
apply (case_tac "index div blockSize ~= byteIndex div blockSize")
apply force
apply (subgoal_tac "index mod blockSize ~= byteIndex mod blockSize")
apply force
apply (insert modInequalityLemma)
apply force
apply force
apply (subgoal_tac "index ~= byteIndex")
apply (case_tac "index div blockSize ~= byteIndex div blockSize", simp_all)
apply force
apply (subgoal_tac "index mod blockSize ~= byteIndex mod blockSize")
apply (case_tac "nextFreeBlock cfile1 = Suc (index div blockSize)")
apply (subgoal_tac "~ index < fileSize cfile1");
apply (simp add: lastBlockInvariant_def)
apply auto
apply (simp add: unallocatedBlocksInvariant_def)
apply (erule_tac x="index div blockSize" in allE)
apply (erule_tac x="index mod blockSize" in allE)
apply (simp add: nonZeroBlockSize)
apply (insert modInequalityLemma)
apply auto
apply (simp add: nextFreeBlockIncreases)
done

text {* Final statement that all invariants are preserved. *}
lemma cfWritePreserves: 
   "[| reachabilityInvariant cfile1;
       cfWrite cfile1 byteIndex value = Some cfile2 |] ==> 
    reachabilityInvariant cfile2"
apply (simp (no_asm) add: reachabilityInvariant_def)
apply (simp add: cfWritePreservesNextFreeBlockInvariant)
apply (simp add: cfWritePreservesUnallocatedBlocksInvariant)
apply (simp add: cfWritePreservesLastBlockInvariant)
done

(* ---------------------------------------------------------------*)
subsection {* Commuting Diagrams for Simulation Relation *}

text {* Here we show correctness of file system operations. *}

(* ---------------------------------------------------------------*)
subsubsection {* Abstraction Function *}

constdefs
  abstFn :: "CFile => AFile"
  "abstFn cfile == (fileSize cfile, 
                    % index . case cfRead cfile index of
                                None       => fillByte
                              | Some value => value)"

consts
  oAbstFn :: "CFile option => AFile option"
  primrec "oAbstFn None = None"
          "oAbstFn (Some s) = Some (abstFn s)"

(* ---------------------------------------------------------------*)
subsubsection {* Creating a File *}

lemma makeCFCorrect: "abstFn makeCF = makeAF"
by (simp add: makeCF_def makeAF_def abstFn_def cfRead_def
    split add: bool.splits option.splits)

subsubsection {* File Size *}

lemma fileSizeCorrect:
  "cfSize cfile = afSize (abstFn cfile)"
by (simp add: cfSize_def afSize_def abstFn_def)

subsubsection {* Read Operation *}

lemma readCorrect:
  "cfRead cfile = afRead (abstFn cfile)"
apply (simp add: abstFn_def)
apply (rule ext)
apply (simp add: cfRead_def afRead_def Let_def)
done

subsubsection {* Write Operation *}

lemma writeNoExtendCorrect:
  "[| index < fileSize cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (simp add: abstFn_def afWrite_def raWrite_def Let_def cfWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (simp_all add: cfWriteNoExtend_def Let_def)
apply (rule ext)
apply (simp add: cfRead_def writeCArray_def readCArray_def Let_def)
apply (case_tac "indexa < fileSize cfile1", simp_all)
apply (case_tac "indexa = index", simp_all)
apply (case_tac "indexa mod blockSize = index mod blockSize", simp_all)
apply (subgoal_tac "indexa div blockSize ~= index div blockSize", simp_all)
apply (simp_all add: modInequalityLemma)
done

lemma writeExtendCorrect:
  "[| nextFreeBlockInvariant cfile1;
      unallocatedBlocksInvariant cfile1;
      lastBlockInvariant cfile1;
      ~ index < fileSize cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (insert nextFreeBlockIncreases [of cfile1 index "value" cfile2])
apply (simp add: abstFn_def afWrite_def raWrite_def Let_def)
apply (case_tac "~ index div blockSize < numBlocks",
  simp_all add: cfWrite_def cfWriteNoExtend_def cfExtendFile_def Let_def)
apply (rule ext)
apply (simp add: cfRead_def fillAndUpdate_def Let_def writeCArrayCorrect1)
apply (case_tac "indexa < fileSize cfile1", simp_all) (* 2 subgoals *)
apply (subgoal_tac "indexa ~= index", simp_all)
apply (case_tac "indexa div blockSize = index div blockSize") (* 3 subgoals *)
apply (case_tac "indexa mod blockSize = index mod blockSize",
  simp add: modInequalityLemma) (* 3 subgoals *)
apply (simp_all add: writeCArrayCorrect1 writeCArrayCorrect2) (* 1 subgoal *)
apply (case_tac "indexa < index", simp_all)
apply (case_tac "indexa div blockSize = index div blockSize") (* 2 subgoals *)
apply (case_tac "indexa mod blockSize = index mod blockSize",
  simp add: modInequalityLemma)
apply (simp_all add: readCArray_def writeCArray_def lastBlockInvariant_def)
apply (erule_tac x=indexa in allE, simp_all)
apply (case_tac "nextFreeBlock cfile1 = nextFreeBlock cfile2", simp_all)
apply (simp add: unallocatedBlocksInvariant_def)
apply (subgoal_tac "~ indexa div blockSize < nextFreeBlock cfile1", simp_all)
apply (subgoal_tac "indexa mod blockSize < blockSize", simp_all)
apply (insert nonZeroBlockSize)
apply force (* 1 subgoal *)
apply (simp add: unallocatedBlocksInvariant_def)
apply (case_tac "~ indexa div blockSize < nextFreeBlock cfile1", simp_all)
apply (subgoal_tac "indexa div blockSize < numBlocks", simp_all) 
  (* 2 subgoals *)
apply (subgoal_tac "indexa div blockSize <= index div blockSize", simp_all)
apply (simp add: div_le_mono) (* 1 subgoal *)
apply (subgoal_tac "nextFreeBlock cfile1 = Suc (indexa div blockSize)", simp)
apply (simp add: nextFreeBlockInvariant_def)
apply (subgoal_tac "nextFreeBlock cfile1 = 
  (fileSize cfile1 + blockSize - Suc 0) div blockSize", simp_all)
apply (subgoal_tac "(fileSize cfile1 + blockSize - Suc 0) div blockSize <=
  Suc (indexa div blockSize)", simp_all)
apply (subgoal_tac "Suc (indexa div blockSize) = 
  (indexa + blockSize) div blockSize", simp_all) (* 2 subgoals *)
apply (subgoal_tac "fileSize cfile1 + blockSize - Suc 0 <= indexa + blockSize",
  simp add: div_le_mono)
apply (insert diff_le_self [of "fileSize cfile1 + blockSize" "Suc 0"])
apply (subgoal_tac "fileSize cfile1 + blockSize <= indexa + blockSize")
 (* 3 subgoals *)
apply (insert le_trans [of "fileSize cfile1 + blockSize - Suc 0" 
  "fileSize cfile1 + blockSize" _], simp) (* 2 subgoals *)
apply force (* 1 subgoal *)
apply (simp add: div_add_self2)
done

lemma writeSucceedCorrect:
  "[| nextFreeBlockInvariant cfile1;
      unallocatedBlocksInvariant cfile1;
      lastBlockInvariant cfile1;
      Some cfile2 = cfWrite cfile1 index value
   |] ==> Some (abstFn cfile2) = afWrite (abstFn cfile1) index value"
apply (case_tac "index < fileSize cfile1")
apply (simp_all add: writeExtendCorrect writeNoExtendCorrect)
done

lemma writeFailCorrect:
  "cfWrite cfile1 index value = None ==> 
   afWrite (abstFn cfile1) index value = None"
apply (simp add: abstFn_def cfWrite_def afWrite_def)
apply (case_tac "index div blockSize < numBlocks", simp_all)
apply (case_tac "index < fileSize cfile1", simp_all)
done

lemma writeCorrect:
  "reachabilityInvariant cfile1 ==>
   oAbstFn (cfWrite cfile1 index value) = afWrite (abstFn cfile1) index value"
apply (simp add: reachabilityInvariant_def)
apply (case_tac "cfWrite cfile1 index value")
apply (simp add: writeFailCorrect)
apply (simp add: writeSucceedCorrect)
done

end
