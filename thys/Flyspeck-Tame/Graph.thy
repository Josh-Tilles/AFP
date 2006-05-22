(*  ID:         $Id: Graph.thy,v 1.1 2006-05-22 09:53:59 nipkow Exp $
    Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Graph *}

theory Graph
imports Rotation
begin

syntax (xsymbols)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" 10)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" 10)

subsection{* Notation *}

types vertex = "nat"

consts
 vertices :: "'a \<Rightarrow> vertex list"
 edges :: "'a \<Rightarrow> (vertex \<times> vertex) set" ("\<E>")

syntax "_Vertices" :: "'a \<Rightarrow> vertex set" ("\<V>")
translations "\<V> f" == "set(vertices f)"


subsection {* Faces *}

text {*
We represent faces by (distinct) lists of vertices and a face type.
*}

datatype facetype = Final | Nonfinal

datatype face = Face "(vertex list)"  facetype

consts final :: "'a \<Rightarrow> bool"
primrec
  "final (Face vs f) = (case f of Final \<Rightarrow> True | Nonfinal \<Rightarrow> False)"

consts type :: "'a \<Rightarrow> facetype"
primrec "type (Face vs f) = f"

primrec
  "vertices (Face vs f) = vs"

defs (overloaded) cong_face_def:
 "f\<^isub>1 \<cong> (f\<^isub>2::face) \<equiv> vertices f\<^isub>1 \<cong> vertices f\<^isub>2" 

text {* The following operation makes a face final. *}

constdefs setFinal :: "face \<Rightarrow> face"
  "setFinal f \<equiv> Face (vertices f) Final"


text {* The function @{text nextVertex} (written @{text "f \<bullet> v"}) is based on
@{text nextElem}, that returns the successor of an element in a list.  *}

consts nextElem :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
primrec
 "nextElem [] b x = b"
 "nextElem (a#as) b x =
    (if x=a then (case as of [] \<Rightarrow> b | (a'#as') \<Rightarrow> a') else nextElem as b x)"

constdefs nextVertex :: "face \<Rightarrow> vertex \<Rightarrow> vertex" (*<*) ("_ \<bullet>")(*>*) (* *)
 "f \<bullet> v \<equiv> let vs = vertices f in nextElem vs (hd vs) v"


text {* @{text nextVertices} is $n$-fold application of
@{text nextvertex}. *}

constdefs nextVertices :: "face \<Rightarrow> nat \<Rightarrow> vertex \<Rightarrow> vertex" (*<*)("_\<^bsup>_\<^esup> \<bullet> _")(*>*) (* *)
  "f\<^bsup>n\<^esup> \<bullet> v \<equiv> ((f \<bullet>)^n) v"

lemma nextV2: "f\<^bsup>2\<^esup>\<bullet>v = f\<bullet> (f\<bullet> v)"
by (simp add: nextVertices_def nat_number)

(*<*) defs edges_face_def: (*>*)
  "edges (f::face) \<equiv> {(a, f \<bullet> a)|a. a \<in> \<V> f}"


(*<*)consts op :: "'a \<Rightarrow> 'a" ("_\<^bsup>op\<^esup>" [1000] 999)  (*>*) (* *)

defs (*<*) op_vertices_def:(*>*) "(vs::vertex list)\<^bsup>op\<^esup> \<equiv> rev vs"
primrec "(Face vs f)\<^bsup>op\<^esup> = Face (rev vs) f"  (*<*)
lemma [simp]: "vertices ((f::face)\<^bsup>op\<^esup>) = (vertices f)\<^bsup>op\<^esup>"
  by (induct f) (simp add: op_vertices_def)
lemma [simp]: "xs \<noteq> [] \<Longrightarrow> hd (rev xs)= last xs"
  by(induct xs) simp_all
lemma [THEN eq_reflection, code unfold]: "f\<^bsup>op\<^esup>\<bullet>v = (if
      vertices f = [] then hd (vertices f)
      else (let vs = vertices f in nextElem (rev vs) (last vs) v))"
 by (simp add: nextVertex_def op_vertices_def) (*>*) (* *)

constdefs prevVertex :: "face \<Rightarrow> vertex \<Rightarrow> vertex" (*<*)("_\<^bsup>-1\<^esup> \<bullet>")(*>*) (* *)
  "f\<^bsup>-1\<^esup> \<bullet> v \<equiv> (let vs = vertices f in nextElem (rev vs) (last vs) v)"



syntax triangle :: "face \<Rightarrow> bool"
translations "triangle f" == "|vertices f| = 3"


subsection {* Graphs *}

datatype graph = Graph "(face list)" "nat" "face list list" "nat list"

consts faces :: "graph \<Rightarrow> face list"
primrec "faces (Graph fs n f h) = fs"

syntax "_Faces" :: "graph \<Rightarrow> face set" ("\<F>")
translations "\<F> g" == "set(faces g)"

consts countVertices :: "graph \<Rightarrow> nat"
primrec "countVertices (Graph fs n f h) = n"

primrec "vertices (Graph fs n f h) = [0 ..< n]"

lemma vertices_graph: "vertices g = [0 ..< countVertices g]"
by (induct g) simp

lemma in_vertices_graph[THEN eq_reflection, code unfold]:
  "v \<in> set (vertices g) = (v < countVertices g)"
by (simp add:vertices_graph)

lemma len_vertices_graph[THEN eq_reflection, code unfold]:
  "|vertices g| = countVertices g"
by (simp add:vertices_graph)


consts faceListAt :: "graph \<Rightarrow> face list list"
primrec
  "faceListAt (Graph fs n f h) = f"

constdefs facesAt :: "graph \<Rightarrow> vertex \<Rightarrow> face list"
 "facesAt g v \<equiv> if v \<in> set(vertices g) then faceListAt g ! v else []"

consts heights :: "graph \<Rightarrow> nat list"
primrec
  "heights (Graph fs n f h) = h"

constdefs height :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
  "height g v \<equiv> heights g ! v"

lemma graph_split:
  "g = Graph (faces g)
             (countVertices g)
             (faceListAt g)
             (heights g)"
  by (induct g) simp


constdefs graph :: "nat \<Rightarrow> graph"
  "graph n \<equiv>
    (let vs = [0 ..< n];
     fs = [ Face vs Final, Face (rev vs) Nonfinal]
     in (Graph fs n (replicate n fs) (replicate n 0)))"

subsection{* Operations on graphs *}

text {* final graph, final / nonfinal faces *}

constdefs finals :: "graph \<Rightarrow> face list"
  "finals g \<equiv> [f \<in> faces g. final f]"

constdefs nonFinals :: "graph \<Rightarrow> face list"
  "nonFinals g \<equiv> [f \<in> faces g. \<not> final f]"

constdefs countNonFinals :: "graph \<Rightarrow> nat"
  "countNonFinals g \<equiv> |nonFinals g|"

defs finalGraph_def: "final g \<equiv> (nonFinals g = [])"

lemma finalGraph_faces[simp]: "final g \<Longrightarrow> finals g = faces g"
 by (simp add: finalGraph_def finals_def nonFinals_def filter_compl1)

lemma finalGraph_face: "final g \<Longrightarrow> f \<in> set (faces g) \<Longrightarrow> final f"
  by (simp only: finalGraph_faces[symmetric]) (simp add: finals_def)


constdefs finalVertex :: "graph \<Rightarrow> vertex \<Rightarrow> bool"
  "finalVertex g v \<equiv> \<forall>f \<in> set(facesAt g v). final f"

lemma finalVertex_final_face[dest]:
  "finalVertex g v \<Longrightarrow> f \<in> set (facesAt g v) \<Longrightarrow> final f"
  by (auto simp add: finalVertex_def)




text {* counting faces *}

constdefs degree :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
  "degree g v \<equiv> |facesAt g v|"

constdefs tri :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
 "tri g v \<equiv> |[f: facesAt g v. final f \<and> |vertices f| = 3]|"

constdefs quad :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
 "quad g v \<equiv> |[f: facesAt g v. final f \<and> |vertices f| = 4]|"

constdefs except :: "graph \<Rightarrow> vertex \<Rightarrow> nat"
 "except g v \<equiv> |[f: facesAt g v. final f \<and> 5 \<le> |vertices f| ]|"

constdefs vertextype :: "graph \<Rightarrow> vertex \<Rightarrow> nat \<times> nat \<times> nat"
  "vertextype g v \<equiv> (tri g v, quad g v, except g v)"

lemma[simp]: "0 \<le> tri g v" by (simp add: tri_def)

lemma[simp]: "0 \<le> quad g v" by (simp add: quad_def)

lemma[simp]: "0 \<le> except g v" by (simp add: except_def)


constdefs exceptionalVertex :: "graph \<Rightarrow> vertex \<Rightarrow> bool"
  "exceptionalVertex g v \<equiv> except g v \<noteq> 0"

constdefs noExceptionals :: "graph \<Rightarrow> vertex set \<Rightarrow> bool"
  "noExceptionals g V \<equiv> (\<forall>v \<in> V. \<not> exceptionalVertex g v)"


text {* An edge $(a,b)$ is contained in face f,
  $b$ is the successor of $a$ in $f$. *}

defs edges_graph_def: (*>*)
 "edges (g::graph) \<equiv> \<Union>\<^bsub>f \<in> \<F> g\<^esub> edges f"

constdefs neighbors :: "graph \<Rightarrow> vertex \<Rightarrow> vertex list"
 "neighbors g v \<equiv> [f\<bullet>v. f \<in> facesAt g v]"


subsection {* Navigation in graphs *}

text {*
The function $s'$ permutating the faces at a vertex,
is implemeted by the function @{text nextFace}
*}

constdefs nextFace :: "graph \<times> vertex \<Rightarrow> face \<Rightarrow> face" (*<*) ("_ \<bullet>")(*>*)
(*<*) "p \<bullet> \<equiv> \<lambda>f. (let (g,v) = p; fs = (facesAt g v) in
   (case fs of [] \<Rightarrow> f
           | g#gs \<Rightarrow> nextElem fs (hd fs) f))"  (*>*)
(*<*) lemma nextFace_def: (*>*)

  "(g,v) \<bullet> f \<equiv> (let fs = (facesAt g v) in
   (case fs of [] \<Rightarrow> f
           | g#gs \<Rightarrow> nextElem fs (hd fs) f))"
(*<*) by (simp add: nextFace_def) (*>*)

(* Unused: *)
constdefs prevFace :: "graph \<times> vertex \<Rightarrow> face \<Rightarrow> face" (*<*) ("_\<^bsup>-1\<^esup> \<bullet>")(*>*)
(*<*) "p\<^bsup>-1\<^esup> \<bullet> \<equiv>
     \<lambda>f. (let (g,v) = p; fs = (facesAt g v) in
    (case fs of [] \<Rightarrow> f
           | g#gs \<Rightarrow> nextElem (rev fs) (last fs) f))"  (*>*)
(*<*) lemma prevFace_def: (*>*)

  "(g,v)\<^bsup>-1\<^esup> \<bullet> f \<equiv> (let fs = (facesAt g v) in
   (case fs of [] \<Rightarrow> f
           | g#gs \<Rightarrow> nextElem (rev fs) (last fs) f))"
(*<*) by (simp add: prevFace_def) (*>*)


(* precondition a b in f *)
constdefs directedLength :: "face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> nat"
  "directedLength f a b \<equiv>
  if a = b then 0 else |(between (vertices f) a b)| + 1"

end
