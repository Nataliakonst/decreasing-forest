section \<open>theory_decr_forest\<close>
theory theory_decr_forest
imports Main
begin

text \<open> This theory defines a notion of graphs. A graph is a record that contains a set of nodes 
\<open>V\<close> and a set of edges VxV, where the values v are the unique vertex labels.\<close>

subsection \<open>Definitions\<close>
  text \<open>A graph is represented by a record.\<close>
  record ('v) graph =
    nodes :: "'v set" 
    edges :: "('v \<times> 'v) set"

  text \<open>In a valid graph, edges only go from nodes to nodes.\<close>
  locale valid_graph = 
    fixes G :: "('v) graph"
    assumes E_valid: "fst`edges G \<subseteq> nodes G"
                     "snd`edges G \<subseteq> nodes G"
  begin
    abbreviation "V \<equiv> nodes G"
    abbreviation "E \<equiv> edges G"

    lemma E_validD: assumes "(v,v')\<in>E"
      shows "v\<in>V" "v'\<in>V"
      apply -
      apply (rule subsetD[OF E_valid(1)])
      using assms apply force
      apply (rule subsetD[OF E_valid(2)])
      using assms apply force
      done
  end

subsection \<open>Basic operations on Graphs\<close>
  text \<open>The empty graph.\<close>
  definition empty where 
    "empty \<equiv> \<lparr> nodes = {}, edges = {} \<rparr>"
  text \<open>Adds a node to a graph.\<close>
  definition add_node where 
    "add_node v g \<equiv> \<lparr> nodes = insert v (nodes g), edges=edges g\<rparr>"
  text \<open>Deletes a node from a graph. Also deletes all adjacent edges.\<close>
  definition delete_node where "delete_node v g \<equiv> \<lparr> 
    nodes = nodes g - {v},   
    edges = edges g \<inter> (-{v})\<times>(-{v})
    \<rparr>"
  text \<open>Adds an edge to a graph, edges only go from smaller to larger vertex labels\<close>
  definition add_edge where "add_edge v  v' g \<equiv> \<lparr>
    nodes = {v,v'} \<union> nodes g,
    edges = (if v'>v then 
    insert (v,v') (edges g) else insert (v',v) (edges g))
    \<rparr>"
  text \<open>Deletes an edge from a graph.\<close>
  definition delete_edge where "delete_edge v v' g \<equiv> \<lparr>
    nodes = nodes g, 
    edges = edges g - {(v,v')} \<rparr>"
  text \<open>Now follow some simplification lemmas.\<close>
  lemma empty_valid[simp]: "valid_graph empty"
    unfolding empty_def by unfold_locales auto
  lemma add_node_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (add_node v g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding add_node_def 
      by unfold_locales (auto dest: E_validD)
  qed
  lemma delete_node_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (delete_node v g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding delete_node_def 
      by unfold_locales (auto dest: E_validD)
  qed
  lemma add_edge_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (add_edge v v' g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding add_edge_def
      by unfold_locales (auto dest: E_validD)
  qed
  lemma delete_edge_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (delete_edge v v' g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding delete_edge_def
      by unfold_locales (auto dest: E_validD)
  qed

  lemma nodes_empty[simp]: "nodes empty = {}" unfolding empty_def by simp
  lemma edges_empty[simp]: "edges empty = {}" unfolding empty_def by simp
  lemma nodes_add_node[simp]: "nodes (add_node v g) = insert v (nodes g)"
    by (simp add: add_node_def)
  lemma nodes_add_edge[simp]: 
    "nodes (add_edge v v' g) = insert v (insert v' (nodes g))"
    by (simp add: add_edge_def)
  lemma edges_add_edge[simp]: 
    "edges (add_edge v v' g) = (if v'>v then 
insert (v,v') (edges g) else insert (v',v) (edges g))"
    by (simp add: add_edge_def)
  lemma edges_add_node[simp]: 
    "edges (add_node v g) = edges g"
    by (simp add: add_node_def)

subsection \<open>Preliminary definitions\<close>
  text \<open>This function finds the connected component corresponding to the given vertex.\<close>
  definition "nodes_above g v \<equiv>{v} \<union> snd ` Set.filter (\<lambda>e. fst e = v) ((edges g)\<^sup>+)" 

  text \<open>The function puts a component into a tree and preserves the decreasing property.\<close>
  fun nodes_order :: " nat graph \<Rightarrow> nat \<Rightarrow> nat graph " where
     "nodes_order g x\<^sub>1 =  (let nodes\<^sub>1= nodes_above g 1 in
                           let nodes\<^sub>2= nodes_above g (x\<^sub>1+2) in
                            let max_comp\<^sub>1= Max(nodes\<^sub>1) in
                            let max_comp\<^sub>2= Max(nodes\<^sub>2) in 
                              (if max_comp\<^sub>1=max_comp\<^sub>2 then g else
                                (if max_comp\<^sub>1 > max_comp\<^sub>2 then 
                                    let st_p=Max(Set.filter (\<lambda>v. v<max_comp\<^sub>2) nodes\<^sub>1) in
                                    let end_p=Min(Set.filter (\<lambda>v. v>max_comp\<^sub>2) nodes\<^sub>1) in
                                    let g1= delete_edge st_p end_p g in
                                    let g2= add_edge st_p max_comp\<^sub>2 g1 in
                                    let g3=add_edge max_comp\<^sub>2 end_p g2 in g3
                                 else 
                                   add_edge max_comp\<^sub>1 max_comp\<^sub>2 g
                                 )
                               )
                            )" 

  text \<open>This is an additional function. Input:
    1. Order number of the current node that can be added to the graph 
    2. Order number of the previous node from branch1 (above 1) added to the graph
    3. Order number of the previous node from branch2 (above x1+2) added to the graph
    4. The current graph
    5. Number sequence to encode the graph

    How does the function work:
    I. If the sequence (input 5.) is empty, return current graph (input 4.)
    II. If the sequence is not empty and starts with a zero, add one to the order number of the 
    current node, delete the first number (0) from the sequence and call the function again
    III. If the sequence isn't empty and doesn't start with a 0, add the current node to the graph
    IIIa. If the sequence starts with a 1, add an edge to branch1 using input (2)
    IIIb.  If the sequence starts with a 2, add an edge to branch2 using input (3)\<close>
  fun enc_to_graph :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat graph \<Rightarrow> nat list \<Rightarrow> nat graph" where
     "enc_to_graph curr_v prev_v1 prev_v2 g Nil = g"
|    "enc_to_graph curr_v prev_v1 prev_v2 g (0#ns)  = 
      enc_to_graph (Suc curr_v) prev_v1 prev_v2 g ns "
|    "enc_to_graph curr_v prev_v1 prev_v2 g (x#ns) = (if x=1 then
      enc_to_graph (Suc curr_v) curr_v prev_v2 (add_edge prev_v1 curr_v g) ns
      else (if curr_v=prev_v2 then enc_to_graph (Suc curr_v) prev_v1 curr_v g ns 
      else enc_to_graph (Suc curr_v) prev_v1 curr_v (add_edge prev_v2 curr_v g) ns
           )                                         )" 

  text \<open>Define f1 to be the start graph.\<close>
  definition "f1 \<equiv> \<lparr>nodes = {1::nat}, edges = {}\<rparr>"

 text \<open>This is the inverse encoding function. Input:
    1.x1
    2. number sequence to encode into a graph 
    How does the function work:
    I.delete the last number since it only gives information about the number of trees in the graph
    but distinguish between cases in dependence of this last value
    II. take first x1 numbers and build the first graph part with enc_to_graph
    III. add the node x1+2 to the graph
    IV. delete x1 first numbers and build the second part with the rest 
    V(0). if the last encoding value was 0, output tree2
    V(1)(2).if the last encoding value was 1 and there are 2's in the encoding,
            connect two branches into one component using the function nodes_order
    V(1)(1). if the encoding only has 0 and 1 in it, build further on tree1 \<close>
  fun encoding_to_graph :: "nat \<Rightarrow> nat list \<Rightarrow> nat graph" where
     "encoding_to_graph x1 l = (let code_l=butlast l in
                            let tree\<^sub>1 = enc_to_graph 2 1 (x1+2) f1 (take x1 (code_l)) in
                            let max\<^sub>1 = Max (nodes tree\<^sub>1) in
                            let tree\<^sub>2 = enc_to_graph (x1+3) max\<^sub>1 (x1+2) (add_node (x1+2) tree\<^sub>1) 
                                        (drop x1 code_l) in
                            if (last l=0) then tree\<^sub>2 else
                            if 2\<in>set(code_l) then (nodes_order tree\<^sub>2 x1 ) 
                             else  enc_to_graph (x1+3) (x1+2) (x1+2) (add_edge max\<^sub>1 (x1+2) tree\<^sub>1) 
                                   (drop (x1) code_l)  
                                    
                                )"



 text \<open>This is the main encoding function. Input:
      1. Graph g to be encoded
      2. x1
      3. 2 as the starting node
      4. x1+x2+2
      5. False as the starting value for branching
      How does the function work:
      I. For each x from 2 (input (3)) to x1+x2+2 (input (4)), check whether 
         the vertex is in the graph, and if so, above which leaf does it exist
      II. For the nodes above the vertex with label 1, add 1 to the encoding,For the nodes 
          above the vertex with label x1+2, add 2 to the encoding, change input (5) if 
          we found a vertex with 2 incoming edges. If the value is not on a vertex,
          add 0 to the encoding
      III.using the value (5), decide to put 1 or 0 for 1 or 2 connected components\<close>
 fun graph_to_encoding_impl :: "nat graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat list" where
    "graph_to_encoding_impl f x1 x 0 c = [if c then 1 else 0]"
|   "graph_to_encoding_impl f x1 x (Suc n) c = (let above_one = (1, x) \<in> (edges f)\<^sup>+ in
                                                let above_x1_2 = (x1+2, x) \<in> (edges f)\<^sup>* in
                                                (if x = x1 + 2 then
                                                  graph_to_encoding_impl f x1 (Suc x) n 
                                                  (above_one \<and> above_x1_2)
                                                 else (if x \<in> nodes f then 
                                                  (if above_one \<and> (c \<or> \<not> above_x1_2) then 1 else 2)
                                                       else 0)
                                                # graph_to_encoding_impl f x1 (Suc x) n 
                                                  (c \<or> above_one \<and> above_x1_2))
                                               )"
  text \<open>Add some computation simplifications.\<close>
  lemma in_rtrancl_code [code_unfold]:  "x \<in> rtrancl R \<longleftrightarrow> fst x = snd x \<or> x \<in> trancl R"
  by (metis prod.exhaust_sel rtrancl_eq_or_trancl)

  print_theorems
  definition "graph_to_encoding f x1 x2 \<equiv> graph_to_encoding_impl f x1 2 (x1+x2+1) False"

(* Examples Part 1
definition "graph_ex1 \<equiv>
  \<lparr>nodes = {1::nat,2,5,7},
   edges = {(1,2),(2,5),(5,7)}\<rparr>"
 
definition "graph_ex2 \<equiv>
  \<lparr>nodes = {1::nat,2,3,5,7},
   edges = {(1,2),(2,3),(3,7),(5,7)}\<rparr>"

definition "graph_ex3 \<equiv>
  \<lparr>nodes = {1::nat,4,5,6,7},
   edges = {(1,4),(4,6),(5,7)}\<rparr>"

definition x1:: nat where "x1=3"
definition x2:: nat where "x2=2"
value "graph_to_encoding graph_ex1 x1 x2"
value "graph_to_encoding graph_ex2 x1 x2"
value "graph_to_encoding graph_ex3 x1 x2"

Part 2:
definition "f2 \<equiv>
  \<lparr>nodes = {1::nat,2,5,6,7,8,10},
   edges = {(1,2),(2,7),(7,8),
            (5,6),(6,8),(8,10)}\<rparr>"

lemma "graph_to_encoding f2 3 5 = [1,0,0,2,1,2,0,1,1]" by eval

definition "f3 \<equiv>
  \<lparr>nodes = {1::nat,2,5,6,7,8,10},
   edges = {(1,2),(2,8),
            (5,6),(6,7),(7,8),(8,10)}\<rparr>"

definition "f4 \<equiv>
  \<lparr>nodes = {1::nat,2,5,6,7,8,10},
   edges = {(1,2),(2,7),
            (5,6),(6,8),(8,10)}\<rparr>"

definition "f6 \<equiv>
  \<lparr>nodes = {1::nat,4,5,7,8},
   edges = {(1,4),(4,5),(5,7),(7,8)}\<rparr>"

definition "f7 \<equiv>
  \<lparr>nodes = {1::nat,5,7,10},
   edges = {(1,10),(5,7),(7,10)}\<rparr>"

definition "f8 \<equiv>
  \<lparr>nodes = {1::nat,5,7,10},
   edges = {(1,5),(5,7),(7,10)}\<rparr>"


definition "f5 \<equiv>
  \<lparr>nodes = {1::nat,3,5,6,7,8,10},
   edges = {(1,3),(3,6),
            (5,6),(6,7),(7,8),(8,10)}\<rparr>"

definition "f9 \<equiv>
  \<lparr>nodes = {1::nat,5},
   edges = {}\<rparr>"

value "(encoding_to_graph 3 (graph_to_encoding f3 3 5)) =f3"
value "(encoding_to_graph 3 (graph_to_encoding f4 3 5)) =f4"
value "(encoding_to_graph 3 (graph_to_encoding f5 3 5)) =f5"
value "(encoding_to_graph 3 (graph_to_encoding f6 3 5)) =f6"
value "(encoding_to_graph 3 (graph_to_encoding f7 3 5)) =f7"
value "(encoding_to_graph 3 (graph_to_encoding f8 3 5)) =f8"
value "(encoding_to_graph 3 (graph_to_encoding f9 3 5)) =f9"*)


 text \<open>Define locales for the encoding and the forest to represent them canonically.\<close>
 locale encoding = 
   fixes L  :: "nat list"
   and   x1 :: "nat"
   and   x2 :: "nat"
 assumes L_valid: "length L = x1+x2+1"
                  "set (take x1 L) \<subseteq> {0,1} "
                  "set (drop x1 L) \<subseteq> {0,1,2}"
                  "set (drop (x1+x2) L) \<subseteq> {0,1}"

 text \<open>This is a function that finds the edges that are incident to the given vertex.\<close>
 definition edges_v :: "nat graph \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set" where
          " edges_v g v \<equiv> {e. e \<in> edges g \<and> (fst e = v \<or> snd e = v)}"

 locale forest = 
   fixes T  :: "nat graph"
   and   x1 :: "nat"
   and   x2 :: "nat"
 assumes Ed_valid: "x1+2 \<in> nodes T"
                   "\<forall> (v)\<in> fst`edges T. card(snd`(edges_v T v)-{v})<2"
                   "\<forall> (v)\<in> snd`edges T. card(fst`(edges_v T v)-{v})<3"
                   "\<forall> (v,v')\<in> edges T. ( v<v')"
                   "nodes T \<noteq> {}"
                   "edges T \<noteq> {}"
                   "Max (nodes T) < x1+x2+3"


 text \<open>This is a test section with a simplified theory. Its purpose is to define the direction of
the future research. A single tree with one leaf can be encoded as a set of its nodes. The encoding 
for such a tree is just a list of Bool values, True for "node in the graph" and False for "not". \<close>
definition "valid_tree S n \<equiv> (\<forall>x. x \<in> S \<longrightarrow> 0 < x \<and> x \<le> n)"
definition "valid_encoding B n \<equiv> length B = n \<and> set B \<subseteq> {True, False}"

 text \<open>Non-recursive definitions allow to use induction and prove some simple theorems.\<close>
fun tree_to_encoding :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool list" where
"tree_to_encoding x n S = map (\<lambda>i. i \<in> S) [x..<x+n]"

fun encoding_to_tree :: " nat \<Rightarrow> bool list \<Rightarrow> nat set" where
"encoding_to_tree n B = (\<lambda>i. i + n) ` {i. i < length B \<and> B ! i}"

text \<open>To show that two functions form a bijection, one should first check that the
outputs are well-defined.\<close>
lemma length_tree_to_encoding:
  "length (tree_to_encoding x n S) = n"
  by (induct x n S rule: tree_to_encoding.induct) auto

lemma encoding_members:
  "set (tree_to_encoding x n S) \<subseteq> {True, False}"
  by (induct x n S rule: tree_to_encoding.induct) auto

lemma valid_tree_to_valid_encoding: 
  "valid_encoding (tree_to_encoding x n S) n"
  unfolding valid_encoding_def
  using encoding_members length_tree_to_encoding by auto

lemma valid_encoding_to_valid_tree_aux:
  "encoding_to_tree n B \<subseteq> {n..<n + length B}"
  by (induction n B rule: encoding_to_tree.induct)
     (auto simp: valid_encoding_def valid_tree_def)

lemma valid_encoding_to_valid_tree:
  "valid_encoding B n \<Longrightarrow> valid_tree (encoding_to_tree 1 B ) n"
  using valid_encoding_to_valid_tree_aux unfolding valid_encoding_def valid_tree_def
  by force

end
