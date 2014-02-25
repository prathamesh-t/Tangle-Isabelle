theory Component
imports Tangles
begin
(*Hi,
     I remembered that Isabelle/Isar users guide says that Isabelle has relations R as well as their transitive closures. This is the main step in globailisation. So the following simpler approach can give components:

(1) Create a datatype strand (with elements Str_Cup, ..., Str_Over_first, ...)

(2) For each block we get a list of strands recursively.

(3) We get functions from the list of Strands to domains and codomains

(4) Now inductively define the set of components: 
(a) For a block, this is the set of strands (may be wrapped in some new type)
(b) When we attach a block, we get an equivalence relation by taking the closure of identifications. *)
datatype strand = Str_vert|Str_over|Str_under|Str_cup|Str_cap

primrec brick_strand ::"brick \<Rightarrow> strand list"
where
 "brick_strand vert = [Str_vert]"
| "brick_strand over = [Str_over,Str_under]"
| "brick_strand under = [Str_under,Str_over]"
| "brick_strand cup = [Str_cup]"
| "brick_strand cap = [Str_cap]"

primrec block_strand::"block \<Rightarrow> strand list"
where
"block_strand (cement x) = (brick_strand x)"|
"block_strand (x#xs) =  ((brick_strand x)@(block_strand xs))"

primrec block_position::"block \<Rightarrow> nat"
where
"block_position (cement x) = 0"|
"block_position (cons x xs) = 1+(block_position xs)"

primrec wall_position::"walls \<Rightarrow> nat"
where
"wall_position (basic x) = 0"|
"wall_position (prod x xs) = (1+(wall_position xs))"
 

primrec block_location::"block \<Rightarrow> (brick \<times> nat)"
where
"block_position (cement x) = (x, 0)"|
"block_position (cons x xs) = (x,1+(block_position xs))"



end
