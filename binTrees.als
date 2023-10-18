// CISC/CMPE 422/835
module BinTrees

sig Val {}

sig Node {
   leftChild : lone Node,
   rightChild : lone Node,
   val : Val
}

sig BinTree {
   root : lone Node
}

fun nodes[b : BinTree] : set Node {
   (b.root).*(leftChild + rightChild)
}

pred isLeaf[n : Node] {
   no n.leftChild && no n.rightChild
}

fact Facts {
   // no cycles
   all b : BinTree | no n : nodes[b] | n in n.^(leftChild + rightChild)
   // at most one parent
   all b : BinTree | all n : nodes[b] | lone n.~(leftChild + rightChild)
   // all nodes belong to at least one tree
   Node in (BinTree.root).*(leftChild + rightChild)
   // left child iff right child
   all b : BinTree | all n : nodes[b] | some n.leftChild iff some n.rightChild
   // children are different
   all b : BinTree | all n : nodes[b] | !isLeaf[n] => (n.leftChild != n.rightChild)
   // balanced
   all b : BinTree | # (b.root.leftChild).*(leftChild + rightChild) = # (b.root.rightChild).*(leftChild + rightChild)
}
 
pred show {
   #BinTree = 2
   #Node = 6
}

run show for 8

        
