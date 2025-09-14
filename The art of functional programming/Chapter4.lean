def longest_string (xs : List String) : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: y :: rest =>
    if x.length >= y.length then
      longest_string (x :: rest)
    else
      longest_string (y :: rest)

#eval longest_string ["a", "ab", "abc", "abcd"]
#eval longest_string ["a"]
#eval longest_string []

def concat (delimiter : String) (strs : List String) : String :=
  match strs with
  | [] => ""
  | [x] => x
  | x :: xs => x ++ delimiter ++ concat delimiter xs

#eval concat ", " ["apple", "banana", "cherry"]

inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | branch : BinaryTree α -> α → BinaryTree α → BinaryTree α

def bintree_length (tree : BinaryTree α) : Nat :=
  match tree with
  | BinaryTree.leaf => 0
  | BinaryTree.branch left _ right =>
    1 + max (bintree_length left)  (bintree_length right)


#eval bintree_length (BinaryTree.branch (BinaryTree.branch BinaryTree.leaf 2 BinaryTree.leaf) 1 (BinaryTree.branch (BinaryTree.branch BinaryTree.leaf 4 BinaryTree.leaf) 3 (BinaryTree.branch BinaryTree.leaf 5 BinaryTree.leaf)))
