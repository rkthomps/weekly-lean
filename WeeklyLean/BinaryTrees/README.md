
# Binary Trees

Consider the following definition of a tree: 
```
inductive Tree (α : Type) where
  | mt
  | node (data: α) (l: Tree α) (r: Tree α)
```

## Challenge 1
- Define what it means for this tree to be a binary tree. You can use either a function or an inductively defined proposition. 
- Define a function `bInsert` that a new element into the binary tree. 
- Prove that given any binary tree, and any new element, inserting the element into the tree with `bInsert` results in a binary tree.  

## Challenge 2
- Prove that flattening a binary tree using a pre-order traversal results in a sorted list. 

## Challenge 3
- Prove that inserting the elements from a sorted list into an empty tree with `bInsert` results in a tree whose height is equal to the length of the list. 