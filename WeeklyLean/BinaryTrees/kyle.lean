
namespace Kyle

inductive Tree (α : Type) where
  | mt
  | node (data: α) (l: Tree α) (r: Tree α)


inductive Tree.all (p : α → Prop) : Tree α → Prop where
  | mt_all : Tree.mt.all p
  | cons_all (l r d):
      l.all p ->
      r.all p -> (p d) ->
      (Tree.node d l r).all p


inductive Tree.sorted: Tree Nat -> Prop where
  | mt_sorted: Tree.mt.sorted
  | cons_sorted (data l r):
    l.sorted → r.sorted →
    l.all (λ x => x ≤ data) →
    r.all (λ x => data < x) → (Tree.node data l r).sorted


def Tree.insert : Nat -> Tree Nat -> Tree Nat
  | n, .mt => (.node n .mt .mt)
  | n, (.node data l r) => if (n ≤ data)
    then .node data (insert n l) r
    else .node data l (insert n r)


def Tree.height : Tree Nat -> Nat
  | .mt         => 0
  | .node _ l r =>
    if l.height < r.height
    then 1 + r.height
    else 1 + l.height


def Tree.size : Tree α → Nat
  | .mt => 0
  | .node _ l r => 1 + l.size + r.size


inductive List (α : Type) where
  | mt
  | cons (data: α) (rst: List α)

def List.len: (l: List α) -> Nat
  | .mt => 0
  | cons _ xs => 1 + xs.len

def List.append: (l1: List α) -> (l2: List α) -> List α
  | mt, l2 => l2
  | cons h l1', l2 => cons h (l1'.append l2)


def Tree.flatten : Tree Nat -> List Nat
  | Tree.mt => List.mt
  | Tree.node d l r => l.flatten.append (List.cons d r.flatten)

inductive List.all (p: α -> Prop): List α → Prop where
  | mt_all: mt.all p
  | cons_all (x xs):
    (p x) ->
    xs.all p ->
    (cons x xs).all p


inductive List.sorted: List Nat -> Prop where
  | mt_sorted: mt.sorted
  | cons_sorted (x xs):
    xs.all (λ a => x ≤ a) ->
    xs.sorted ->
    (cons x xs).sorted


def Tree.add_list: Tree Nat -> List Nat -> Tree Nat
  | t, List.mt => t
  | t, List.cons x xs => (t.add_list xs).insert x


def List.rev: List α -> List α
  | .mt => .mt
  | .cons x xs => (rev xs).append (cons x .mt)


theorem all_new: forall (t: Tree Nat) p n,
  p n ->
  t.all p ->
  (t.insert n).all p := by
  intros t p n H1 H2
  induction n, t using Tree.insert.induct with
  | case1 n =>
    simp[Tree.insert]; apply Tree.all.cons_all <;> assumption
  | case2 n data l r h ih =>
    simp[Tree.insert, h]; apply Tree.all.cons_all
    . apply ih <;> cases H2 <;> assumption
    . cases H2 <;> assumption
    . cases H2 <;> assumption
  | case3 n data l r h ih =>
    simp[Tree.insert, h]; apply Tree.all.cons_all
    . cases H2 <;> assumption
    . apply ih <;> cases H2 <;> assumption
    . cases H2 <;> assumption


theorem insert_sorted: forall (n: Nat) (t: Tree Nat),
  t.sorted → (t.insert n).sorted := by
  intros n t H
  induction n, t using Tree.insert.induct with
  | case1 _ =>
    simp[Tree.insert]; repeat constructor
  | case2 _ _ _ _ h ih =>
    simp[Tree.insert, h]
    apply Tree.sorted.cons_sorted
    . apply ih; cases H; assumption
    . cases H; assumption
    . cases H; apply all_new <;> assumption
    . cases H; assumption
  | case3 _ _ _ _ h ih =>
    simp[Tree.insert, h]; apply Tree.sorted.cons_sorted
    . cases H <;> assumption
    . apply ih; cases H <;> assumption
    . cases H; assumption
    . cases H; apply all_new;
      . exact Nat.gt_of_not_le h
      . assumption


theorem all_app_elim: forall (l1 l2: List Nat) (p: Nat -> Prop),
  (l1.append l2).all p -> l1.all p ∧ l2.all p := by
  intros l1 l2 p h
  induction l1 with
  | mt =>
    constructor
    constructor
    simp[List.append] at h; assumption
  | cons l ls ih =>
    constructor
    simp[List.append] at h; apply List.all.cons_all
    . cases h <;> assumption
    . cases h with
      | cons_all _ _ _ h_app =>
        simp[h_app] at ih; cases ih; assumption
    . simp[List.append] at h; cases h with
      | cons_all _ _ _ h_app =>
      simp[h_app] at ih; cases ih; assumption


theorem all_app_intro : forall (l1 l2: List Nat) (p: Nat -> Prop),
  l1.all p → l2.all p → (l1.append l2).all p := by
  intros l1 l2 p h1 h2
  induction l1 with
  | mt => simp[List.append]; assumption
  | cons l ls ih =>
    simp[List.append]; apply List.all.cons_all;
    . cases h1; assumption
    . apply ih; cases h1; assumption


theorem even_less: forall (l: List Nat) (x1 x2: Nat),
  x1 <= x2 ->
  l.all (λ x => x2 <= x) ->
  l.all (λ x => x1 <= x) := by
  intros l x1 x2 h1 h2
  induction l with
  | mt => constructor
  | cons l ls' ih =>
    apply List.all.cons_all
    . cases h2 with
      | cons_all _ _ h_x2l h_all =>
        exact Nat.le_trans h1 h_x2l
    . apply ih; cases h2; assumption


theorem all_lt_imp_all_le: forall (l: List Nat) (d: Nat),
  l.all (λ x => d < x) -> l.all (λ x => d ≤ x) := by
  intros l d h
  induction l with
  | mt => constructor
  | cons l ls ih =>
    apply List.all.cons_all
    . cases h with
      | cons_all _ _ hlt => omega
    . apply ih; cases h; assumption



theorem app_sorted: forall (l1 l2: List Nat) (d: Nat),
  l1.sorted ->
  l2.sorted ->
  l1.all (λ x => x ≤ d) ->
  l2.all (λ x => d < x) ->
  (l1.append (List.cons d l2)).sorted := by
  intros l1 l2 d H1 H2 H3 H4
  induction l1 with
  | mt =>
    simp[List.append];
    apply List.sorted.cons_sorted;
    apply all_lt_imp_all_le; assumption; assumption
  | cons l ls ih =>
    simp[List.append]
    apply List.sorted.cons_sorted
    . apply all_app_intro
      . cases H1; assumption
      . cases H3 with
        | cons_all _ _ h_ld h_all =>
          cases H1 with
          | cons_sorted _ _ _ h_sorted =>
            apply List.all.cons_all
            . assumption
            . apply even_less l2 l d
              . assumption
              . apply all_lt_imp_all_le; assumption
    . apply ih
      . cases H1; assumption
      . cases H3; assumption


theorem all_equiv: forall (t: Tree Nat) (p: Nat -> Prop),
  t.all p -> t.flatten.all p := by
  intros t p H
  induction t with
  | mt => constructor
  | node d l r lih rih =>
    simp[Tree.flatten]; apply all_app_intro
    apply lih; cases H; assumption
    apply List.all.cons_all
    . cases H; assumption
    . apply rih; cases H; assumption


theorem flatten_sorted: forall (t : Tree Nat), t.sorted -> t.flatten.sorted := by
  intros t H ; induction t with
  | mt => simp[Tree.flatten]; constructor
  | node d l r lih rih =>
    simp[Tree.flatten]; apply app_sorted
    . apply lih; cases H; assumption
    . apply rih; cases H; assumption
    . cases H; apply all_equiv; assumption
    . cases H; apply all_equiv; assumption


theorem add_list_single: forall (t: Tree Nat) (x: Nat),
  t.insert x = t.add_list (List.cons x List.mt) := by
  intros t x
  simp[Tree.add_list]


theorem app_mt_r: forall (l: List α), l.append .mt = l := by
  intros l; induction l with
  | mt => simp[List.append]
  | cons x xs ih => simp[List.append]; assumption


theorem add_list_app: forall (t: Tree Nat) (l1 l2: List Nat),
  (t.add_list l1).add_list l2 = t.add_list (l2.append l1) := by
  intros t l1 l2
  induction l2 with
    | mt => simp[Tree.add_list, List.append]
    | cons x xs ih => simp[Tree.add_list]; rw [ih]


inductive Tree.is_left_chain: Tree α -> Prop where
  | mt_left: Tree.mt.is_left_chain
  | node_left (d l r):
    r = .mt ->
    l.is_left_chain ->
    (Tree.node d l r).is_left_chain


theorem left_chain_height: forall (t: Tree Nat),
  t.is_left_chain → t.size = t.height := by
  intros t H
  induction t with
  | mt => simp[Tree.size, Tree.height]
  | node d l r lih _ =>
    simp[Tree.size, Tree.height]
    cases H with
    | node_left _ _ _ h_mt h_left =>
      have h_height: (r.height = 0) := by
        rw [h_mt]; simp[Tree.height]
      rw [h_height]
      have h_lheight: ¬ (l.height < 0) := by
        exact Nat.not_lt_zero l.height
      simp[h_lheight]
      rw [h_mt]; simp[Tree.size]; rw [lih]
      assumption



theorem insert_add_one: forall (t: Tree Nat) (n: Nat),
  (t.insert n).size = t.size + 1 := by
  intros t n
  induction n, t using Tree.insert.induct with
  | case1 => simp[Tree.insert, Tree.size]
  | case2 n d l r h ih =>
    simp[Tree.insert, Tree.size, h]
    rw [ih]
    omega
  | case3 n d l r h ih =>
    simp[Tree.insert, Tree.size, h]
    rw [ih]
    omega


theorem cons_len_add_one: forall (l: List α) (n: α),
  (List.cons n l).len = l.len + 1 := by
  intros l n
  simp[List.len]; exact Nat.add_comm 1 l.len

theorem add_list_size: forall (t: Tree Nat) (l: List Nat),
  (t.add_list l).size = t.size + l.len := by
  intros t l
  induction l with
  | mt => simp[Tree.add_list, List.len]
  | cons x xs ih =>
    simp[Tree.add_list, insert_add_one]
    rw[ih]
    rw[cons_len_add_one]
    exact rfl


theorem insert_le_preserves_left_chain: forall (n: Nat) (t: Tree Nat),
  t.is_left_chain →
  t.all (λ x => n ≤ x) →
  (t.insert n).is_left_chain := by
  intros n t H1 H2
  induction n, t using Tree.insert.induct with
  | case1 n =>
    simp[Tree.insert]
    apply Tree.is_left_chain.node_left
    . simp
    . assumption
  | case2 n d l r h ih =>
    simp[Tree.insert, h]
    cases H1 with
    | node_left _ _ _ hmt hl =>
      rw[hmt]
      apply Tree.is_left_chain.node_left
      simp
      apply ih; assumption
      cases H2; assumption
  | case3 n d l r h _ =>
    simp[Tree.insert, h]
    cases H2 with
    | cons_all _ _ _ _ _ hd => omega


theorem add_list_all: forall (l: List Nat) (p: Nat → Prop),
  l.all p → (Tree.mt.add_list l).all p := by
  intros l p H
  induction l with
  | mt => simp[Tree.add_list]; constructor
  | cons x xs ih =>
    simp[Tree.add_list]
    apply all_new
    cases H; assumption
    apply ih
    cases H; assumption



theorem insert_sorted_is_left_chain: forall (l: List Nat),
  l.sorted → (Tree.mt.add_list l).is_left_chain := by
  intros l H
  induction l with
  | mt => simp[Tree.add_list]; constructor
  | cons l ls ih =>
    simp[Tree.add_list]
    cases H with
    | cons_sorted _ _ hall hsort =>
      apply insert_le_preserves_left_chain
      apply ih; assumption
      apply add_list_all; assumption



theorem sorted_insert_all_height: forall (l: List Nat),
  l.sorted -> (Tree.mt.add_list l).height = l.len := by
  intros l H
  generalize ht: (Tree.mt.add_list l) = t
  have h_left := insert_sorted_is_left_chain l H
  simp[ht] at h_left
  have h_height := left_chain_height t h_left
  rw [<- h_height]
  rw[<- ht]
  rw [add_list_size]
  simp[Tree.size]
