
import Init.Data.Random

inductive Ball where
  | White
  | Black

notation:max " ⚪ " => Ball.White
notation:max " ⚫️ " => Ball.Black

def p : Nat → Nat → Nat
  | 0, 0 => 0
  | n1, n2 => n1 + n2

def Ball.beq : (Ball → Ball → Bool)
  | ⚪, ⚪ => true
  | ⚪, ⚫️ => false
  | ⚫️, ⚪ => false
  | ⚫️, ⚫️ => true


instance: BEq Ball where
  beq := Ball.beq

def BallBag := List Ball


def placeBall: Nat → Ball → BallBag → BallBag
  | 0, b, bb              => b :: bb
  | _, b, []              => [b]
  | Nat.succ n, b, b'::bs => b' :: placeBall n b bs


def shuffleBag (g: StdGen): BallBag → BallBag
  | [] => []
  | b :: bs =>
    let (idx, g') := randNat g 0 (bs.length)
    placeBall idx b (shuffleBag g' bs)


def turn (g: StdGen): (BallBag → BallBag)
  | [] => []
  | [b] => [b]
  | ⚪ :: ⚪ :: r => shuffleBag g (⚪ :: r)
  | ⚪ :: ⚫️ :: r => shuffleBag g (⚫️ :: r)
  | ⚫️ :: ⚪ :: r => shuffleBag g (⚫️ :: r)
  | ⚫️ :: ⚫️ :: r => shuffleBag g (⚪ :: r)


theorem placeBallIncr: forall (i: Nat) (b: Ball) (bb: BallBag),
  (placeBall i b bb).length = bb.length + 1 := by
  intros i b bb
  induction i, b, bb using placeBall.induct with
  | case1 b bb => simp[placeBall]
  | case2 i b ih => simp[placeBall]
  | case3 i b b' bs ih => simp[placeBall]; apply ih


theorem shuffleBagLenPreserved: forall (bb: BallBag) (g: StdGen),
  (shuffleBag g bb).length = bb.length := by
  intros bb
  induction bb with
  | nil => simp[shuffleBag]
  | cons b bb' ih =>
    simp[shuffleBag, placeBallIncr, ih]


theorem turn_ge_2_dec: forall (g: StdGen) (b1 b2 : Ball) (r: BallBag),
  (turn g (b1 :: b2 :: r)).length < r.length + 1 + 1 := by
  intros g b1 b2 r
  induction r with
  | nil =>
    cases b1 <;> cases b2 <;>
    simp[turn, shuffleBag, placeBall, placeBallIncr]
  | cons rh rt ih => cases b1 <;> cases b2 <;> simp[turn, shuffleBagLenPreserved]


def game (g: StdGen): BallBag → Option Ball
  | []  => Option.none
  | [b] => b
  | b1 :: b2 :: r => game g (turn g (b1 :: b2 :: r))
termination_by b => List.length b
decreasing_by
  all_goals simp_wf
  apply turn_ge_2_dec


def num_blacks: BallBag → Nat
  | [] => 0
  | ⚪ :: r => num_blacks r
  | ⚫️ :: r => 1 + num_blacks r


theorem placeBlackIncr: forall (i: Nat) (b: Ball) (bb: BallBag),
  b = ⚫️ → num_blacks (placeBall i b bb) = 1 + num_blacks bb := by
  intros i b bb H
  induction i, b, bb using placeBall.induct with
  | case1 b bb => simp[H, placeBall, num_blacks]
  | case2 i b ih => simp[H, placeBall, num_blacks]
  | case3 i b b' bb ih =>
    cases b' <;>
    simp[H, placeBall, num_blacks] <;> rw[<- H] <;>
    apply ih <;> assumption


theorem placeBlackConst: forall (i: Nat) (b: Ball) (bb: BallBag),
  b = ⚪ → num_blacks (placeBall i b bb) = num_blacks bb := by
  intros i b bb H
  induction i, b, bb using placeBall.induct with
  | case1 b bb => simp[H, placeBall, num_blacks]
  | case2 i b ih => simp[H, placeBall, num_blacks]
  | case3 i b b' bb ih =>
    cases b' <;>
    simp[H, placeBall, num_blacks] <;> rw[<- H] <;>
    apply ih <;> assumption


theorem shufflePreservesNumBlacks: forall (bb: BallBag) (g: StdGen),
  num_blacks (shuffleBag g bb) = num_blacks bb := by
  intros bb
  induction bb with
  | nil => simp[shuffleBag]
  | cons b bb' ih =>
    intros g
    cases b <;> simp[shuffleBag]
    . rw [placeBlackConst]; apply ih; simp
    . rw [placeBlackIncr]; simp[num_blacks]; apply ih; simp


def even : Nat → Bool
  | 0 => true
  | 1 => false
  | Nat.succ (Nat.succ n) => even n


def EvenP (n: Nat) := even n = true


theorem turnPreservesBlackParity: forall (bb: BallBag) (g: StdGen),
  EvenP (num_blacks bb) = EvenP (num_blacks (turn g bb))
  | [] => by simp[turn]
  | [b] => by cases b <;> simp[turn]
  | ⚪ :: ⚪ :: r => by simp[turn, shufflePreservesNumBlacks, num_blacks]
  | ⚪ :: ⚫️ :: r => by simp[turn, shufflePreservesNumBlacks, num_blacks]
  | ⚫️ :: ⚪ :: r => by simp[turn, shufflePreservesNumBlacks, num_blacks]
  | ⚫️ :: ⚫️ :: r => by
    simp[turn, shufflePreservesNumBlacks, num_blacks, EvenP]
    generalize h_nb: (num_blacks r) = nb
    have H' : 1 + (1 + nb) = Nat.succ (Nat.succ nb) := by omega
    rw [H']; simp[EvenP, even]


def EvenBlackStart (bb: BallBag) := EvenP (num_blacks bb) ∧ 0 < bb.length
def OddBlackStart (bb: BallBag) := ¬ EvenP (num_blacks bb) ∧ 0 < bb.length


theorem zeroBlacksEndWhite : forall (bb: BallBag) (g: StdGen),
  0 < bb.length → num_blacks bb = 0 → game g bb = some ⚪  := by
  intros bb g H1 H2
  induction bb using game.induct with
  | g => assumption
  | case1 => contradiction
  | case2 b => cases b; simp[game]; simp[num_blacks] at H2
  | case3 b1 b2 r ih =>
    cases b1 <;> cases b2 <;> simp[num_blacks] at H2
    simp[game]; apply ih; simp[turn, shuffleBagLenPreserved]
    simp[turn, shufflePreservesNumBlacks, num_blacks, H2]
    omega; omega; omega


theorem evenTwoPlus : forall (n: Nat), even (1 + (1 + n)) = even n := by
  intros n
  have hs : 1 + (1 + n) = Nat.succ (Nat.succ n) := by omega
  rw [hs]; simp[even]


theorem end_white : forall (bb: BallBag) (g: StdGen),
  EvenBlackStart bb → game g bb = some ⚪ := by
  simp[EvenBlackStart]
  intros bb g H1 H2
  induction bb using game.induct with
  | g => assumption
  | case1 => contradiction
  | case2 b => cases b; simp[game]; simp[num_blacks, EvenP, even] at H1
  | case3 b1 b2 r ih =>
    cases b1 <;> cases b2 <;>
    simp[game] <;> apply ih <;>
    simp[turn, shufflePreservesNumBlacks, num_blacks, shuffleBagLenPreserved] <;>
    try assumption
    simp[EvenP, even] at *; rw[<- evenTwoPlus]; assumption



theorem end_black : forall (bb: BallBag) (g: StdGen),
  OddBlackStart bb → game g bb = some ⚫️ := by
  simp[OddBlackStart]
  intros bb g H1 H2
  induction bb using game.induct with
  | g => assumption
  | case1 => contradiction
  | case2 b => cases b; simp[EvenP, num_blacks, even] at H1; simp[game]
  | case3 b1 b2 r ih =>
    cases b1 <;> cases b2 <;>
    simp[game] <;> apply ih <;>
    simp[turn, shufflePreservesNumBlacks, num_blacks, shuffleBagLenPreserved] <;>
    try assumption
    simp[EvenP, even] at *; rw[<- evenTwoPlus]; assumption
