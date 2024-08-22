structure Bag where
  numBlackBalls: Nat
  numWhiteBalls: Nat
deriving Repr

inductive Step : Bag → Bag → Prop where
| ww_w (w: Nat) (b: Nat) : w >= 2 →
         b >= 0 →
         Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b, numWhiteBalls := w - 1}
| wb_b (w: Nat) (b: Nat) : w >= 1 →
         b >= 1 →
          Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b , numWhiteBalls := w - 1}
| bb_w (w: Nat) (b: Nat) : w >= 0 →
         b >= 2 →
          Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b - 2, numWhiteBalls := w + 1}

inductive StepStar: Bag → Bag → Prop where
| refl : StepStar s s
| step : Step s1 s2 → StepStar s2 s3 → StepStar s1 s3

def numBalls (b: Bag) : Nat :=
  b.numBlackBalls + b.numWhiteBalls

def isFinalState (s: Bag) : Prop :=
  s.numBlackBalls + s.numWhiteBalls = 1

def isValid (b: Bag) : Prop :=
  numBalls b > 0

theorem sizeDecreases :
  ∀ s1: Bag, ∀ s2: Bag,
  numBalls s1 > 1 ->
  Step s1 s2 ->
  numBalls s2 = (numBalls s1) - 1 := by
    intros s1 s2 Hsize Hstep
    cases Hstep with
    | ww_w w b Hw Hb => simp [numBalls]
                        omega
    | wb_b w b Hw Hb => simp [numBalls]
                        omega
    | bb_w w b Hw Hb => simp [numBalls]
                        omega

theorem finalStateCannotStep (finalState: Bag) :
  isFinalState finalState -> ¬ exists s : Bag, Step finalState s := by
    intros Hfinal Hexists
    cases Hexists with
    | intro s Hstep => cases Hstep with
      | ww_w w b Hw Hb => simp [isFinalState] at Hfinal
                          omega
      | wb_b w b Hw Hb => simp [isFinalState] at Hfinal
                          omega
      | bb_w w b Hw Hb => simp [isFinalState] at Hfinal
                          omega

theorem progress (state: Bag) :
  isValid state →
  ¬ isFinalState state ->
    ∃ s : Bag, Step state s := by
  intros Hvalid HnonFinal
  simp [isValid, numBalls] at Hvalid
  simp [isFinalState] at HnonFinal
  have HmoreThanOneBall: state.numBlackBalls + state.numWhiteBalls > 1 := by
    simp [numBalls]
    omega

  have Hcondition: state.numWhiteBalls >= 2 ∨ ¬ state.numWhiteBalls >= 2 := by
    apply Decidable.em
  cases Hcondition with
  -- numWhiteBalls >= 2
  | inl Hw =>
    exists {numBlackBalls := state.numBlackBalls, numWhiteBalls := state.numWhiteBalls - 1}
    apply Step.ww_w <;> omega
  -- numWhiteBalls < 2
  | inr Hw =>
  have Hcondition': state.numBlackBalls >= 2 ∨ ¬ state.numBlackBalls >= 2 := by
    apply Decidable.em
  cases Hcondition' with
  -- numBlackBalls >= 2
  | inl Hb =>
    exists {numBlackBalls := state.numBlackBalls - 2, numWhiteBalls := state.numWhiteBalls + 1}
    apply Step.bb_w <;> omega
  -- numBlackBalls < 2
  | inr Hb =>
    exists {numBlackBalls := state.numBlackBalls, numWhiteBalls := state.numWhiteBalls - 1}
    apply Step.wb_b <;> omega



-- induction on size
-- if size is 0, then it's a contradiction as we can't have a bag with 0 balls
-- if size is 1, then it must be final
-- if size is greater than 1, then we can apply one step rule
theorem terminates :
  ∀ nb: Nat, ∀ start: Bag,
  numBalls start = nb →
  isValid start →
  ∃ finish: Bag, ∃ stepStar: StepStar start finish,
    isFinalState finish := by
    intro numBalls
    cases numBalls
    -- numBalls = 0: contradiction
    case zero => intros start HnumBalls Hvalid; simp [isValid, numBalls] at *; omega
    case succ n =>
    induction n
    -- numBalls = 1: final state, finish = start
    case zero =>
      simp [isFinalState]
      intros start HnumBalls Hvalid
      simp [isValid, numBalls] at *
      exists start
      constructor
      . constructor
      . omega
    -- numBalls > 1: apply one step then induct
    case succ n' IH =>
    simp [isFinalState]
    simp at IH
    intros start HnumBalls Hvalid
    simp [isValid, numBalls] at *
    have HnonFinal: ¬ isFinalState start := by
      intro Hfinal
      simp [isFinalState] at Hfinal
      omega

    -- there exists a state s that can be reached from start
    have HstepExists: ∃ s : Bag, Step start s := by
      apply progress
      . simp [isValid, numBalls]; omega
      . assumption

    have HmoreThanOneBall: numBalls start > 1 := by
      simp [numBalls]
      omega


    cases HstepExists; case intro s Hstep =>
    -- build a step star using Hstep.
    -- start -Hstep-> s -Hstepstar-> finish
    -- since for every s, there exists a finish, we can use this to build a finish
    have H1 : numBalls s = numBalls start - 1 := by
      apply sizeDecreases start s HmoreThanOneBall Hstep

    simp [numBalls] at H1
    have HsSize: n' + 1 = s.numBlackBalls + s.numWhiteBalls := by omega

    have HfinishExists: ∃ finish: Bag, StepStar s finish ∧ isFinalState finish
      := by apply IH s <;> omega

    cases HfinishExists with
    | intro finish' Hfinish' =>

    simp [isFinalState] at Hfinish'
    cases Hfinish' with
    | intro Hstepstar Hfinal =>

    exists finish'
    constructor
    . apply StepStar.step Hstep Hstepstar
    . assumption

theorem evenBlackStepsToWhite (start: Bag) (ending: Bag) :
  start.numBlackBalls % 2 = 0 →
  StepStar start ending →
  isFinalState ending ->
  ending.numBlackBalls = 0 && ending.numWhiteBalls = 1 := by
    intros Heven Hstepstar Hfinal
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    induction Hstepstar
    case refl next => simp [isFinalState] at Hfinal; omega
    case step s1 s2 s3 S SS IH =>
      have H: s2.numBlackBalls % 2 = 0 := by cases S with
        | ww_w w b Hw Hb  => apply Heven
        | wb_b w b Hw Hb  => apply Heven
        | bb_w w b Hw Hb  => simp [Bag.numBlackBalls] at *; omega
      apply IH H Hfinal

theorem oddBlackStepsToBlack (start: Bag) :
  start.numBlackBalls % 2 = 1 →
  StepStar start ending ->
  isFinalState ending ->
  ending.numBlackBalls = 1 && ending.numWhiteBalls = 0 := by
    intros Hodd Hstepstar Hfinal
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    simp [isFinalState] at Hfinal
    induction Hstepstar
    case refl => omega
    case step s1 s2 s3 S SS IH =>
      have H: s2.numBlackBalls % 2 = 1 := by cases S with
        | ww_w w b Hw Hb  => simp [Bag.numBlackBalls] at Hodd
                             simp [Bag.numBlackBalls]
                             assumption
        | wb_b w b Hw Hb  => simp [Bag.numBlackBalls] at Hodd
                             simp [Bag.numBlackBalls]
                             assumption
        | bb_w w b Hw Hb  => simp [Bag.numBlackBalls] at Hodd
                             simp [Bag.numBlackBalls]
                             omega
      apply IH H Hfinal
