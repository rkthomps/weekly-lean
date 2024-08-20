structure Bag where
  numBlackBalls: Int
  numWhiteBalls: Int

inductive Turn where
| ww_w
| wb_b
| bb_w

inductive Step : Bag → Bag → Prop where
| ww_w (w: Int) (b: Int) : w >= 2 →
         b >= 0 →
         Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b, numWhiteBalls := w - 1}
| wb_b (w: Int) (b: Int) : w >= 1 →
         b >= 1 →
          Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b , numWhiteBalls := w - 1}
| bb_w (w: Int) (b: Int) : w >= 0 →
         b >= 2 →
          Step
          {numBlackBalls := b, numWhiteBalls := w}
          {numBlackBalls := b - 2, numWhiteBalls := w + 1}

inductive StepStar: Bag → Bag → Prop where
| ending : s.numBlackBalls >= 0
  -> s.numWhiteBalls >= 0
  -> s.numBlackBalls + s.numWhiteBalls = 1
  -> StepStar s s
| step : Step s1 s2 → StepStar s2 s3 → StepStar s1 s3


theorem sizeDecreases (h: Step s1 s2) :
  s2.numBlackBalls + s2.numWhiteBalls
  = s1.numBlackBalls + s1.numWhiteBalls - 1 := by
  cases h
  case ww_w =>
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    omega
  case wb_b =>
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    omega
  case bb_w =>
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    omega


theorem evenBlackStepsToWhite (start: Bag) (ending: Bag) :
  start.numBlackBalls % 2 = 0 →
  StepStar start ending →
  ending.numBlackBalls = 0 && ending.numWhiteBalls = 1 := by
    intros Heven Hstepstar
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    induction Hstepstar
    case ending => omega
    case step s1 s2 s3 S SS IH =>
      have H: s2.numBlackBalls % 2 = 0 := by cases S with
        | ww_w w b Hw Hb  => apply Heven
        | wb_b w b Hw Hb  => apply Heven
        | bb_w w b Hw Hb  => simp [Bag.numBlackBalls] at Heven
                            simp [Bag.numBlackBalls]
                            assumption
      apply IH
      apply H




theorem oddBlackStepsToBlack (start: Bag) :
  start.numBlackBalls % 2 = 1 →
  StepStar start ending ->
  ending.numBlackBalls = 1 && ending.numWhiteBalls = 0 := by
    intros Hodd Hstepstar
    simp [Bag.numBlackBalls, Bag.numWhiteBalls]
    induction Hstepstar
    case ending => omega
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
                             assumption
      apply IH
      apply H
