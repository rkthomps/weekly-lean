structure State where
  white: Nat
  black: Nat
deriving BEq

inductive step : State → State → Prop where
  | ww : w >= 2 →
         step ⟨w, b⟩ ⟨w - 1, b⟩

  | bw : w >= 1 →
         b >= 1 →
         step ⟨w, b⟩ ⟨w - 1, b⟩

  | bb : b >= 2 →
         step ⟨w, b⟩ ⟨w + 1, b - 2⟩

inductive trans_step : State → State → Prop where
  | refl : trans_step s s
  | step : step s1 s2 → trans_step s2 s3 → trans_step s1 s3

def odd (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k + 1

def even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

def even_final := ∀ s, even s.black → trans_step s ⟨1, 0⟩ ∨ s = ⟨0, 0⟩

def odd_final := ∀ s, odd s.black → trans_step s ⟨0, 1⟩

-- WellFounded

def invStep (s2 s1 : State) := step s1 s2

def State.measure (s : State) : Nat := s.white + s.black

theorem measure_decreases (h : step s1 s2) : s2.measure < s1.measure := by
  cases h <;> simp [State.measure] <;> omega

theorem wf_transfer
    (f : α -> β)
    (rβ : β → β → Prop)
    (H : Subrelation rα (fun a1 a2 => rβ (f a1) (f a2)))
    (Hf : WellFounded rβ) : WellFounded rα := by
  apply Subrelation.wf H
  apply InvImage.wf; assumption

theorem wf_inv_step : WellFounded invStep := by
  apply wf_transfer State.measure Nat.lt measure_decreases
  apply Nat.lt_wfRel.wf

-- Normalization

inductive final : State -> Prop where
  | white : final ⟨1, 0⟩
  | black : final ⟨0, 1⟩
  | none : final ⟨0, 0⟩

theorem progress : ∀ s1, final s1 ∨ (∃ s2, step s1 s2)  := by
  intro s1
  match s1 with
  | ⟨0, 0⟩ | ⟨0, 1⟩ | ⟨1, 0⟩ =>  apply Or.inl ; constructor
  | ⟨1, 1⟩ => apply Or.inr ; exists ⟨0, 1⟩  ; apply step.bw <;> simp_arith
  | ⟨w + 2, b⟩ => apply Or.inr ; exists ⟨w + 1, b⟩ ; apply step.ww ; simp_arith
  | ⟨w, b + 2⟩ =>  apply Or.inr; exists ⟨w + 1, b⟩ ; apply step.bb; simp_arith

def halts (s : State) := ∃ s', trans_step s s' ∧ final s'

theorem halts_step : step s1 s2 → halts s2 → halts s1 := by
  rintro hstep ⟨s', ⟨htrans, _⟩⟩
  exists s'
  apply And.intro
  · apply trans_step.step hstep htrans
  · assumption

theorem normalization : ∀ s, halts s := by
  intro s1
  apply WellFounded.induction wf_inv_step
  intros s2 ih
  rcases progress s2 with _ | ⟨_, hstep⟩
  · exists s2 ; apply And.intro
    · apply trans_step.refl
    · trivial
  · apply halts_step hstep
    apply ih
    assumption

-- Properties about step

theorem preservation_trans {P : State → Prop}: (∀ s1 s2, P s1 → step s1 s2 → P s2) → P s1 → trans_step s1 s2 → P s2 := by
  intros h hp hstep
  induction hstep with
  | refl => assumption
  | step hstep _ ih => apply ih ; apply h <;> assumption

theorem none_unreachable : ¬∃s, step s ⟨0, 0⟩ := by
  rintro ⟨s, hstep⟩
  match s with
  | ⟨0, 0⟩ | ⟨w + 1, b⟩ => cases hstep <;> contradiction -- why does dependent elimination fail?

theorem none_refl : trans_step s1 ⟨0, 0⟩ → s1 = ⟨0, 0⟩ := by
  intro hstep
  generalize heq: State.mk 0 0  = s2 at hstep
  induction hstep with
  | refl => rfl
  | @step s3 =>
    exfalso
    apply none_unreachable
    exists s3
    simp_all

-- Even

theorem Nat.even_n_even_n_minus_2: even n → even (n - 2) := by rintro ⟨k, _⟩; exists k - 1; omega
theorem Nat.even_n_plus_2_even_n : even (n + 2) → even n := by rintro ⟨k, _⟩; exists k - 1; omega
theorem Nat.one_not_even : ¬(even 1) := by intros heven ; cases heven ; omega

theorem even_preservation : ∀ s1 s2, even s1.black → step s1 s2 → even s2.black := by
  intros s1 s2 heven hstep
  match s1 with
  | ⟨0, 0⟩ | ⟨0, 1⟩ | ⟨1, 0⟩ | ⟨1, 1⟩ => cases hstep <;> trivial
  | ⟨w + 2, b⟩ => cases hstep <;> simp_all [Nat.even_n_even_n_minus_2]
  | ⟨w, b + 2⟩ => cases hstep <;> simp_all [Nat.even_n_plus_2_even_n]

theorem even_final_result : even_final := by
  intro s1 heven
  rcases normalization s1 with ⟨s2, ⟨hstep, _ | _ |_ ⟩⟩
  · apply Or.inl ; assumption
  · exfalso ; apply Nat.one_not_even ; simp [preservation_trans even_preservation heven hstep]
  · apply Or.inr ; apply none_refl ; assumption

-- Odd

theorem Nat.odd_n_odd_n_minus_2: n >= 2 → odd n → odd (n - 2) := by rintro _ ⟨k, _⟩; exists k - 1; omega
theorem Nat.odd_n_plus_2_odd_n: odd (n + 2) → odd n := by rintro ⟨k, _⟩; exists k - 1; omega
theorem Nat.zero_not_odd : ¬(odd 0) := by intros hodd; cases hodd; omega

theorem odd_preservation: ∀ s1 s2, odd s1.black → step s1 s2 → odd s2.black := by
  intros s1 s2 heven hstep
  match s1 with
  | ⟨0, 0⟩ | ⟨0, 1⟩ | ⟨1, 0⟩ | ⟨1, 1⟩ => cases hstep <;> trivial
  | ⟨w + 2, b⟩ => cases hstep <;> simp_all [Nat.odd_n_odd_n_minus_2]
  | ⟨w, b + 2⟩ => cases hstep <;> simp_all [Nat.odd_n_plus_2_odd_n]

theorem odd_final_result : odd_final := by
  intro s1 hodd
  rcases normalization s1 with ⟨s2, ⟨hstep, _ | _ | _⟩⟩
  · exfalso ; apply Nat.zero_not_odd ; simp [preservation_trans odd_preservation hodd hstep]
  · assumption
  · simp_all [none_refl hstep, Nat.zero_not_odd]
