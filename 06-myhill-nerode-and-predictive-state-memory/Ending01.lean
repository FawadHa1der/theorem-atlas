module

public import Cslib.Computability.Languages.MyhillNerode

@[expose] public section

namespace CommonGround.Ending01

open Cslib Cslib.Automata Cslib.Automata.Acceptor

/-- The independent specification: the complete word ends in false,true (01). -/
def L01 : Language Bool := {w | ∃ u : List Bool, w = u ++ [false, true]}

/-- Literal three-state table, columns false(0), true(1):
    state 0: (1,0); state 1: (1,2); state 2: (1,0). -/
def transition01 (q : Fin 3) (symbol : Bool) : Fin 3 :=
  match q.val with
  | 0 => if symbol then 0 else 1
  | 1 => if symbol then 2 else 1
  | _ => if symbol then 0 else 1

/-- A native CSLib recognizer. -/
def M01 : DA.FinAcc (Fin 3) Bool where
  tr := transition01
  start := 0
  accept := {2}

/-- Inspect the last at most two symbols, keeping arbitrary earlier history. -/
def suffixState (w : List Bool) : Fin 3 :=
  match w.reverse with
  | false :: _ => 1
  | true :: false :: _ => 2
  | _ => 0

private theorem suffixState_append (w : List Bool) (symbol : Bool) :
    suffixState (w ++ [symbol]) = transition01 (suffixState w) symbol := by
  grind [suffixState, transition01, List.reverse_append]

private theorem reachedState_eq_suffixState (w : List Bool) :
    M01.mtr M01.start w = suffixState w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w symbol ih =>
    rw [FLTS.mtr_concat_eq, suffixState_append, ih]
    rfl

private theorem suffixState_accept_iff (w : List Bool) :
    suffixState w = 2 ↔ w ∈ L01 := by
  constructor
  · intro h
    unfold suffixState at h
    split at h <;> try norm_num at h
    rename_i tail heq
    refine ⟨tail.reverse, ?_⟩
    simpa only [List.reverse_reverse, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append] using
      congrArg List.reverse heq
  · rintro ⟨u, rfl⟩
    simp [suffixState, List.reverse_append]

/-- The table recognizes exactly the words ending in 01. -/
theorem ending01_recognizer_correct :
    Acceptor.language M01 = L01 := by
  ext w
  change M01.mtr M01.start w = 2 ↔ w ∈ L01
  simpa only [reachedState_eq_suffixState] using suffixState_accept_iff w

def witnessHistories : Set (List Bool) := {[], [false], [false, true]}

instance finiteWitnessHistories : Finite witnessHistories := by
  exact (((Set.finite_singleton ([false, true] : List Bool)).insert [false]).insert []).to_subtype

private theorem witnessHistories_card : Nat.card witnessHistories = 3 := by
  simp [witnessHistories]

private theorem empty_not_nerode_zero :
    ¬ (L01.NerodeCongruence).r [] [false] := by
  intro h
  simpa [← suffixState_accept_iff, suffixState] using h [true]

private theorem empty_not_nerode_zeroOne :
    ¬ (L01.NerodeCongruence).r [] [false, true] := by
  intro h
  simpa [← suffixState_accept_iff, suffixState] using h []

private theorem zero_not_nerode_zeroOne :
    ¬ (L01.NerodeCongruence).r [false] [false, true] := by
  intro h
  simpa [← suffixState_accept_iff, suffixState] using h []

private theorem witnessHistories_pairwise :
    witnessHistories.Pairwise (¬ (L01.NerodeCongruence).r · ·) := by
  grind [witnessHistories, Set.Pairwise, (L01.NerodeCongruence).iseqv.symm,
    empty_not_nerode_zero, empty_not_nerode_zeroOne, zero_not_nerode_zeroOne]

/-- Every finite native recognizer for L01 has at least three states, by the
    native dfa_num_state_ge theorem. -/
theorem ending01_requires_three_states
    {State : Type*} [Finite State] {M : DA.FinAcc State Bool}
    (hM : Acceptor.language M = L01) :
    3 ≤ Nat.card State := by
  simpa only [witnessHistories_card] using
    (_root_.Language.dfa_num_state_ge
      (l := L01) (ws := witnessHistories) (M := M)
      witnessHistories_pairwise hM)

end CommonGround.Ending01
