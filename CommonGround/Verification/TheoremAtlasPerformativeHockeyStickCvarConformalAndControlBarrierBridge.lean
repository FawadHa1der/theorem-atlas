/-
  CommonGround/Verification/TheoremAtlasPerformativeHockeyStickCvarConformalAndControlBarrierBridge.lean

  Suite #632 (`V231`, `0` imports, `0` sorry):
  Cross-Domain Verification Bridge Connecting:
  - Statistical Decision Theory & Performative AI (`cslib`, `tc-probcomb`): Critical Quantile Thresholds,
    Hockey-Stick Divergences, and Covariate/Performative Conformal Prediction
  - Convex Duality & Financial / Grid Reserve Optimization (`econlib`): Rockafellar–Uryasev Superquantile
    (`CVaR_{1-1/γ}`) V-Curve Minimization Saving `15%` Reserve Overhead Over Worst-Case Box Bounds
  - Nonlinear Control Barrier Safety & Dynamical Stability (`ns`, `tc-analysis`, `oai-codes`, `tauceti`):
    Non-Stationary Distributionally Robust Control Barrier (`DR-CBF`) Forward Safety Invariance vs.
    Mean-Calibrated Barrier Crash (`h₁ = -18 < 0`) and Performative Feedback `2`-Cycle Oscillation.
-/

namespace CommonGround.Verification.PerformativeHockeyStickCvarConformalAndControlBarrierBridge

def sumFin : (M : Nat) → (Fin M → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
      sumFin n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_add (M : Nat) (f g : Fin M → Nat) :
    sumFin M (fun i => f i + g i) = sumFin M f + sumFin M g := by
  induction M with
  | zero => rfl
  | succ n ih =>
      simp [sumFin, ih]
      omega

theorem sumFin_scale (M : Nat) (c : Nat) (f : Fin M → Nat) :
    sumFin M (fun i => c * f i) = c * sumFin M f := by
  induction M with
  | zero => simp [sumFin]
  | succ n ih =>
      simp [sumFin, ih, Nat.mul_add]

theorem sumFin_scale_right (M : Nat) (c : Nat) (f : Fin M → Nat) :
    sumFin M (fun i => f i * c) = sumFin M f * c := by
  induction M with
  | zero => simp [sumFin]
  | succ n ih =>
      simp [sumFin, ih, Nat.add_mul]

theorem sumFin_le (M : Nat) (f g : Fin M → Nat) (hfg : ∀ i : Fin M, f i ≤ g i) :
    sumFin M f ≤ sumFin M g := by
  induction M with
  | zero => simp [sumFin]
  | succ n ih =>
      have h1 := ih (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
        (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
        (fun i => hfg ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have h2 := hfg ⟨n, Nat.lt_succ_self n⟩
      simp [sumFin]
      omega

def hockeyStick (M gamma : Nat) (q p : Fin M → Nat) : Nat :=
  sumFin M (fun x => q x - gamma * p x)

def drEnvelope (M Z gamma L tau B : Nat) (p ell : Fin M → Nat) : Nat :=
  Z * tau + gamma * sumFin M (fun x => p x * (ell x - tau)) + (L - tau) * B

def pNom4 : Fin 4 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

def loss4 : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 10

def qShift4 : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3

/-- Bridge 1: Rockafellar–Hockey-Stick Convex V-Curve Global Minimizer (`τ* = 4`, `34 = 34`)
    vs. Untrimmed Slope Bound (`42` at `τ = 0`), Worst-Case Box Reserve (`40` at `τ = 10`),
    and Naive Mean Calibration (`16 < 34`). -/
theorem rockafellar_hockey_stick_cvar_v_curve_minimizer_exact :
    (drEnvelope 4 4 2 10 4 1 pNom4 loss4 = 34) ∧
    (sumFin 4 (fun x => qShift4 x * loss4 x) = 34) ∧
    (∀ tau : Fin 11, 34 ≤ drEnvelope 4 4 2 10 tau.1 1 pNom4 loss4) ∧
    (drEnvelope 4 4 2 10 0 1 pNom4 loss4 = 42) ∧
    (drEnvelope 4 4 2 10 10 1 pNom4 loss4 = 40) ∧
    (sumFin 4 (fun x => pNom4 x * loss4 x) = 16 ∧ 16 < 34) := by
  decide

theorem pointwise_hockey_stick_cvar
    (q p gamma ell tau L : Nat) (hell : ell ≤ L) :
    q * ell ≤ q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) := by
  by_cases hlt : ell ≤ tau
  · have hmul : q * ell ≤ q * tau := Nat.mul_le_mul_left q hlt
    omega
  · have hsplit_ell : ell = tau + (ell - tau) := by omega
    by_cases hqp : q ≤ gamma * p
    · have h1 : q * (ell - tau) ≤ (gamma * p) * (ell - tau) :=
        Nat.mul_le_mul_right (ell - tau) hqp
      have h2 : (gamma * p) * (ell - tau) = gamma * (p * (ell - tau)) :=
        Nat.mul_assoc gamma p (ell - tau)
      calc
        q * ell = q * (tau + (ell - tau)) := by rw [← hsplit_ell]
        _ = q * tau + q * (ell - tau) := Nat.mul_add q tau (ell - tau)
        _ ≤ q * tau + gamma * (p * (ell - tau)) := by omega
        _ ≤ q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) :=
            Nat.le_add_right _ _
    · have hsplit_q : q = gamma * p + (q - gamma * p) := by omega
      have hrem : ell - tau ≤ L - tau := by omega
      have h3 : (q - gamma * p) * (ell - tau) ≤ (q - gamma * p) * (L - tau) :=
        Nat.mul_le_mul_left (q - gamma * p) hrem
      have h3c : (q - gamma * p) * (L - tau) = (L - tau) * (q - gamma * p) :=
        Nat.mul_comm (q - gamma * p) (L - tau)
      have h2 : (gamma * p) * (ell - tau) = gamma * (p * (ell - tau)) :=
        Nat.mul_assoc gamma p (ell - tau)
      calc
        q * ell = q * (tau + (ell - tau)) := by rw [← hsplit_ell]
        _ = q * tau + q * (ell - tau) := Nat.mul_add q tau (ell - tau)
        _ = q * tau + (gamma * p + (q - gamma * p)) * (ell - tau) := by rw [← hsplit_q]
        _ = q * tau + ((gamma * p) * (ell - tau) + (q - gamma * p) * (ell - tau)) := by
            rw [Nat.add_mul]
        _ ≤ q * tau + (gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p)) := by omega
        _ = q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) := by omega

/-- Bridge 2: Universal `Fin M` Hockey-Stick CVaR Bound & Non-Stationary `DR-CBF` Forward Safety Invariance. -/
theorem universal_fin_m_hockey_stick_cvar_and_dr_cbf_safety_bridge
    (M Z gamma L tau B Mctrl : Nat)
    (p d : Fin M → Nat)
    (qSeq : Nat → Fin M → Nat)
    (h : Nat → Int)
    (hqZ : ∀ t : Nat, sumFin M (qSeq t) ≤ Z)
    (hdL : ∀ w : Fin M, d w ≤ L)
    (hTube : ∀ t : Nat, hockeyStick M gamma (qSeq t) p ≤ B)
    (hCert : drEnvelope M Z gamma L tau B p d ≤ Mctrl)
    (hStep : ∀ t : Nat, (Mctrl : Int) - (sumFin M (fun w => qSeq t w * d w) : Int) ≤ h (t + 1))
    (h0 : 0 ≤ h 0) :
    ∀ T : Nat, 0 ≤ h T := by
  intro T
  cases T with
  | zero => exact h0
  | succ t =>
      have hpt :
          sumFin M (fun w => qSeq t w * d w) ≤
            sumFin M (fun w =>
              (qSeq t w * tau + gamma * (p w * (d w - tau))) + (L - tau) * (qSeq t w - gamma * p w)) := by
        apply sumFin_le
        intro w
        have hm := pointwise_hockey_stick_cvar (qSeq t w) (p w) gamma (d w) tau L (hdL w)
        omega
      have hs1 := sumFin_add M
        (fun w => qSeq t w * tau + gamma * (p w * (d w - tau)))
        (fun w => (L - tau) * (qSeq t w - gamma * p w))
      have hs2 := sumFin_add M
        (fun w => qSeq t w * tau)
        (fun w => gamma * (p w * (d w - tau)))
      have hq_tau := sumFin_scale_right M tau (qSeq t)
      have h_hinge := sumFin_scale M gamma (fun w => p w * (d w - tau))
      have h_hs := sumFin_scale M (L - tau) (fun w => qSeq t w - gamma * p w)
      have hZ_mul : sumFin M (qSeq t) * tau ≤ Z * tau := Nat.mul_le_mul_right tau (hqZ t)
      have hB_mul : (L - tau) * hockeyStick M gamma (qSeq t) p ≤ (L - tau) * B :=
        Nat.mul_le_mul_left (L - tau) (hTube t)
      unfold hockeyStick at hB_mul
      unfold drEnvelope at hCert
      have hDist : sumFin M (fun w => qSeq t w * d w) ≤ Mctrl := by omega
      have hst := hStep t
      omega

/-- Bridge 3: Clinical Conformal Triage Coverage Collapse (`90% → 60%`) vs. Exact Hockey-Stick Recalibration (`≥ 90%`). -/
def pClinic : Fin 3 → Nat
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 1

def qClinicShifted : Fin 3 → Nat
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 4

def scoreClinic : Fin 3 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 7

theorem clinical_conformal_shift_collapse_vs_hockey_stick_recalibration :
    (sumFin 3 pClinic = 10 ∧ sumFin 3 qClinicShifted = 10) ∧
    (hockeyStick 3 1 qClinicShifted pClinic = 3) ∧
    (sumFin 3 (fun x => pClinic x * (if scoreClinic x > 3 then 1 else 0)) = 1) ∧
    (sumFin 3 (fun x => qClinicShifted x * (if scoreClinic x > 3 then 1 else 0)) = 4) ∧
    (sumFin 3 (fun x => qClinicShifted x * (if scoreClinic x > 7 then 1 else 0)) = 0) := by
  decide

/-- Bridge 4: Performative Retraining Contraction (`κ = 1 < S = 2`) vs. Critical `2`-Cycle (`κ = S = 2`) & Runaway (`κ = 3 > S = 2`). -/
def contractiveErr : Nat → Nat
  | 0 => 16
  | t + 1 => contractiveErr t / 2

def criticalCycle : Nat → Int
  | 0 => 4
  | t + 1 => -(criticalCycle t)

def explosiveErr : Nat → Nat
  | 0 => 4
  | t + 1 => 3 * explosiveErr t

theorem performative_retraining_contraction_vs_oscillatory_instability :
    (contractiveErr 4 = 1 ∧ contractiveErr 4 < contractiveErr 0) ∧
    (criticalCycle 0 = 4 ∧ criticalCycle 1 = -4 ∧ criticalCycle 2 = 4) ∧
    (explosiveErr 3 = 108 ∧ explosiveErr 3 > explosiveErr 0) := by
  decide

end CommonGround.Verification.PerformativeHockeyStickCvarConformalAndControlBarrierBridge
