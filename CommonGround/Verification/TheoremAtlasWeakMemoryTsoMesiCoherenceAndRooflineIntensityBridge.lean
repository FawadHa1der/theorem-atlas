/-
  Common Ground — Verification Bridge (`Suite #651` · Wave `V250`)
  Module: `CommonGround/Verification/TheoremAtlasWeakMemoryTsoMesiCoherenceAndRooflineIntensityBridge.lean`
  Toolchain: `leanprover/lean4:v4.33.0` · Zero `sorry`

  Cross-Domain Bridge (`cslib` ↔ `apsp3sum` ↔ `tc-probcomb` ↔ `econlib`):
  Unifies weak-memory fence ordering (`x86-TSO` Store-Buffering vs. `MFENCE`), `MESI` snooping
  cache-coherence `SWMR` state-machine invariants, and Williams–Waterman–Patterson `Roofline`
  convex piecewise-linear ridge saturation (`FlashAttention` `33×` HBM byte reduction → `5.317×`
  end-to-end Tensor-Core speedup).
-/

namespace CommonGround.Verification.TheoremAtlasWeakMemoryTsoMesiCoherenceAndRooflineIntensityBridge

/-! ## 1. `x86-TSO` Store-Buffer (`SB`) Litmus vs. `MFENCE` Sequential Consistency (`SC`) -/

def scSbInterleavings : List (Nat × Nat × Nat × Nat) :=
  [ (0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2),
    (1, 2, 0, 3), (1, 3, 0, 2), (2, 3, 0, 1) ]

def scSbReadPair (s : Nat × Nat × Nat × Nat) : Nat × Nat :=
  let (tW0, tR0, tW1, tR1) := s
  (if tW1 < tR0 then 1 else 0, if tW0 < tR1 then 1 else 0)

structure TsoCore2Machine where
  memX  : Nat
  memY  : Nat
  bufX0 : Option Nat
  bufY1 : Option Nat
  r0    : Nat
  r1    : Nat
  deriving DecidableEq, Repr

inductive TsoSbAct where
  | w0 | w1 | r0 | r1 | f0 | f1
  deriving DecidableEq, Repr

def stepTsoCore2 (m : TsoCore2Machine) (a : TsoSbAct) : TsoCore2Machine :=
  match a with
  | .w0 => { m with bufX0 := some 1 }
  | .w1 => { m with bufY1 := some 1 }
  | .r0 => { m with r0 := m.memY }
  | .r1 => { m with r1 := m.memX }
  | .f0 => match m.bufX0 with | some v => { m with memX := v, bufX0 := none } | none => m
  | .f1 => match m.bufY1 with | some v => { m with memY := v, bufY1 := none } | none => m

def execTsoCore2 (acts : List TsoSbAct) : TsoCore2Machine :=
  acts.foldl stepTsoCore2 { memX := 0, memY := 0, bufX0 := none, bufY1 := none, r0 := 9, r1 := 9 }

def mfenceCore0Slots20 : List (Nat × Nat × Nat) :=
  [ (0,1,2), (0,1,3), (0,1,4), (0,1,5),
    (0,2,3), (0,2,4), (0,2,5), (0,3,4), (0,3,5), (0,4,5),
    (1,2,3), (1,2,4), (1,2,5), (1,3,4), (1,3,5), (1,4,5),
    (2,3,4), (2,3,5), (2,4,5), (3,4,5) ]

def interleaveMfence (remSteps : Nat) (c0 : List Nat) (q0 q1 : List TsoSbAct) : List TsoSbAct :=
  match remSteps with
  | 0 => []
  | k + 1 =>
      let idx := 6 - (k + 1)
      if idx ∈ c0 then
        match q0 with | e :: es => e :: interleaveMfence k c0 es q1 | [] => interleaveMfence k c0 [] q1
      else
        match q1 with | e :: es => e :: interleaveMfence k c0 q0 es | [] => interleaveMfence k c0 q0 []

def evalMfenceSlot (s : Nat × Nat × Nat) : Nat × Nat :=
  let (a, b, c) := s
  let m := execTsoCore2 (interleaveMfence 6 [a, b, c] [.w0, .f0, .r0] [.w1, .f1, .r1])
  (m.r0, m.r1)

theorem tso_store_buffer_vs_mfence_dekker_safety :
    (scSbInterleavings.all (fun s => scSbReadPair s != (0, 0))) = true ∧
    (let unfenced := execTsoCore2 [.w0, .w1, .r0, .r1, .f0, .f1]
     (unfenced.r0, unfenced.r1) = (0, 0) ∧ (unfenced.memX, unfenced.memY) = (1, 1)) ∧
    mfenceCore0Slots20.length = 20 ∧
    (mfenceCore0Slots20.all (fun s => evalMfenceSlot s != (0, 0))) = true := by
  decide

/-! ## 2. `MESI` Cache-Coherence `SWMR` (`14 / 64` States, `126 / 126` Transitions) & `BusUpgr` Guard -/

inductive MesiLineState where
  | M | E | S | I
  deriving DecidableEq, Repr

def mesiAlphabet : List MesiLineState := [.M, .E, .S, .I]

def isExclusiveOrMod (t : MesiLineState) : Bool :=
  t == .M || t == .E

def swmrCoherent3 (a b c : MesiLineState) : Bool :=
  if isExclusiveOrMod a then b == .I && c == .I
  else if isExclusiveOrMod b then a == .I && c == .I
  else if isExclusiveOrMod c then a == .I && b == .I
  else true

def snoopDemote (t : MesiLineState) : MesiLineState :=
  if t == .I then .I else .S

def stepMesi3 (st : MesiLineState × MesiLineState × MesiLineState) (op : Fin 9) :
    MesiLineState × MesiLineState × MesiLineState :=
  let (s0, s1, s2) := st
  match op.val with
  | 0 => if s0 != .I then st else if s1 == .I && s2 == .I then (.E, .I, .I) else (.S, snoopDemote s1, snoopDemote s2)
  | 1 => if s1 != .I then st else if s0 == .I && s2 == .I then (.I, .E, .I) else (snoopDemote s0, .S, snoopDemote s2)
  | 2 => if s2 != .I then st else if s0 == .I && s1 == .I then (.I, .I, .E) else (snoopDemote s0, snoopDemote s1, .S)
  | 3 => (.M, .I, .I)
  | 4 => (.I, .M, .I)
  | 5 => (.I, .I, .M)
  | 6 => (.I, s1, s2)
  | 7 => (s0, .I, s2)
  | _ => (s0, s1, .I)

def allMesi64 : List (MesiLineState × MesiLineState × MesiLineState) :=
  mesiAlphabet.flatMap (fun a => mesiAlphabet.flatMap (fun b => mesiAlphabet.map (fun c => (a, b, c))))

def allOps9 : List (Fin 9) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
   ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩,
   ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]

theorem mesi_swmr_invariant_and_bus_upgr_guard :
    let valid := allMesi64.filter (fun (a, b, c) => swmrCoherent3 a b c)
    allMesi64.length = 64 ∧
    valid.length = 14 ∧
    (valid.all (fun st => allOps9.all (fun op =>
      let (u, v, w) := stepMesi3 st op
      swmrCoherent3 u v w))) = true ∧
    swmrCoherent3 .M .S .I = false := by
  decide

/-! ## 3. Williams–Waterman–Patterson `Roofline` Ridge & `FlashAttention` `5.317×` Tile-Fusion Witness -/

def rooflineCross (piPeak betaMem flopsW bytesQ : Nat) : Nat :=
  if bytesQ * piPeak ≤ betaMem * flopsW then bytesQ * piPeak else betaMem * flopsW

theorem roofline_ridge_iff (piPeak betaMem flopsW bytesQ : Nat) :
    rooflineCross piPeak betaMem flopsW bytesQ = bytesQ * piPeak ↔
      bytesQ * piPeak ≤ betaMem * flopsW := by
  unfold rooflineCross
  split <;> omega

/-- Master `Suite #651` Bridge Theorem unifying:
    (1) `x86-TSO` `SB` `(0,0)` Dekker mutual-exclusion failure vs. `SC` (`6/6`) and `MFENCE` (`20/20`),
    (2) `MESI` `SWMR` `14/64` reachable envelope & `126/126` inductive snooping invariance vs. `(M,S,I)`,
    (3) `Roofline` `H100` (`Π=990, β=3, I*=330`) `FlashAttention` (`33×` HBM byte cut → `5445/1024 ≈ 5.317×`
        Tensor-Core speedup over unfused `18.8%`-MFU HBM attention). -/
theorem master_weak_memory_tso_mesi_coherence_and_roofline_intensity_bridge :
    ((scSbInterleavings.all (fun s => scSbReadPair s != (0, 0))) = true ∧
     (let u := execTsoCore2 [.w0, .w1, .r0, .r1, .f0, .f1]; (u.r0, u.r1) = (0, 0)) ∧
     (mfenceCore0Slots20.all (fun s => evalMfenceSlot s != (0, 0))) = true) ∧
    ((allMesi64.filter (fun (a, b, c) => swmrCoherent3 a b c)).length = 14 ∧
     swmrCoherent3 .M .S .I = false) ∧
    (let w := 4 * 4096 * 4096 * 128
     let qUnf := 8 * 4096 * 4096 + 8 * 4096 * 128
     let qFus := 8 * 4096 * 128
     qUnf = 33 * qFus ∧
     qUnf * 990 > 3 * w ∧
     qFus * 990 ≤ 3 * w ∧
     1024 * (qUnf * rooflineCross 990 3 w qFus) = 5445 * (qFus * rooflineCross 990 3 w qUnf)) := by
  decide

end CommonGround.Verification.TheoremAtlasWeakMemoryTsoMesiCoherenceAndRooflineIntensityBridge
