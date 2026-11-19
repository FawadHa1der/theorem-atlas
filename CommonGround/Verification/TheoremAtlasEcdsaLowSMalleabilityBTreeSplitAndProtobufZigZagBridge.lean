/-
  CommonGround/Verification/TheoremAtlasEcdsaLowSMalleabilityBTreeSplitAndProtobufZigZagBridge.lean

  Wave V278 · Suite #679:
  Cross-Domain Kernel Bridge Unifying:
  - Bitcoin `BIP-62` / Ethereum `EIP-2` `ECDSA` `(r, q - s)` Signature Malleability Involution
    (`1,210/1,210` Valid Twins over `q = 11`) vs. Canonical Low-`s` (`1 ≤ s ≤ 5`) Uniqueness (`flt` ↔ `cslib` ↔ `econlib`)
  - Bayer–McCreight (`1972`) `B-Tree` Proactive Full-Node Split (`(t-1)+1+(t-1) = 2t - 1`) &
    Exponential Fanout (`btreeMinKeys 64 3 = 8,191`) (`cslib` ↔ `apsp3sum`)
  - Protocol Buffers Signed `ZigZag` Bijection (`ℤ ↔ ℕ`, `zigZagEncode (-1) = 1`, `1`-Byte Varint)
    vs. Unsigned Two's-Complement `-1` (`10`-Byte Varint Blowup) (`cslib` ↔ `oai-codes`)

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Verification.TheoremAtlasEcdsaLowSMalleabilityBTreeSplitAndProtobufZigZagBridge

def invMod11 (a : Nat) : Nat :=
  (List.range 11).find? (fun x => (a * x) % 11 == 1) |>.getD 0

def ecXCoord11 (scalar : Nat) : Nat :=
  let t := scalar % 11; (t * t) % 11

def ecdsaVerifyX11 (z pubX r s : Nat) : Nat :=
  let sInv := invMod11 (s % 11)
  ecXCoord11 ((((z * sInv) % 11) + pubX * ((r * sInv) % 11)) % 11)

def isLowS11 (s : Nat) : Bool := 1 ≤ s && s ≤ 5

def btreeMinKeys (t : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | h + 2 => 2 * (t ^ (h + 1)) - 1

def zigZagEncode (z : Int) : Nat :=
  if z ≥ 0 then (2 * z).toNat else (-2 * z - 1).toNat

def zigZagDecode (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else -Int.ofNat (n / 2 + 1)

def varintByteLen : Nat → Nat → Nat
  | 0, _ => 10
  | fuel + 1, n => if n < 128 then 1 else 1 + varintByteLen fuel (n / 128)

/--
  **Bridge 1 (`flt` ↔ `cslib` ↔ `econlib`)**:
  Exhaustive `ECDSA` `(r, 11 - s)` verification equivalence across `Fin 11` vs. `BIP-62`/`EIP-2`
  canonical Low-`s` orbit uniqueness (`isLowS11 s != isLowS11 (11 - s)`).
-/
theorem ecdsa_low_s_canonical_vs_negated_malleability_bridge :
    (∀ s : Fin 11, s.val ≠ 0 → 11 - s.val ≠ s.val) ∧
    (∀ z r s : Fin 11, s.val ≠ 0 →
      ecdsaVerifyX11 z.val 3 r.val (11 - s.val) = ecdsaVerifyX11 z.val 3 r.val s.val) ∧
    (∀ s : Fin 11, s.val ≠ 0 → isLowS11 s.val != isLowS11 (11 - s.val)) := by
  decide

/--
  **Bridge 2 (`cslib` ↔ `apsp3sum`)**:
  Universal `B-Tree` full-node median split conservation (`(t-1)+1+(t-1) = 2t - 1`) and fanout
  capacity (`8,191` keys in `3` cache lines at `t = 64` vs. `3` on a chain).
-/
theorem btree_split_conservation_and_fanout_bridge (t : Nat) (ht : t ≥ 2) :
    (t - 1) + 1 + (t - 1) = 2 * t - 1 ∧
    btreeMinKeys 4 3 = 31 ∧
    btreeMinKeys 64 3 = 8191 := by
  exact ⟨by omega, by decide, by decide⟩

/--
  **Bridge 3 (`cslib` ↔ `oai-codes`)**:
  Universal Protobuf `ZigZag` bijection (`zigZagDecode (zigZagEncode z) = z`) + `1`-byte `-1`
  varint vs. `10`-byte raw two's-complement `-1`.
-/
theorem protobuf_zigzag_bijection_vs_varint_blowup_bridge (z : Int) :
    zigZagDecode (zigZagEncode z) = z ∧
    varintByteLen 12 (zigZagEncode (-1)) = 1 ∧
    varintByteLen 12 (2 ^ 64 - 1) = 10 := by
  refine ⟨?_, by decide, by decide⟩
  dsimp [zigZagEncode, zigZagDecode]
  by_cases hz : z ≥ 0
  · rw [if_pos hz]
    have hEven : (2 * z).toNat % 2 = 0 := by omega
    rw [if_pos hEven]; omega
  · rw [if_neg hz]
    have hOdd : (-2 * z - 1).toNat % 2 ≠ 0 := by omega
    rw [if_neg hOdd]; omega

/--
  **Master Triad Theorem (`Suite #679`)**:
  Unifies `BIP-62`/`EIP-2` `ECDSA` Low-`s` non-malleability, `B-Tree` proactive node splitting,
  and Protobuf `ZigZag` signed-integer serialization.
-/
theorem master_ecdsa_low_s_btree_and_zigzag_bridge
    (t : Nat) (ht : t ≥ 2) (z : Int) :
    (∀ s : Fin 11, s.val ≠ 0 → isLowS11 s.val != isLowS11 (11 - s.val)) ∧
    ((t - 1) + 1 + (t - 1) = 2 * t - 1) ∧
    zigZagDecode (zigZagEncode z) = z := by
  exact ⟨ecdsa_low_s_canonical_vs_negated_malleability_bridge.2.2,
         (btree_split_conservation_and_fanout_bridge t ht).1,
         (protobuf_zigzag_bijection_vs_varint_blowup_bridge z).1⟩

end CommonGround.Verification.TheoremAtlasEcdsaLowSMalleabilityBTreeSplitAndProtobufZigZagBridge
