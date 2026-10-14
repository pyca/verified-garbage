module

public import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Fixed-length masked signature output -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.WriteBytes (writeW8_apply)

abbrev copyMaskedByte : List Instr :=
  [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x8, .strb .x3 .x2 0,
    .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

theorem masked_byte (b : Byte) (valid : Bool) :
    (BitVec.ofNat 64 b.toNat &&& mask valid).setWidth 8 = if valid then b else 0 := by
  have hb := b.isLt
  cases valid
  · simp [mask]
  · rw [show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp only [↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

theorem byte_zext (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat]
  have := (m a).isLt
  simp
  omega

structure CopyMaskedInv (s : State) (src out : Addr) (j : Nat) (valid : Bool) (t : State) : Prop where
  keep : Keep [.x3, .x1, .x2, .x9] s t
  x1 : t.gpr .x1 = src + BitVec.ofNat 64 j
  x2 : t.gpr .x2 = out + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copyMasked_ok {s : State} {src out : Addr} {n : Nat} {valid : Bool}
    (hsi : s.gpr .x1 = src) (hdx : s.gpr .x2 = out) (hcx : s.gpr .x9 = BitVec.ofNat 64 n)
    (h8 : s.gpr .x8 = mask valid) (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block copyMaskedByte) (.nonzero .x .x9)) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x3, .x1, .x2, .x9] s t := by
  refine WP.mono (wp_countdown (N := n) h64 h1 (CopyMaskedInv s src out · valid) ?_
    ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx,
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩ hcx)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j hj t ht _
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.rd, ht.keep.wr]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.wr]; exact hw j hj
  have ht8 := (ht.keep.gpr .x8 (by decide)).trans h8
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega))
  have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
  refine WP.mono (WP.keep [.x3, .x1, .x2, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (if valid then s.mem (src + BitVec.ofNat 64 j) else (0 : Byte)) ∧
    u.gpr .x1 = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .x9 = t.gpr .x9 - BitVec.ofNat 64 1) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hum, husi, hudx, hucx⟩, hku⟩ => ?_
  · unfold copyMaskedByte
    brun [exec_ldrb' (show 0 < 4096 by decide), ht.x1, ht.x2, ht8, hrd, hwr, hw8, hval,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [byte_zext, masked_byte, hval]
  · refine ⟨⟨(ht.keep.trans hku).mono (by decide), husi, hudx, ?_, ?_⟩, hucx⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact ht.bytes i (by omega)
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact ht.frame x fun i hi => hx i (by omega)

end VG.Proof.Dsa.AArch64
