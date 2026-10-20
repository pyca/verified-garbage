module
public import VerifiedGarbage.Impl.Bignum.X86_64
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # Fixed-length masked signature output -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

abbrev copyMaskedByte : List Instr :=
  [.movzx8 .rax (at0 .rsi), .alu .and .rax (.reg .r8), .store8 (at0 .rdx) .rax,
    .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

theorem masked_byte (b : Byte) (valid : Bool) :
    (b.zeroExtend 64 &&& mask valid).setWidth 8 = if valid then b else 0 := by
  cases valid <;> simp [mask, BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le]
  exact BitVec.and_allOnes

structure CopyMaskedInv (s : State) (src out : Addr) (n j : Nat) (valid : Bool) (t : State) : Prop where
  keep : Keep [.rax, .rsi, .rdx, .rcx] s t
  rsi : t.gpr .rsi = src + BitVec.ofNat 64 j
  rdx : t.gpr .rdx = out + BitVec.ofNat 64 j
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copyMasked_ok {s : State} {src out : Addr} {n : Nat} {valid : Bool}
    (hsi : s.gpr .rsi = src) (hdx : s.gpr .rdx = out) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (h8 : s.gpr .r8 = mask valid) (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block copyMaskedByte) .ne) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .rsi, .rdx, .rcx] s t := by
  refine WP.mono (wp_upto (a := 0) (N := n) h1 (CopyMaskedInv s src out n · valid) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j _ hj t ht
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.1, ht.keep.2.2]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.2]; exact hw j hj
  have ht8 := (ht.keep.gpr (show Reg.r8 ∉ _ by decide)).trans h8
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega))
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (if valid then s.mem (src + BitVec.ofNat 64 j) else (0 : Byte)) ∧
    u.gpr .rsi = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .rdx = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .rcx = BitVec.ofNat 64 (n - (j + 1)) ∧ u.zf = some (decide (j + 1 = n))) ?_ rfl)
    fun u ⟨⟨hum, husi, hudx, hucx, huz⟩, hku⟩ => ?_
  · unfold copyMaskedByte
    xrun [State.ea, at0, ht.rsi, ht.rdx, ht.rcx, ht8,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrd, hwr, masked_byte, hval,
      ofNat64_pred (show 1 ≤ n - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show n - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by rw [show n - j - 1 = n - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩
  · refine ⟨huz, (ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact ht.bytes i (by omega)
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact ht.frame x fun i hi => hx i (by omega)

end VG.Proof.Dsa.X86_64
