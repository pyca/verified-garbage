module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Words
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
/-! # FFDH on x86-64: the complete masked scalar store -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Mask.lean`, which only this module imported.
section

/-! # FFDH on x86-64: mask a rejected scalar's output -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The masked prefix and unchanged remainder of a scalar buffer. -/
structure MaskInv (s₀ : State) (op : Addr) (len : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r11, .rcx] s₀ t
  ptr : t.gpr .r11 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (len - j)
  bytes : ∀ i < j, t.mem (off op i) = if c then s₀.mem (off op i) else 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem maskBody_ok {s : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = off op j)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len - j)) (hm : s.gpr .r15 = mask c)
    (hwr : InRegions s.wr (off op j) 1) :
    WP isa (.block maskBody) s fun t =>
      (t.mem = s.mem.writeW (off op j) (if c then s.mem (off op j) else (0 : Byte)) ∧
      t.gpr .r11 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
      t.zf = some (decide (j + 1 = len))) ∧ Keep [.rax, .r11, .rcx] s t := by
  have hrd : InRegions (s.rd ++ s.wr) (off op j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  have hmByte : ((s.mem (off op j)).setWidth 64 &&& mask c).setWidth 8 =
      if c then s.mem (off op j) else 0 := by
    cases c <;> simp [mask, BitVec.setWidth_and]
    exact BitVec.and_allOnes
  refine WP.keep _ ?_ rfl
  unfold maskBody
  xrun [State.ea, at0, hp, hcx, hm,
    show off op j + BitVec.ofInt 64 0 = off op j by simp, hrd, hwr, hmByte,
    ofNat64_pred (show 1 ≤ len - j by omega) (by omega),
    ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · rw [show len - j - 1 = len - (j + 1) by omega]
  · exact decide_eq_decide.mpr (by omega)

theorem maskStep_ok {s₀ t : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hm : s₀.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s₀.wr (off op i) 1) (h : MaskInv s₀ op len c j t) :
    WP isa (.block maskBody) t fun u =>
      u.zf = some (decide (j + 1 = len)) ∧ MaskInv s₀ op len c (j + 1) u := by
  refine WP.mono (maskBody_ok hj hl h.ptr h.count ((h.keep.gpr (by decide)).trans hm)
    (by rw [h.keep.2.2]; exact hwr j hj)) fun u ⟨⟨hmem, hp, hcount, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨keep_trans h.keep k, hp, hcount, ?_, ?_⟩⟩
  · intro i hi
    rw [hmem, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl, h.frame _ (fun i hi => out_ne (by omega) (by omega) (by omega))]
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hmem, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

/-- The mask loop writes every byte on both success and failure. -/
theorem mask_ok {s : State} {op : Addr} {len : Nat} {c : Bool}
    (hl1 : 1 ≤ len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = op)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 len) (hm : s.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.loop (.block maskBody) .ne) s (MaskInv s op len c len) :=
  wp_upto (a := 0) (by omega) (MaskInv s op len c)
    (fun j _ hj t ht => maskStep_ok hj hl hm hwr ht) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [hp]; simp, by rw [hcx, Nat.sub_zero], fun i hi => by omega, fun _ _ => rfl⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem maskX_ok {s : State} {B xp : Addr} {Z k ld : Nat} {c : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hk : k < 2 ^ 31) (hld : ld < k)
    (hX : word s.mem B (8 * sX) = off xp ld)
    (hL : word s.mem B (8 * sXl) = BitVec.ofNat 64 (k - ld))
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hax : s.gpr .rax = BitVec.ofNat 64 c.toNat)
    (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp k) :
    WP isa maskX s fun t =>
      (∀ i < k, t.mem (off xp i) = if c then s.mem (off xp i) else 0) ∧
      word t.mem B (8 * sF) = BitVec.ofNat 64 c.toNat ∧ t.gpr .rdi = B ∧
      (∀ a, Z ≤ ofs B a → (∀ i < k, a ≠ off xp i) → t.mem a = s.mem a) ∧
      (∀ i < 6, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧ Keep mmRegs s t := by
  unfold maskX
  refine WP.seq (WP.mono (maskSetup_ok hs hdi hZ hk hld hX hL hK hax)
    fun u ⟨⟨hp, hm, hcx, hF, hf⟩, k₁⟩ => ?_)
  have hi : InScr B Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_singleton]; rintro r rfl; change 248 ≤ Z; omega)
  refine WP.mono (mask_ok (by omega) hk hp hcx hm (fun i hi => by rw [k₁.2.2]; exact ho.wr i hi))
    fun t hc => ?_
  have hout : Outside B Z (2 ^ 64 - Z) u.mem t.mem := by
    intro a ha
    have ha64 : ofs B a < 2 ^ 64 := (a - B).isLt
    apply hc.frame
    intro i hi he
    have hh : Z ≤ ofs B (off xp i) := ho.sep i hi
    rw [← he] at hh
    omega
  have hh : ∀ d, d + 8 ≤ Z → word t.mem B d = word u.mem B d :=
    fun d hd => hout.word (Or.inl hd) (by have := hs.nowrap; omega)
  refine ⟨?_, by rw [hh _ (by change 248 ≤ Z; omega)]; exact hF,
    ((k₁.trans hc.keep).gpr (by decide)).trans hdi, ?_, ?_, (k₁.trans hc.keep).mono (by decide)⟩
  · intro i hi'
    rw [hc.bytes i hi', hi _ (ho.sep i hi')]
  · intro a ha hne
    rw [hc.frame a hne, hi a ha]
  · intro i hi'
    rw [hh _ (by omega), hf.word_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      exact Or.inl (by unfold sF sFn; omega)) (by omega)]

end VG.Proof.Ffdh.X86_64.GenerateKey
