module

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Mask

/-! # FFDH on x86-64: the complete masked scalar store -/

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
