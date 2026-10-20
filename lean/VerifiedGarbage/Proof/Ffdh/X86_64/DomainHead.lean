module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # FFDH on x86-64: check the packed modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The modulus check returns its public result in ZF and leaves the
packed domain's g and q pointers in the outer header. -/
theorem domHead_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) :
    WP isa (.block domHead) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k) ∧
      word t.mem B (8 * sG) = dp + BitVec.ofNat 64 k ∧
      word t.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k) ∧
      Frm B [(8 * sG, 8), (8 * sQ, 8)] s.mem t.mem ∧ t.gpr .rdi = B ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have eq2 : dp + BitVec.ofNat 64 k + BitVec.ofNat 64 k = dp + BitVec.ofNat 64 (2 * k) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show k + k = 2 * k by omega]
  unfold domHead
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx, .rcx, .rax] (Q := fun t => t.gpr .rdx = dp ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.mem =
      (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)).writeW
        (off B (8 * sQ)) (dp + BitVec.ofNat 64 (2 * k)))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sDom) (by change 136 ≤ Z; omega),
      hs.ld (d := 8 * sK) (by change 152 ≤ Z; omega),
      hs.st (d := 8 * sG) (by change 224 ≤ Z; omega),
      hs.st (d := 8 * sQ) (by change 232 ≤ Z; omega), hD, hK, eq2]) rfl)
    fun s₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  have o1 := writeW_outside s.mem B (d := 8 * sG) (dp + BitVec.ofNat 64 k) (by decide)
  have o2 := writeW_outside (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)) B
    (d := 8 * sQ) (dp + BitVec.ofNat 64 (2 * k)) (by decide)
  have f : Frm B [(8 * sG, 8), (8 * sQ, 8)] s.mem s₁.mem := by
    rw [hm]
    exact (Frm.of_outside o1 (by simp)).trans (Frm.of_outside o2 (by simp))
  have hsrc₁ := hsrc.congrK (InScr.of_frm f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · change 224 ≤ Z; omega
    · change 232 ≤ Z; omega)) k₁
  refine WP.mono (invalid_ok hdx hcx hk1 hk2 hl
    (fun i hi => hsrc₁.rd i (by omega)) (fun i hi => hsrc₁.val i (by omega)))
    fun t ⟨hz, hm', k₂⟩ => ?_
  have K := (k₁.trans k₂).mono (show ∀ r ∈ [.rdx, .rcx, .rax] ++ [.rax, .rbp, .rsi], r ∈ mmRegs by decide)
  refine ⟨hz, ?_, ?_, by rw [hm']; exact f, (K.gpr (by decide)).trans hdi, K⟩
  · rw [hm', hm, o2.word (by decide) (by decide)]; exact word_writeW_self _ _ _ _
  · rw [hm', hm]; exact word_writeW_self _ _ _ _

end VG.Proof.Ffdh.X86_64
