module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands

import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Complete byte-buffer zero and nonzero checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Scan every byte and intersect the acceptance mask with the requested
zero/nonzero predicate. No input or temporary scalar buffer is modified. -/
theorem zero_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.zero seqs
  refine WP.seq (WP.mono (zeroHead_ok hg.scr hg.rdi hZ a ha)
    fun v ⟨hvp, hvn, hv8, hvm, hks⟩ => ?_)
  rw [hlen] at hvn
  have hvs : Src v B Z (pointerValue s.mem B a.pointer) bytes :=
    hsrc.congrK (by rw [hvm]; exact InScr.refl _ _ _) hks
  refine WP.seq (WP.mono (zeroLoop_ok hvp hvn hvs h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (∀ b ∈ bytes, b = 0) := by
    apply decide_eq_decide.mpr
    simpa only [hv8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 nonzero) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hkl' := (hks.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hvm)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hkl'.2.2, (hkl'.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hkl'.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
