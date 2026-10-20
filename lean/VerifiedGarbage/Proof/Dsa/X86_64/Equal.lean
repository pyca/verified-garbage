module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands

import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.EqualLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Complete byte-buffer equality and inequality checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem equal_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 as.length)
    (has : Src s B Z (pointerValue s.mem B a.pointer) as)
    (hbs : Src s B Z (pointerValue s.mem B b.pointer) bs)
    (helen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.equal seqs
  refine WP.seq (WP.mono (equalHead_ok hg.scr hg.rdi hZ a b ha hb)
    fun u ⟨hup, huq, hun, hu8, hum, hku⟩ => ?_)
  rw [hlen] at hun
  have hua := has.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  have hub := hbs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  refine WP.seq (WP.mono (equalLoop_ok hup huq hun hua hub helen h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (as = bs) := by
    apply decide_eq_decide.mpr
    simpa only [hu8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 unequal) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hks := (hku.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hum)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hks.2.2, (hks.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
