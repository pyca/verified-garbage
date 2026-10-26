module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame

import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Counting bytes in the DSA streaming reduction loop -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The only loop condition is the public remaining length. -/
theorem reduceCount_ok {s : State} {B : Addr} {Z o w wx m n : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hn : word s.mem (off B o) (8 * Crt.sRem) = BitVec.ofNat 64 n)
    (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block Arithmetic.reduceCount) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      word t.mem (off B o) (8 * Crt.sRem) = BitVec.ofNat 64 (n - 1) ∧
      t.zf = some (decide (n = 1)) ∧
      Outside (off B o) (8 * Crt.sRem) 8 s.mem t.mem ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hslot := hdr_lt_slot wx 8 (show Crt.sRem < 32 by decide)
  have hsub : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) :=
    ofNat64_pred h1 h64
  have hzero : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega)]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off (off B o) (8 * Crt.sRem)) (BitVec.ofNat 64 (n - 1)) ∧
    t.zf = some (decide (n = 1))) ?_ rfl) fun t ⟨⟨hmem, hz⟩, hk⟩ => ?_
  · unfold Arithmetic.reduceCount
    xrun [State.ea, hdr, hc.rdi, hdrOff, hn, hsub, hzero,
      hc.good.scr.ld (show 8 * Crt.sRem + 8 ≤ slot wx 8 by omega),
      hc.good.scr.st (show 8 * Crt.sRem + 8 ≤ slot wx 8 by omega)]
  have ho : Outside (off B o) (8 * Crt.sRem) 8 s.mem t.mem := by
    rw [hmem]; exact writeW_outside _ _ _ (by decide)
  have hf : Frm (off B o) (workRanges wx) s.mem t.mem := by
    intro x hx
    apply ho x
    have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
    unfold Crt.sRem sFn at *
    omega
  have ht := hc.of_frmT hf (workRanges_ok wx) hk.2.2 (hk.gpr (by decide))
  have hnowrap := hc.good.scr.nowrap
  refine ⟨ht, ⟨ht.good, ?_, ?_⟩, ?_, hz, ho, hf, hk.mono (by decide)⟩
  · rw [hmem, hdrStore_wv _ _ _ (by decide) (by decide) hnowrap]
    exact hm.modulus
  · rw [hmem, hdrStore_word _ _ _ (by decide) (by decide) hnowrap]
    exact hm.inverse
  · rw [hmem, word_writeW_self]

/-- The unread tail is still a source at the next byte address. -/
theorem source_tail {s : State} {B p : Addr} {Z : Nat} {b : Byte} {bs : List Byte}
    (h : Src s B Z p (b :: bs)) : Src s B Z (p + 1) bs := by
  have addr (i : Nat) : p + 1 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      ← BitVec.ofNat_add]
    rw [Nat.add_comm 1 i]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; rw [addr]; exact h.rd (i + 1) (by simpa using hi)
  · intro i hi; rw [addr]; exact h.val (i + 1) (by simpa using hi)
  · intro i hi; rw [addr]; exact h.out (i + 1) (by simpa using hi)

end VG.Proof.Dsa.X86_64
