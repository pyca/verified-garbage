module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckFirst
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckFinish
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedAcceptance
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedChecks
import VerifiedGarbage.Proof.Bignum.X86.ArrayCompare
import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Packed RSA values enter Montgomery arithmetic only with safe bounds -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem precomputedChecks_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (space : size n ≤ bytes) :
    WP isa (precomputedChecks n) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (precomputedAccepted
        (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n) (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n)).toNat ∧
      t.zf = some (!precomputedAccepted (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n) (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n)) ∧
      Outs base (precomputedCheckRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have b1 := slot_header n 1
  unfold precomputedChecks
  refine WP.seq (WP.mono (precomputedCheckFirst_ok hs hn space) fun u ⟨Saved, O, K⟩ => ?_)
  refine WP.seq (WP.mono (arrayCompare_ok (hs.of_keeps K (by decide)) hn space
    (by decide) (by decide) (by decide) (by decide)) fun v ⟨Mask, Ov, Kv⟩ => ?_)
  have Os : Outs base (precomputedCheckRanges n) s.mem v.mem :=
    O.trans (Outs.of_outside Ov (by simp [precomputedCheckRanges]))
  have Ks : Keeps powerClob s v := K.trans (Kv.mono (by decide))
  have M0 := precomputedCheck_value Os (by decide : 0 < 8) (by decide) (by decide) (by omega)
  have Low := modulus_low (base := base) (mem := v.mem) hn rfl
  rw [M0] at Low
  have Header : v.mem.readW (off base 148) 32 = u.mem.readW (off base 148) 32 :=
    by
      apply BitVec.eq_of_toNat_eq
      exact Outside.w32 Ov (.inl (by omega)) (by decide)
  refine WP.mono (precomputedCheckFinish_ok (hs.of_keeps Ks (by decide)) space) fun t ⟨C, Z, M, Kt⟩ => ?_
  have Result : t.gpr .ecx = BitVec.ofNat 32 (precomputedAccepted
      (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n) (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n)).toNat := by
    rw [C, Header, Saved, Mask,
      precomputedCheck_value O (by decide : 5 < 8) (by decide) (by decide) (by omega),
      precomputedCheck_value O (by decide : 0 < 8) (by decide) (by decide) (by omega)]
    exact precomputedAcceptance Low
  refine ⟨Result, ?_, ?_, Ks.trans (Kt.mono (by decide))⟩
  · rw [Z, Result]
    cases precomputedAccepted (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n) (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n) <;> rfl
  · rw [M]; exact Os

end VG.Proof.Bignum.X86.PublicContext
