module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Complete streaming modular reduction for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Reduce an arbitrary big-endian byte string, including the empty string,
modulo an odd integer greater than 255. No primality or divisibility relation
between the source and destination moduli is required. -/
theorem reduce_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} {bytes : List Byte} {sp sl : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (hlen : bytes.length < 2 ^ 64) :
    WP isa (Arithmetic.reduce M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.decodeBE bytes % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.reduce seqs
  refine WP.seq (WP.mono (reduceSetup_ok M hc hw hw48 (by omega) hodd hn hinv)
    fun u ⟨hcu, hmu, hur, huy, hux, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (reduceInit_ok hcu hmu hsp hsl
    ((work_parent hc hfu hsp).trans hp) ((work_parent hc hfu hsl).trans hl) hlen)
    fun v ⟨hcv, hmv, harr, hvp, hvl, hvz, hfv, hkv⟩ => ?_)
  have hf := hfu.trans hfv
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have hvy := (harr aY (by decide)).trans huy
  have hvx := (harr aX (by decide)).trans hux
  have hv : ReduceState v B Z o w wx m minv p bytes 0 :=
    ⟨hcv, hmv, (harr aR2 (by decide)).trans hur,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp hvx i hi,
      hvy, by omega, hvp, hvl, work_source hc hf hk hs⟩
  by_cases he : bytes.length = 0
  · refine WP.ite true ?_ (fun _ => WP.block_nil ?_) (fun h => Bool.noConfusion h)
    · change VG.X86_64.eval .e v = some true
      simp only [VG.X86_64.eval, hvz, he, decide_true]
    · refine ⟨hcv, hmv, ?_, hf, hk⟩
      rw [List.length_eq_zero_iff.mp he]
      exact hvy
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change VG.X86_64.eval .e v = some false
      simp only [VG.X86_64.eval, hvz, he, decide_false]
    · refine WP.mono (reduceLoop_ok M hv hw (by omega) hm hodd (by omega) hlen)
        fun t ⟨hct, hmt, htval, hft, hkt⟩ => ?_
      rw [VG.Proof.Dsa.reduceBytes_eq] at htval
      exact ⟨hct, hmt, htval, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
