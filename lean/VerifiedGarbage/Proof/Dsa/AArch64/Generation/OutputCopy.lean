module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Copy accepted packed parameters to the caller and return success -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (VG.Proof.Bignum.off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i ≠ VG.Proof.Bignum.off (W 6) j) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok (by omega) hsi hdi hcx
    (fun i hi => by rw [ku.rd, ku.wr]; exact hrd i hi)
    (fun i hi => by rw [ku.wr]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)), hm]

end VG.Proof.Dsa.AArch64.Generation
