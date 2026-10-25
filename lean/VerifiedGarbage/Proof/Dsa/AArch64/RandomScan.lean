module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Adapt the existing verified width scan to the random sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The sampler obtains the first significant byte, width and pointer, while
preserving all memory and the caller's other registers. -/
theorem random_significant_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .x12 = p) (hn : s.gpr .x9 = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.significant s fun t =>
      t.gpr .x12 = p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) ∧
      t.gpr .x9 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .x0 = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.x0, .x1, .x3, .x8, .x9, .x10, .x12, .x13] s t := by
  unfold Random.significant
  refine WP.seq (WP.mono (WP.keep [.x1, .x13] (Q := fun u =>
    u.gpr .x1 = p ∧ u.gpr .x13 = BitVec.ofNat 64 bs.length ∧ u.mem = s.mem)
    (by brun [hp, hn]) rfl rfl rfl) fun u ⟨⟨hup, hun, hum⟩, hku⟩ => ?_)
  have hus := hs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  refine WP.seq (WP.mono (significant_ok hup ((hku.gpr .x9 (by decide)).trans hn) hus hpos hbound)
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hk := hku.trans hkv
  have hvp := (hk.gpr .x12 (show Reg.x12 ∉ [Reg.x1, Reg.x13] ++
    [Reg.x3, Reg.x8, Reg.x10, Reg.x1, Reg.x9] by decide)).trans hp
  have hvn := (hkv.gpr .x13 (by decide)).trans hun
  have hsub : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 =
      BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hw := VG.Proof.Dsa.significant_fits bs
    omega
  refine WP.mono (WP.keep [.x13, .x9, .x12, .x0] (Q := fun t =>
      t.gpr .x12 = p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) ∧
      t.gpr .x9 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .x0 = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧ t.mem = v.mem)
      (by brun [hvp, hvn, hv8, hv9, hsub]) rfl rfl rfl)
    fun t ⟨⟨htp, htn, hta, htm⟩, hkt⟩ =>
      ⟨htp, htn, hta, (htm.trans hvm).trans hum, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
