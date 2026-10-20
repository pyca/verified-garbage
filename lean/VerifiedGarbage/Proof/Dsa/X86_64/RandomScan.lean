module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! Adapt the existing verified width scan to the random sampler. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The sampler obtains the first significant byte, width and pointer, while
preserving all memory and the caller's other registers. -/
theorem random_significant_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .r10 = p) (hn : s.gpr .r11 = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (hpos : 0 < bs.length) (hbound : bs.length < 2 ^ 64) :
    WP isa Random.significant s fun t =>
      t.gpr .r10 = p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) ∧
      t.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .rax = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s t := by
  unfold Random.significant
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx] (Q := fun u =>
    u.gpr .rsi = p ∧ u.gpr .rcx = BitVec.ofNat 64 bs.length ∧ u.mem = s.mem)
    (by xrun [hp, hn]) rfl) fun u ⟨⟨hup, hun, hum⟩, hku⟩ => ?_)
  have hus := hs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  refine WP.seq (WP.mono (significant_ok hup hun hus hpos hbound)
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hk := hku.trans hkv
  have hvp := (hk.gpr (show Reg.r10 ∉ [Reg.rsi, Reg.rcx] ++
    [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx] by decide)).trans hp
  have hvn := (hk.gpr (show Reg.r11 ∉ [Reg.rsi, Reg.rcx] ++
    [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx] by decide)).trans hn
  have hsub : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 =
      BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hw := VG.Proof.Dsa.significant_fits bs
    omega
  refine WP.mono (WP.keep [.r11, .r10, .rax] (Q := fun t =>
      t.gpr .r10 = p + BitVec.ofNat 64 (bs.length - (VG.Proof.Dsa.significant bs).1) ∧
      t.gpr .r11 = BitVec.ofNat 64 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .rax = (VG.Proof.Dsa.significant bs).2.zeroExtend 64 ∧ t.mem = v.mem)
      (by xrun [hvp, hvn, hv8, hv9, hsub]) rfl)
    fun t ⟨⟨htp, htn, hta, htm⟩, hkt⟩ =>
      ⟨htp, htn, hta, (htm.trans hvm).trans hum, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
