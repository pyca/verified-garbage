module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Branch only on the public exponent, at its full 64-bit width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponent_pair_equal (lo hi value : BitVec 32) :
    (((lo ^^^ value) ||| hi) == 0) = decide (lo.toNat + 2 ^ 32 * hi.toNat = value.toNat) := by
  have Z : ((lo ^^^ value) ||| hi) = 0 ↔ lo = value ∧ hi = 0 := by
    change ((lo ^^^ value) ||| hi) = 0#32 ↔ lo = value ∧ hi = 0#32
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  have V : lo.toNat + 2 ^ 32 * hi.toNat = value.toNat ↔ lo = value ∧ hi = 0 := by
    have lb := lo.isLt
    have vb := value.isLt
    constructor
    · intro E
      have H : hi.toNat = 0 := by omega
      exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq H⟩
    · rintro ⟨rfl, rfl⟩
      simp
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using Z.trans V.symm

theorem equalExponent_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) (value : BitVec 32) :
    WP isa (.block (equalExponent value)) s fun t =>
      Ws t B Z n N ∧ t.mem = s.mem ∧
      isa.eval .e t = some (decide (val32 s.mem B kEv 2 = value.toNat)) ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold equalExponent
  refine wp_movS (readSrc_sc h.workspace (by unfold kEv hdr at *; omega)) fun u U _ => ?_
  refine wp_logicS (.inr rfl) rfl fun v V => ?_
  have hv := (h.rest U.keeps).rest V.keeps
  refine wp_orS (readSrc_sc hv.workspace (by unfold kEvHi hdr at *; omega)) fun w W => ?_
  refine wp_cmpS rfl fun t T flag => WP.block_nil ?_
  have K : Keeps [.eax] s t := ((U.keeps.trans V.keeps).trans W.keeps).trans (T.keeps _)
  refine ⟨h.rest K, T.mem.trans (W.mem.trans (V.mem.trans U.mem)), ?_, K⟩
  change t.zf = _
  rw [flag]
  change some (w.gpr .eax - 0#32 == 0#32) = _
  rw [BitVec.sub_zero, W.gpr, V.gpr, U.gpr, V.mem, U.mem]
  change some (((s.mem.readW (off B kEv) 32 ^^^ value) ||| s.mem.readW (off B kEvHi) 32) == 0) = _
  rw [exponent_pair_equal]
  rfl

theorem parityExponent_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N) :
    WP isa (.block parityExponent) s fun t =>
      Ws t B Z n N ∧ t.mem = s.mem ∧
      isa.eval .e t = some (decide (val32 s.mem B kEv 2 % 2 = 0)) ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold parityExponent
  refine wp_movS (readSrc_sc h.workspace (by unfold kEv hdr at *; omega)) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  refine wp_cmpS rfl fun t T flag => WP.block_nil ?_
  have K : Keeps [.eax] s t := (U.keeps.trans V.keeps).trans (T.keeps _)
  refine ⟨h.rest K, T.mem.trans (V.mem.trans U.mem), ?_, K⟩
  change t.zf = _
  rw [flag]
  change some (v.gpr .eax - 0#32 == 0#32) = _
  rw [BitVec.sub_zero, V.gpr, U.gpr]
  change some (s.mem.readW (off B kEv) 32 &&& (1 : BitVec 32) == 0#32) = _
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_zero]
  rw [VG.Proof.Rsa.KeyBits32.bv_and_one, VG.Proof.Mont.X86.Dynamic.val32_parity]

end VG.Proof.RsaKeyGen.X86.Key
