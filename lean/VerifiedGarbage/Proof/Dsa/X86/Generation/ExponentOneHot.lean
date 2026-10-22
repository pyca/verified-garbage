module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Proof.Bignum.X86.TwoPower
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Mont.Words32

/-! Retain the full one-hot word beside the prepared window exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem exponent_one_hot {L : Lay} {s : State} {base : Addr} {bytes len count : Nat}
    (h : RtWs L s base bytes len count) :
    WP isa (.block Impl.Dsa.X86.Generation.exponentOneHot) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [64, 68] s.mem t.mem ∧
      (word t.mem base 64).toNat = 2 ^ (slot s.mem base 20 % 64) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have head : 160 ≤ bytes := h.ws.hdr_le
  unfold Impl.Dsa.X86.Generation.exponentOneHot
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc h.ws.workspace (d := 20) (by omega)) fun u U _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.Bignum.X86.TwoPower.code_ok u) ?_)
  rintro v ⟨value, mem, K⟩
  rw [U.gpr] at value
  have Kv : Keeps [.eax, .ebx, .ecx, .edx] s v := (U.keeps.mono (by decide)).trans K
  have memv : v.mem = s.mem := mem.trans U.mem
  have hv := h.keep Kv (by decide) (by decide) (by rw [memv]; exact Outside.refl _ _ _ _)
  refine WP.block_append (WP.mono (storeSlot_ok hv (d := 64) (by decide) .eax) ?_)
  rintro w ⟨hw, F, low, Kw⟩
  refine WP.mono (storeSlot_ok hw (d := 68) (by decide) .edx) ?_
  rintro t ⟨ht, F', high, Kt⟩
  rw [Kw.1 .edx (by simp)] at high
  have low' := (F'.slot (e := 64) (by decide) (by simp)).trans low
  rw [memv] at F
  have number := congrArg BitVec.toNat value
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (v.gpr .eax).isLt,
    Nat.shiftLeft_eq, BitVec.toNat_twoPow_of_lt (Nat.mod_lt _ (by decide : 0 < 64))] at number
  refine ⟨ht, F.join F', ?_, (Kv.trans (Kw.mono (by simp))).trans (Kt.mono (by simp))⟩
  rw [word_eq_w32]
  change slot t.mem base 64 + 2 ^ 32 * slot t.mem base 68 = _
  rw [low', high]
  change _ = 2 ^ ((s.mem.readW (off base 20) 32).toNat % 64)
  omega

end VG.Proof.Dsa.X86.Generation
