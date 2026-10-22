module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Halving
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The halving loop decrements only its public iteration counter. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_next {L : Lay} {s : State} {base : Addr} {bytes len count : Nat}
    (h : RtWs L s base bytes len count) (positive : 0 < slot s.mem base 56) :
    WP isa (.block Impl.Dsa.X86.Generation.halvingNext) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [56] s.mem t.mem ∧
      slot t.mem base 56 = slot s.mem base 56 - 1 ∧
      t.zf = some (decide (slot s.mem base 56 - 1 = 0)) ∧ Keeps [.eax] s t := by
  have head : 160 ≤ bytes := h.ws.hdr_le
  unfold Impl.Dsa.X86.Generation.halvingNext Impl.Rsa.X86.Recover.cntNext
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc h.ws.workspace (d := 56) (by omega)) fun u U _ => wp_subS rfl fun v V _ => ?_
  have original : s.mem.readW (off base 56) 32 = BitVec.ofNat 32 (slot s.mem base 56) :=
    by
      symm
      simpa only [BitVec.setWidth_eq] using BitVec.ofNat_toNat 32 (s.mem.readW (off base 56) 32)
  have word : v.gpr .eax = BitVec.ofNat 32 (slot s.mem base 56 - 1) := by
    rw [V.gpr, U.gpr, original]
    change BitVec.ofNat 32 (slot s.mem base 56) - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have val : (v.gpr .eax).toNat = slot s.mem base 56 - 1 := by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have small : slot s.mem base 56 < 2 ^ 32 := (s.mem.readW (off base 56) 32).isLt
      omega)]
  have K : Keeps [.eax] s v := U.keeps.trans V.keeps
  have mem : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep K (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _)
  refine WP.block_append (WP.mono (storeSlot_ok hv (by decide : 56 + 4 ≤ Impl.Rsa.X86.Keys.hdr) .eax) ?_)
  rintro w ⟨hw, F, value, Kw⟩
  rw [val] at value
  rw [mem] at F
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  have kt := T.keeps ([] : List Reg)
  have ht := hw.keep kt (by decide) (by decide) (by rw [T.mem]; exact Outside.refl _ _ _ _)
  refine ⟨ht, T.mem ▸ F, T.mem ▸ value, ?_, (K.trans (Kw.mono (by simp))).trans (kt.mono (by simp))⟩
  rw [Z, Kw.1 .eax (by simp)]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (v.gpr .eax - 0#32 = 0#32) ↔ _
  rw [BitVec.sub_zero]
  constructor
  · intro zero
    rw [zero] at val
    exact val.symm
  · intro zero
    apply BitVec.eq_of_toNat_eq
    rw [val, zero]
    rfl

end VG.Proof.Dsa.X86.Generation
