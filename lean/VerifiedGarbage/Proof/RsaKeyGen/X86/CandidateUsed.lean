module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Mont.Words

/-! # The candidate's used count is exported as one zero-extended 64-bit word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateFinish

theorem writeUsed_ok {s : State} {used : BitVec 32}
    (W : Ws s (used.setWidth 64) 8) (P : s.gpr .edx = used) :
    WP isa (.block writeUsed) s fun t =>
      t.mem = s.mem.writeW (used.setWidth 64) (BitVec.ofNat 64 (s.gpr .eax).toNat) ∧
      t.gpr .eax = 0#32 ∧ Outside (used.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  have ptr : PtrAt s (used.setWidth 64) .edx 0 := by
    rw [PtrAt, P, BitVec.toNat_setWidth, Nat.add_zero,
      Nat.mod_eq_of_lt (Nat.lt_trans used.isLt (by decide)), Nat.mod_eq_of_lt used.isLt]
  unfold writeUsed
  refine wp_storeS (ea_ptr W ptr (d := 0) (by decide)) (ws_write W (by decide)) fun a A => ?_
  refine wp_movS rfl fun b B _ => ?_
  have Kb := (A.keeps [.eax]).widen B.keeps
  have Wb := W.of_keeps Kb
  have ptrB : PtrAt b (used.setWidth 64) .edx 0 := by
    rw [PtrAt, Kb.1 .edx (by decide)]
    exact ptr
  refine wp_storeS (ea_ptr Wb ptrB (d := 4) (by decide)) (ws_write Wb (by decide)) fun t T => WP.block_nil ?_
  have pair : (0#32 ++ s.gpr .eax) = BitVec.ofNat 64 (s.gpr .eax).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    change (s.gpr .eax).toNat = (s.gpr .eax).toNat % 2 ^ 64
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (s.gpr .eax).isLt (by decide : 2 ^ 32 < 2 ^ 64))).symm
  have memory : t.mem = s.mem.writeW (used.setWidth 64) (BitVec.ofNat 64 (s.gpr .eax).toNat) := by
    rw [T.mem, B.mem, A.mem, B.gpr]
    simp only [Nat.zero_add, off, BitVec.add_zero]
    rw [← VG.Proof.Rc2.Word32.write64_pair]
    change s.mem.writeW (used.setWidth 64) (0#32 ++ s.gpr .eax) = _
    rw [pair]
  refine ⟨memory, by rw [(T.keeps []).1 .eax (by decide), B.gpr]; rfl, ?_, Kb.widen (T.keeps [])⟩
  rw [memory]
  simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
    VG.Proof.Mont.writeW_outside s.mem (used.setWidth 64) (d := 0)
      (BitVec.ofNat 64 (s.gpr .eax).toNat) (by decide)

end VG.Proof.RsaKeyGen.X86.CandidateFinish
