module

public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Mont.Words
/-! # Native candidate finish writes the exact count and status -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateUsed.lean`, which only this module imported.
section

/-! # The candidate's used count is exported as one zero-extended 64-bit word -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateFinish

theorem used_ok {s : State} {base : Addr} {size status : Nat} {count usedPtr : BitVec 32}
    (S : Scr s base size) (header : 156 ≤ size) (W : Ws s (usedPtr.setWidth 64) 8)
    (pointer : s.mem.readW (off base 44) 32 = usedPtr)
    (countEq : s.mem.readW (off base 152) 32 = count) :
    WP isa (used status) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 status ∧
      t.mem = s.mem.writeW (usedPtr.setWidth 64) (BitVec.ofNat 64 count.toNat) ∧
      Outside (usedPtr.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold used
  refine WP.seq (wp_movS (readSrc_sc S (d := 44) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 152) (by omega)) fun b B _ => WP.block_nil ?_)
  have Kb : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have ptrB : b.gpr .edx = usedPtr := by rw [B.other .edx (by decide), A.gpr, pointer]
  have valueB : b.gpr .eax = count := by rw [B.gpr, A.mem, countEq]
  refine WP.seq (WP.mono (writeUsed_ok (W.of_keeps Kb) ptrB) fun c ⟨memory, _, O, Kc⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨T.gpr, ?_, ?_, (Kb.widen Kc).widen T.keeps⟩
  · rw [T.mem, memory, Mb, valueB]
  · rw [Mb] at O
    rw [T.mem]
    exact O

theorem none_ok {s : State} {base : Addr} {size : Nat} {usedPtr : BitVec 32}
    (S : Scr s base size) (header : 48 ≤ size) (W : Ws s (usedPtr.setWidth 64) 8)
    (pointer : s.mem.readW (off base 44) 32 = usedPtr) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateFinish.none s fun t =>
      t.gpr .eax = 0#32 ∧ t.mem = s.mem.writeW (usedPtr.setWidth 64) 0#64 ∧
      Outside (usedPtr.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.none
  refine WP.seq (wp_movS (readSrc_sc S (d := 44) (by omega)) fun a A _ => wp_movS rfl fun b B _ => WP.block_nil ?_)
  have Kb : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have ptrB : b.gpr .edx = usedPtr := by rw [B.other .edx (by decide), A.gpr, pointer]
  refine WP.mono (writeUsed_ok (W.of_keeps Kb) ptrB) fun t ⟨memory, value, O, Kt⟩ => ?_
  refine ⟨value, ?_, ?_, Kb.widen Kt⟩
  · rw [memory, Mb, B.gpr]; rfl
  · rw [Mb] at O
    exact O

end VG.Proof.RsaKeyGen.X86.CandidateFinish
