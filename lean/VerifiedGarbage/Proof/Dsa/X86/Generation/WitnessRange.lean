module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessUniform
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Uniform witnesses use the exact shared RSA interval, 2 through c-2. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86

theorem witness_range {s : State} {base : Addr} {bytes n candidate x : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (C : WitnessContext base n candidate s) (positive : 0 < n) (upper : n ≤ 48)
    (input : wordsVal s.mem base (slot n 5) n = x) :
    WP isa (witnessRange n) s fun t =>
      WitnessContext base n candidate t ∧
      t.gpr .eax = BitVec.ofNat 32 (if 2 ≤ x ∧ x < candidate - 1 then 1 else 0) ∧
      w32 t.mem base witnessUniform = (if 2 ≤ x ∧ x < candidate - 1 then 1 else 0) ∧
      t.zf = some (decide (¬ (2 ≤ x ∧ x < candidate - 1))) ∧
      Outside base witnessUniform 4 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have parentCapacity : montgomeryBytes ≤ bytes := by unfold montgomeryBytes; omega
  have flagsFit : witnessUniform + 4 ≤ bytes := Nat.le_trans (by decide : witnessUniform + 4 ≤ 40960) capacity
  have O := montgomery_offsets positive upper (show 5 < 9 by decide) (show 3 < 9 by decide)
    (show 1 < 9 by decide) (by decide)
  have b1 := Nat.le_trans O.b_le parentCapacity
  have b3 := Nat.le_trans O.a_le parentCapacity
  have b5 := Nat.le_trans O.o_le parentCapacity
  unfold witnessRange
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.lessThan_ok n scr positive b3 b5)
    fun a ⟨lower, Ka, ma⟩ => ?_)
  rw [C.ordinary, input] at lower
  have SA := scr.of_keeps Ka (by decide)
  refine WP.seq (wp_storeS (SA.ea (d := witnessUniform) (by omega)) (SA.write flagsFit)
    fun b B => WP.block_nil ?_)
  have Kb := Ka.trans (B.keeps _)
  have SB := scr.of_keeps Kb (by decide)
  have first : Outside base witnessUniform 4 s.mem b.mem := by
    rw [B.mem, ma]
    exact writeW32_outside _ _ _ (by have := scr.nowrap; omega)
  have same (j : Nat) (bound : slot n j + 8 * n ≤ montgomeryBytes) :
      wordsVal b.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply first.val32
    · left
      have before : montgomeryBytes ≤ witnessUniform := by decide
      omega
    · unfold montgomeryBytes at bound; omega
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.lessThan_ok n SB positive b5 b1)
    fun c ⟨upperMask, Kc, mc⟩ => ?_)
  rw [same 5 O.o_le, same 1 O.b_le, input, C.ceiling] at upperMask
  have Kpre := Kb.trans Kc
  have SC := scr.of_keeps Kpre (by decide)
  have stored : c.mem.readW (off base witnessUniform) 32 = mask32 (1 < x) := by
    rw [mc, B.mem, Mem.readW_writeW_self32, lower]
  refine WP.mono (witness_uniform SC flagsFit stored upperMask)
    fun t ⟨flag, value, zf, last, Kt⟩ => ?_
  have full : Outside base witnessUniform 4 s.mem t.mem := by
    rw [mc] at last
    exact first.trans last
  have K := Kpre.trans (Kt.mono (by decide))
  have frame := full.frameAt (by decide : witnessUniform + 4 < 2 ^ 64)
  have Ct := C.frame_keep K (by decide) (by decide) frame (by
    intro r hr; rw [List.mem_singleton.mp hr]
    exact (Offset.disjoint_base base (by decide : montgomeryBytes ≤ witnessUniform)
      (by decide : witnessUniform + 4 ≤ 2 ^ 64)).symm)
  have predicate : (1 < x ∧ x < candidate - 1) = (2 ≤ x ∧ x < candidate - 1) := propext (by omega)
  simp only [predicate] at flag value zf
  exact ⟨Ct, flag, value, zf, full, K⟩

end VG.Proof.Dsa.X86.Generation
