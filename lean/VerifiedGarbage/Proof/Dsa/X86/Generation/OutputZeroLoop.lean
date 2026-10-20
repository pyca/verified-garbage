module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.RandomScan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Bounded byte clearing for an unsuccessful parameter search -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

structure OutputZeroInv (out : BitVec 32) (len : Nat) (initial : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = out + BitVec.ofNat 32 k
  ecx : s.gpr .ecx = BitVec.ofNat 32 (len - k)
  eax : s.gpr .eax = 0
  frame : Frame [⟨out.setWidth 64, len⟩] initial.mem s.mem
  zero : ∀ i < k, s.mem (out.setWidth 64 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .esi] initial s

theorem outputZeroStep_ok {out : BitVec 32} {len k : Nat} {initial s : State}
    (positive : k < len) (small : len < 2 ^ 32) (room : out.toNat + len ≤ 2 ^ 32)
    (write : ∀ i, i < len → InRegions initial.wr (off (out.setWidth 64) i) 1)
    (I : OutputZeroInv out len initial k s) :
    WP isa (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) s
      fun t => OutputZeroInv out len initial (k + 1) t ∧ t.zf = some (decide (len - (k + 1) = 0)) := by
  have hp : s.ea (at_ .esi 0) = out.setWidth 64 + BitVec.ofNat 64 k := by
    change (s.gpr .esi + 0#32).setWidth 64 = _
    rw [BitVec.add_zero, I.esi]; exact addr_eq (by omega)
  have hw : InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 k) 1 := by
    rw [I.keeps.2.2]; exact write k positive
  refine wp_store8 hp hw fun a sa => wp_addi fun b ab => wp_subi fun t bt _ zt => WP.block_nil ?_
  have hv : (s.gpr Reg8.al.reg).setWidth 8 = 0 := by change (s.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at sa
  have K : Keeps [.eax, .ecx, .esi] s t :=
    ((sa.keeps _).trans (ab.keeps.mono (by decide))).trans (bt.keeps.mono (by decide))
  have mem : t.mem = s.mem.writeW (out.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [bt.mem, ab.mem, sa.mem]
  have fr : Frame [⟨out.setWidth 64, len⟩] s.mem t.mem := by
    rw [mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans K⟩, ?_⟩
  · rw [bt.other _ (by decide), ab.gpr, sa.gpr, I.esi, Offset.add_ofNat_add_one]
  · rw [bt.gpr, ab.other _ (by decide), sa.gpr, I.ecx, ofNat_pred (by omega)]; rfl
  · rw [bt.other _ (by decide), ab.other _ (by decide), sa.gpr, I.eax]
  · rw [mem]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · rw [writeW8_outside _ _ (d := k) _ (by omega) _ (by rw [ofs_off0 _ (by omega)]; omega)]
      exact I.zero i (by omega)
  · rw [zt, ab.other _ (by decide), sa.gpr, I.ecx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem outputZeroLoop_ok {out : BitVec 32} {len : Nat} {initial s : State}
    (positive : 0 < len) (small : len < 2 ^ 32) (room : out.toNat + len ≤ 2 ^ 32)
    (write : ∀ i, i < len → InRegions initial.wr (off (out.setWidth 64) i) 1)
    (I : OutputZeroInv out len initial 0 s) :
    WP isa (.loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) .ne) s
      fun t => t.gpr .eax = 0 ∧ Frame [⟨out.setWidth 64, len⟩] initial.mem t.mem ∧
        Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
        Keeps [.eax, .ecx, .esi] initial t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = len - k ∧ k < len ∧ OutputZeroInv out len initial k t)
    (fun n t ht => ?_) len s ⟨0, rfl, positive, I⟩
  obtain ⟨k, rfl, hk, J⟩ := ht
  refine WP.mono (outputZeroStep_ok hk small room write J) fun u ⟨K, z⟩ => ?_
  by_cases done : len - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, done, decide_true, Option.map_some, Bool.not_true], K.eax, K.frame, ?_, K.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i hi _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
      exact K.zero i (by omega)
  · exact .inr ⟨by simp only [eval, z, done, decide_false, Option.map_some, Bool.not_false], _, by omega,
      k + 1, rfl, by omega, K⟩
end VG.Proof.Dsa.X86.Generation
