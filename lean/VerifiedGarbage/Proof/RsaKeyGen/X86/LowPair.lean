module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # The paired low-word scan keeps its first nonzero value under masks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

theorem mask_pair (lo hi : BitVec 32) :
    cmask (decide ((lo ||| hi).toNat < 1)) = if lo = 0#32 ∧ hi = 0#32 then BitVec.allOnes 32 else 0#32 := by
  have zero : (lo ||| hi).toNat < 1 ↔ lo = 0#32 ∧ hi = 0#32 := by
    rw [show (lo ||| hi).toNat < 1 ↔ (lo ||| hi).toNat = 0 by omega,
      show (lo ||| hi).toNat = 0 ↔ lo ||| hi = 0#32 from @BitVec.toNat_inj 32 (lo ||| hi) (0#32), BitVec.or_eq_zero_iff]
  rw [show decide ((lo ||| hi).toNat < 1) = decide (lo = 0#32 ∧ hi = 0#32) from decide_eq_decide.mpr zero]
  by_cases h : lo = 0#32 ∧ hi = 0#32 <;> simp [cmask, h]

theorem choose_ok (s : State) :
    WP isa (.block choose) s fun t =>
      (t.gpr .ebx, t.gpr .esi) =
        (if s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32 then (s.gpr .eax, s.gpr .ecx) else (s.gpr .ebx, s.gpr .esi)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  unfold choose
  refine wp_movS rfl fun a A _ => wp_orS rfl fun b B => wp_cmpi fun c C cf _ => ?_
  refine wp_sbb_self cf fun d D => wp_and fun e E => wp_and fun f F => wp_orS rfl fun g G =>
    wp_orS rfl fun t T => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebx, .esi] s t :=
    (((((((A.keeps.mono (by decide)).widen B.keeps).trans (C.keeps _)).widen D.keeps).widen E.keeps).widen
      F.keeps).widen G.keeps).widen T.keeps
  have mask : d.gpr .edx = if s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32 then BitVec.allOnes 32 else 0#32 := by
    rw [D.gpr, B.gpr, A.gpr, A.other .esi (by decide)]
    exact mask_pair _ _
  have low : t.gpr .ebx = s.gpr .ebx ||| (s.gpr .eax &&& d.gpr .edx) := by
    rw [T.other .ebx (by decide), G.gpr, F.other .ebx (by decide), E.other .ebx (by decide),
      D.other .ebx (by decide), C.gpr, B.other .ebx (by decide), A.other .ebx (by decide),
      F.other .eax (by decide), E.gpr, D.other .eax (by decide), C.gpr,
      B.other .eax (by decide), A.other .eax (by decide)]
  have high : t.gpr .esi = s.gpr .esi ||| (s.gpr .ecx &&& d.gpr .edx) := by
    rw [T.gpr, G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.other .esi (by decide),
      G.other .ecx (by decide), F.gpr, E.other .ecx (by decide), D.other .ecx (by decide),
      C.gpr, B.other .ecx (by decide), A.other .ecx (by decide), E.other .edx (by decide)]
  refine ⟨?_, ?_, K⟩
  · rw [low, high, mask]
    by_cases h : s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32
    · simp only [ite_eq_left h]
      rw [BitVec.and_allOnes, BitVec.and_allOnes, h.1, h.2, BitVec.zero_or, BitVec.zero_or]
    · simp only [ite_eq_right h, BitVec.and_zero, BitVec.or_zero]
  · rw [T.mem, G.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowPair
