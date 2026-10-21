module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Finish the witness lower-bound scan as an all-zero or all-one mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem finish_ok {s : State} {base : Addr} {size src upper : Nat} (scratch : Scr s base size)
    (fit : src + 4 ≤ size) (zero : s.gpr .ebx = 0#32 ↔ upper = 0) :
    WP isa (.block (finish src)) s fun t =>
      t.gpr .ebx = cmask (decide (¬(upper = 0 ∧ w32 s.mem base src < 2))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_orS rfl fun b B =>
    wp_logicS (.inr rfl) rfl fun c C => wp_orS rfl fun d D => ?_
  have low : c.gpr .eax = (s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32 := by
    rw [C.gpr, B.gpr, A.gpr]
    rfl
  have combined : d.gpr .ebx = s.gpr .ebx ||| ((s.mem.readW (off base src) 32 ||| 1#32) ^^^ 1#32) := by
    rw [D.gpr, low, C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide)]
  have combinedZero : (d.gpr .ebx).toNat = 0 ↔ upper = 0 ∧ w32 s.mem base src < 2 := by
    rw [show (d.gpr .ebx).toNat = 0 ↔ d.gpr .ebx = 0#32 from @BitVec.toNat_inj 32 (d.gpr .ebx) (0#32),
      combined, BitVec.or_eq_zero_iff, zero, clear_low_zero]
  refine wp_cmpi fun e E cf _ => wp_sbb_self cf fun f F => wp_logicS (.inr rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ((((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).trans (E.keeps _)).widen F.keeps).widen T.keeps⟩
  · rw [T.gpr, F.gpr]
    change cmask (decide ((d.gpr .ebx).toNat < 1)) ^^^ BitVec.allOnes 32 = _
    rw [SigMask.flip_mask]
    exact congrArg cmask (decide_eq_decide.mpr (not_congr combinedZero))
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.WitnessLower
