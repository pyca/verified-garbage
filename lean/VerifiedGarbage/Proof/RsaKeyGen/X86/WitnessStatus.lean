module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-! # Native mask selection implements the reviewed round-count policy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessStatus

def status (passed : Bool) (rounds uniform checks : Nat) : Nat :=
  if passed then if rounds < 16 ∨ uniform < checks then 4 else 1 else 3

theorem mask_status (passed moreRounds moreUniform : Bool) :
    (((((if moreRounds then BitVec.allOnes 32 else 0) ||| (if moreUniform then BitVec.allOnes 32 else 0))
      &&& 3) + 1) &&& (0 - BitVec.ofNat 32 passed.toNat)) |||
      (((0 - BitVec.ofNat 32 passed.toNat) ^^^ BitVec.allOnes 32) &&& 3) =
    BitVec.ofNat 32 (if passed then if moreRounds || moreUniform then 4 else 1 else 3) := by
  cases passed <;> cases moreRounds <;> cases moreUniform <;> decide

theorem code_ok {s : State} {passed : Bool} (flag : s.gpr .esi = BitVec.ofNat 32 passed.toNat) :
    WP isa (.block code) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (status passed (s.gpr .eax).toNat (s.gpr .ebx).toNat (s.gpr .edx).toNat) ∧
      t.mem = s.mem ∧ Keeps [.ecx, .edx, .ebp] s t := by
  unfold code
  refine wp_cmpi fun a A carryA _ => wp_sbb_self carryA fun b B =>
    wp_cmp fun c C carryC _ => wp_sbb_self carryC fun d D =>
    wp_or fun e E => wp_andi fun f F => wp_addS rfl fun g G _ =>
    wp_movS rfl fun h H _ => wp_sub fun i I _ => wp_and fun j J =>
    wp_logicS (Or.inr rfl) rfl fun k K => wp_andi fun l L => wp_or fun t T => WP.block_nil ?_
  have keep : Keeps [.ecx, .edx, .ebp] s t := by
    exact ((((((((((((A.keeps [.ecx, .edx, .ebp]).widen B.keeps).widen (C.keeps [.ecx, .edx, .ebp])).widen D.keeps).widen E.keeps).widen F.keeps).widen G.keeps).widen H.keeps).widen I.keeps).widen J.keeps).widen K.keeps).widen L.keeps).widen T.keeps
  refine ⟨?_, ?_, keep⟩
  · rw [T.gpr, L.other .ecx (by decide), K.other .ecx (by decide), J.gpr,
      I.other .ecx (by decide), H.other .ecx (by decide), G.gpr, F.gpr, E.gpr,
      D.other .ecx (by decide), C.gpr, B.gpr, D.gpr,
      B.other .ebx (by decide), B.other .edx (by decide), A.gpr,
      L.gpr, K.gpr, I.gpr, H.gpr, H.other .esi (by decide),
      G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide)]
    simp only [show AluOp.xor ≠ AluOp.and by decide, ite_false]
    rw [J.other .ebp (by decide), I.gpr, H.gpr, H.other .esi (by decide),
      G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.gpr, flag]
    rw [mask_status]
    simp only [status, Bool.or_eq_true, decide_eq_true_eq]
    rfl
  · exact T.mem.trans (L.mem.trans (K.mem.trans (J.mem.trans (I.mem.trans (H.mem.trans
      (G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))))))))))

end VG.Proof.RsaKeyGen.X86.WitnessStatus
