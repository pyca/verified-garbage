module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Pack
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Load source, destination, length, and the unmasked-copy value -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem packArgs_ok {s : State} {base : Addr} {parent : BitVec 32}
    (F : SearchFrame s base) (saved : s.mem.readW (off base 20) 32 = parent) (src dst len : Nat) :
    WP isa (.block (packArgs src dst len)) s fun t =>
      t.gpr .esi = parent + BitVec.ofNat 32 src ∧ t.gpr .edx = parent + BitVec.ofNat 32 dst ∧
      t.gpr .ecx = BitVec.ofNat 32 len ∧ t.gpr .ebx = BitVec.allOnes 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx, .edx, .esi] s t := by
  unfold packArgs
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (bufferPointer_ok F saved .esi src) fun a ⟨si, ma, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (bufferPointer_ok (parent := parent) (F.keeps Ka (by decide)) (by rw [ma]; exact saved) .edx dst)
    fun b ⟨dx, mb, Kb⟩ => ?_)
  refine wp_movS rfl fun c bc _ => wp_movS rfl fun t ct _ => WP.block_nil ?_
  have tail : Keeps [.ebx, .ecx] b t := (bc.keeps.mono (by decide)).trans (ct.keeps.mono (by decide))
  exact ⟨(tail.1 _ (by decide)).trans ((Kb.1 _ (by decide)).trans si),
    (tail.1 _ (by decide)).trans dx, (ct.other _ (by decide)).trans bc.gpr, ct.gpr,
    ct.mem.trans (bc.mem.trans (mb.trans ma)),
    (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans (tail.mono (by decide)))⟩
end VG.Proof.Dsa.X86.Generation
