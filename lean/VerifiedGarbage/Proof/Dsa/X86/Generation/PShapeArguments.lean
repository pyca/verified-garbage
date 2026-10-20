module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Select the low p-length suffix of the concatenated contributions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem pShapeFromFrameArgs_ok {s : State} {base : Addr} {hashes parent : BitVec 32}
    (F : SearchFrame s base) (savedHashes : s.mem.readW (off base 16) 32 = hashes)
    (savedParent : s.mem.readW (off base 20) 32 = parent) (len count plen : Nat) :
    WP isa (.block (pShapeFromFrameArgs len count plen)) s fun t =>
      t.gpr .esi = hashes + BitVec.ofNat 32 ((count + 1) * len - plen) ∧
      t.gpr .edi = parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped ∧
      t.mem = s.mem ∧ Keeps [.esi, .edi] s t := by
  unfold pShapeFromFrameArgs
  refine wp_movS (v := hashes) (by rw [F.readSlot (by decide : 4 < 37), savedHashes]) fun a sa _ =>
    wp_addi fun b ab => ?_
  have Kb := sa.keeps.trans ab.keeps
  have Fb := F.keeps Kb (by decide)
  refine wp_movS (v := parent) (by rw [Fb.readSlot (by decide : 5 < 37), ab.mem, sa.mem, savedParent]) fun c bc _ =>
    wp_addi fun t ct => WP.block_nil ?_
  exact ⟨(ct.other _ (by decide)).trans ((bc.other _ (by decide)).trans (by rw [ab.gpr, sa.gpr])),
    by rw [ct.gpr, bc.gpr], ct.mem.trans (bc.mem.trans (ab.mem.trans sa.mem)),
    (((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bc.keeps.mono (by decide))).trans (ct.keeps.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
