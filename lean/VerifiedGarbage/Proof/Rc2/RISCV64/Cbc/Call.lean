module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Block
public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit

/-! # RC2-CBC on RISC-V: the calls of the block function -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem block_exec (d : Spec.Rc2.Direction) : ∀ s, (blockC d).pre s →
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  cases d
  · exact block_ok .encrypt (by lit_decide) (by lit_decide)
  · exact block_ok .decrypt (by lit_decide) (by lit_decide)

theorem blockCall_eq (d : Spec.Rc2.Direction) :
    ∃ nm, blockCall d = .call nm (blockCode d) := by cases d <;> exact ⟨_, rfl⟩

theorem blockCode_noFrames (d : Spec.Rc2.Direction) : (blockCode d).noFrames = true := by
  cases d
  · exact (by lit_decide : encryptBlock.noFrames = true)
  · exact (by lit_decide : decryptBlock.noFrames = true)

/-- A call of the block function on the block at `p`, with the schedule at
`T` and the working space at `W`. -/
theorem call_run (d : Spec.Rc2.Direction) (u : State) {T p W : Addr} (h3 : u.gpr .a0 = T) (h4 : u.gpr .a1 = p)
    (h5 : u.gpr .a2 = W) (hal : W.toNat % 8 = 0) (hfp : p.toNat + 8 ≤ 2 ^ 64) (hfw : W.toNat + 256 ≤ 2 ^ 64)
    (hTW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 256⟩) (hpW : (⟨p, 8⟩ : Region).Disjoint ⟨W, 256⟩)
    (hc : Covers ([⟨T, 128⟩] ++ [⟨p, 8⟩, ⟨W, 256⟩]) (u.rd ++ u.wr))
    (hw : Covers [⟨p, 8⟩, ⟨W, 256⟩] u.wr) :
    WP isa (blockCall d) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨p, 8⟩, ⟨W, 256⟩] u.mem u'.mem ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      Spec.Rc2.blockAt u'.mem p = cipher d (Spec.Rc2.scheduleAt u.mem T) (Spec.Rc2.blockAt u.mem p) := by
  obtain ⟨nm, e⟩ := blockCall_eq d
  rw [e]
  have e3 : u.callEntry.gpr .a0 = T := by rw [State.callEntry_gpr u (by decide), h3]
  have e4 : u.callEntry.gpr .a1 = p := by rw [State.callEntry_gpr u (by decide), h4]
  have e5 : u.callEntry.gpr .a2 = W := by rw [State.callEntry_gpr u (by decide), h5]
  refine WP.call (k := blockC d) (block_exec d) (rd := [⟨T, 128⟩]) (wr := [⟨p, 8⟩, ⟨W, 256⟩]) ?_ hc hw
    (fun s' hr hwr _ hf hp _ hpost => ⟨hr, hwr, hf, hp, ?_⟩) (blockCode_noFrames d)
  · show [(⟨T, 128⟩ : Region)] = [⟨u.callEntry.gpr .a0, 128⟩] ∧
      [(⟨p, 8⟩ : Region), ⟨W, 256⟩] = [⟨u.callEntry.gpr .a1, 8⟩, ⟨u.callEntry.gpr .a2, 256⟩] ∧
      (u.callEntry.gpr .a2).toNat % 8 = 0 ∧ (u.callEntry.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧
      (u.callEntry.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      (⟨u.callEntry.gpr .a0, 128⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩ ∧
      (⟨u.callEntry.gpr .a1, 8⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩
    rw [e3, e4, e5]
    exact ⟨rfl, rfl, hal, hfp, hfw, hTW, hpW⟩
  · have := hpost
    simp only [blockC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [e3, e4] at this
    exact this

end VG.Proof.Rc2.RISCV64.Cbc
