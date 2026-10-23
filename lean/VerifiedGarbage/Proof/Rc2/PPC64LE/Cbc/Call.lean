module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Cbc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Rc2.PPC64LE.Lit

/-! # RC2-CBC on PPC64LE: the calls of the block function -/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE.Cbc

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE VG.Impl.Rc2.PPC64LE.Cbc

theorem block_exec (d : Spec.Rc2.Direction) : ∀ s, (blockC d).pre s →
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  cases d
  · exact block_ok .encrypt (by lit_decide) (by lit_decide) (by rw [← Code.allInstrs_eq]; lit_decide)
  · exact block_ok .decrypt (by lit_decide) (by lit_decide) (by rw [← Code.allInstrs_eq]; lit_decide)

theorem blockCall_eq (d : Spec.Rc2.Direction) :
    ∃ nm, blockCall d = .call nm (blockCode d) := by cases d <;> exact ⟨_, rfl⟩

theorem blockCode_noFrames (d : Spec.Rc2.Direction) : (blockCode d).noFrames = true := by
  cases d
  · exact (by lit_decide : encryptBlock.noFrames = true)
  · exact (by lit_decide : decryptBlock.noFrames = true)

/-- A call of the block function on the block at `p`, with the schedule at
`T` and the working space at `W`. -/
theorem call_run (d : Spec.Rc2.Direction) (u : State) {T p W : Addr} (h3 : u.gpr .r3 = T) (h4 : u.gpr .r4 = p)
    (h5 : u.gpr .r5 = W) (hc : Covers ([⟨T, 128⟩] ++ [⟨p, 8⟩, ⟨W, 256⟩]) (u.rd ++ u.wr))
    (hw : Covers [⟨p, 8⟩, ⟨W, 256⟩] u.wr) :
    WP isa (blockCall d) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨p, 8⟩, ⟨W, 256⟩] u.mem u'.mem ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      Spec.Rc2.blockAt u'.mem p = cipher d (Spec.Rc2.scheduleAt u.mem T) (Spec.Rc2.blockAt u.mem p) := by
  obtain ⟨nm, e⟩ := blockCall_eq d
  rw [e]
  refine WP.call (k := blockC d) (block_exec d) (rd := [⟨T, 128⟩]) (wr := [⟨p, 8⟩, ⟨W, 256⟩]) ?_ hc hw
    (fun s' hr hwr _ hf hp _ hpost => ⟨hr, hwr, hf, hp, ?_⟩) (blockCode_noFrames d)
  · show [(⟨T, 128⟩ : Region)] = [⟨u.callEntry.gpr .r3, 128⟩] ∧
      [(⟨p, 8⟩ : Region), ⟨W, 256⟩] = [⟨u.callEntry.gpr .r4, 8⟩, ⟨u.callEntry.gpr .r5, 256⟩]
    rw [State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide),
      h3, h4, h5]
    exact ⟨rfl, rfl⟩
  · have := hpost
    simp only [blockC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [State.callEntry_gpr u (by decide), State.callEntry_gpr u (by decide), h3, h4] at this
    exact this

end VG.Proof.Rc2.PPC64LE.Cbc
