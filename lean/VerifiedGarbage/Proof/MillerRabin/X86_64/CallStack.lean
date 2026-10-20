module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The return address of the round's Montgomery calls

Within the round's two frames, a call stores its return address in the 8
bytes below the frames' 112 (`hole`), 120 bytes below the caller's `rsp`:
apart from the frames' slots and from the workspace, which the round's
precondition keeps 120 bytes from `rsp`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64

theorem entered_hole (s : State) : hole ((entered s).gpr .rsp) = ⟨s.gpr .rsp - 120#64, 8⟩ := by
  rw [hole, entered_rsp]
  congr 1
  bv_omega

theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl

/-- No buffer of the framed body reaches the calls' return address. -/
theorem entered_clear {s : State} {B : Addr} {Z : Nat} (hrd : s.rd = []) (hwr : s.wr = [⟨B, Z⟩])
    (hd : Region.Disjoint ⟨s.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩) :
    Clear (hole ((entered s).gpr .rsp)) (entered s) := by
  intro r hr
  rw [entered_hole]
  rw [entered_rd, hrd, List.nil_append, entered_wr, hwr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h112 : s.gpr .rsp - 112#64 = s.gpr .rsp - 120#64 + BitVec.ofNat 64 8 :=
    Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 112 ≤ 120)
  have h104 : s.gpr .rsp - 104#64 = s.gpr .rsp - 120#64 + BitVec.ofNat 64 16 :=
    Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 104 ≤ 120)
  rcases hr with rfl | rfl | rfl
  · rw [h112]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [h104]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (hd.sub_left (Offset.sub_below _ (by decide : 120 ≤ 120) (by decide : 120 - 120 + 8 ≤ 120))).symm

end VG.Proof.MillerRabin.X86_64
