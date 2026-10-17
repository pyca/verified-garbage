module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.Offset

/-! # The Montgomery calls' return-address slot is outside the saved frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64

theorem entered_clear {s : State} {B : Addr} {Z : Nat}
    (hr : s.rd = []) (hw : s.wr = [⟨B, Z⟩])
    (hd : Region.Disjoint ⟨s.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩) :
    Clear (hole ((entered s).gpr .rsp)) (entered s) := by
  have he : s.gpr .rsp - 112#64 - 8#64 = s.gpr .rsp - 120#64 := by bv_omega
  intro r hm
  simp only [entered, pushed_rd, hr, List.nil_append] at hm
  rw [← entered, entered_wr, hw] at hm
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [entered_rsp]
  change r.Disjoint ⟨s.gpr .rsp - 112#64 - 8#64, 8⟩
  rw [he]
  rcases hm with rfl | rfl | rfl
  · rw [Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 112 ≤ 120)]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · rw [Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 104 ≤ 120)]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (hd.sub_left (Region.sub_prefix (by decide : 8 ≤ 120))).symm

end VG.Proof.MillerRabin.X86_64
