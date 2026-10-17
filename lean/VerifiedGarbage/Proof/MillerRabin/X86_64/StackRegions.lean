module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Stack
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The saved frames provide three disjoint writable regions -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem entered_kw {s : State} {B : Addr} {Z : Nat}
    (hw : s.wr = [⟨B, Z⟩]) (hz : 256 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64)
    (hd : Region.Disjoint ⟨s.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩) :
    KW B (entered s).wr := by
  have h8 : Region.Disjoint ⟨s.gpr .rsp - 112#64, 8⟩ ⟨B, Z⟩ :=
    hd.sub_left (Offset.sub_below _ (a := 112) (n := 8) (b := 120) (m := 120) (by decide) (by decide))
  have h104 : Region.Disjoint ⟨s.gpr .rsp - 104#64, 104⟩ ⟨B, Z⟩ :=
    hd.sub_left (Offset.sub_below _ (a := 104) (n := 104) (b := 120) (m := 120) (by decide) (by decide))
  have hpair : Region.Disjoint ⟨s.gpr .rsp - 112#64, 8⟩ ⟨s.gpr .rsp - 104#64, 104⟩ := by
    rw [Offset.sub_ofNat_eq (s.gpr .rsp) (by decide : 104 ≤ 112)]
    exact Offset.base_disjoint _ (by decide) (by decide)
  refine ⟨⟨s.gpr .rsp - 112#64, 8⟩, ⟨s.gpr .rsp - 104#64, 104⟩, Z,
    ?_, by change 8 ≤ 104; decide, hz, ?_, ?_⟩
  · rw [entered_wr, hw]
    rfl
  · simp [entered_wr, hw, List.pairwise_cons, hpair, h8, h104]
  · simp only [entered_wr, hw, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega_arith

end VG.Proof.MillerRabin.X86_64
