import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Split a straight-line prefix while retaining its continuation. -/
theorem blockPrefix {P Q : State → State → Prop} {a b : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) c)) Q) :
    RelCT isa P (.seq (.block (a++b)) c) Q := by
  intro s t tr ur s' t' hp es et
  cases es with
  | seq ea ec =>
    cases et with
    | seq eb ed =>
      rw [Exec.block_iff,execBlock_append] at ea eb
      obtain ⟨⟨sa,ta⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp ea
      obtain ⟨⟨sb,tb⟩,hc,hd⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨⟨ua,va⟩,he,hf⟩ := Option.bind_eq_some_iff.mp eb
      obtain ⟨⟨ub,vb⟩,hg,hh⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hd hh
      obtain ⟨rfl,rfl⟩ := hd
      obtain ⟨rfl,rfl⟩ := hh
      obtain ⟨hl,hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha) (.seq (.block hc) ec))
        (.seq (.block he) (.seq (.block hg) ed))
      exact ⟨by simpa only [List.append_assoc] using hl,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
