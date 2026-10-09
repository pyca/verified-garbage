import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowInput2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def lowMlsTwo (r q : VReg) : List Instr := mlsTwo r ++ reduceTwo .v24 .v25 r q

theorem lowMlsTwo_ok {r q : VReg} (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [.v24,.v25,r,q] s v →
      (∀e<4,vword (v.v .v24) e=Response.reduceWord
        (vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v r) e=Response.reduceWord
        (vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowMlsTwo r q++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hregs : ∀d∈[.v24,.v25,r,q],d≠.v8 ∧ d≠.v31 := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact ⟨rn .v8 (by decide),rn .v31 (by decide)⟩
    · exact ⟨qn .v8 (by decide),qn .v31 (by decide)⟩
  unfold lowMlsTwo
  rw [List.append_assoc]
  refine mlsTwo_ok (rn .v24 (by decide)) fun u hu ha hb => ?_
  refine reduceTwo_ok (by decide) (Ne.symm (rn .v24 (by decide))) (Ne.symm (qn .v24 (by decide)))
    (Ne.symm (rn .v25 (by decide))) (Ne.symm (qn .v25 (by decide))) hrq hregs
    (by intro e he; rw [hu.get .v31 (by simp [Ne.symm (rn .v31 (by decide))])]; exact hmod e he)
    (by intro e he; rw [hu.get .v8 (by simp [Ne.symm (rn .v8 (by decide))])]; exact hc e he)
    fun v hv hva hvb => k v ((hu.trans hv).mono (by
      intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
  · intro e he; rw [hva e he,ha e he]
  · intro e he; rw [hvb e he,hb e he]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
