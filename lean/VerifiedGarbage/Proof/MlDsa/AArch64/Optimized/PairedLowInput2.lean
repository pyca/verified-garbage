import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowHb2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def lowReserved : List VReg :=
 [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31]

def lowInputTwo (r q : VReg) (off : Nat) : List Instr :=
 lowLoadTwo r q off ++ reduceTwo .v24 .v25 r q ++ caddTwo .v24 .v25 r q

theorem lowInputTwo_ok {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hread' : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [.v27,.v29,.v24,.v25,r,q] s v →
      (∀e<4,vword (v.v .v24) e=lowInputWord s r off e) →
      (∀e<4,vword (v.v r) e=lowInputWord s q (off+128) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowInputTwo r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hr24 := rn .v24 (by decide)
  have hr25 := rn .v25 (by decide)
  have hq24 := qn .v24 (by decide)
  have hq25 := qn .v25 (by decide)
  have hregs : ∀d∈[.v24,.v25,r,q],d≠.v8 ∧ d≠.v31 := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact ⟨rn .v8 (by decide),rn .v31 (by decide)⟩
    · exact ⟨qn .v8 (by decide),qn .v31 (by decide)⟩
  unfold lowInputTwo
  simp only [List.append_assoc]
  refine lowLoadTwo_ok hr24 (rn .v27 (by decide)) (rn .v29 (by decide))
    hq24 (qn .v27 (by decide)) (qn .v29 (by decide)) ho hread hread' fun u hu ha hb => ?_
  have huq : u.v .v31=s.v .v31 := hu.get .v31 (by simp [Ne.symm (rn .v31 (by decide))])
  have huc : u.v .v8=s.v .v8 := hu.get .v8 (by simp [Ne.symm (rn .v8 (by decide))])
  refine reduceTwo_ok (by decide) (Ne.symm hr24) (Ne.symm hq24) (Ne.symm hr25) (Ne.symm hq25) hrq hregs
    (by simpa only [huq] using hmod) (by simpa only [huc] using hc) fun v hv hva hvb => ?_
  have hk : VChg [.v27,.v29,.v24,.v25,r,q] s v := (hu.trans hv).mono (by
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  refine caddTwo_ok (by decide) (Ne.symm hr24) (Ne.symm hq24) (Ne.symm hr25) (Ne.symm hq25) hrq hregs
    (by intro e he; rw [hk.get .v31 (by simp [Ne.symm (rn .v31 (by decide)),Ne.symm (qn .v31 (by decide))])]; exact hmod e he)
    fun w hw hwa hwb => k w ((hk.trans hw).mono (by
      intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
  · intro e he; rw [hwa e he,hva e he,ha e he]; rfl
  · intro e he; rw [hwb e he,hvb e he,hb e he]; rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired
