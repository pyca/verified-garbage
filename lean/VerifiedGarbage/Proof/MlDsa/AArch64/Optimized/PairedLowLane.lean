import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowTail

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

/-- Complete measured lane: both output vectors and the rejection mask. -/
theorem r0Lane_ok {g : Nat} (hg : IsG g) {raw a t h other : VReg} {off : Nat}
    (hat : a≠t) (hah : a≠h) (hht : h≠t) (hor : other≠raw)
    (havoid : ∀r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31],r∉[other,a,t,h])
    (hpres : ∀r∈preservedV,r∉[other,a,t,h,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀u high low,StepKeep [other,a,t,h,.v30] s u →
      u.mem=(s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 high).write
        (s.gpr .x16+BitVec.ofNat 64 off) 16 low →
      (∀e<4,vword high e=lowHighWord g (lowInputWord s raw off e)) →
      (∀e<4,vword low e=Response.reduceWord
        (lowInputWord s raw off e-lowHighWord g (lowInputWord s raw off e)*vword (s.v .v15) e)) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword low e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane g raw a t h other off++rest)) s Q := by
  rw [r0Lane_blocks]
  simp only [List.append_assoc]
  have avoid (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31])
      (x : VReg) (hx : x∈[other,a,t,h]) : x≠r := by
    intro he; subst x; exact havoid r hr hx
  refine lowInput_ok hat hor (by
    intro r hr
    exact ⟨avoid .v8 (by simp) r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only),
      avoid .v31 (by simp) r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)⟩)
    ho hread hq hc fun u hu hw => ?_
  have uk (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31]) : u.v r=s.v r :=
    hu.get r (by intro hm; exact havoid r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  refine lowHb_ok hg hht (avoid .v12 (by simp) h (by simp))
    (avoid .v13 (by simp) h (by simp)) (avoid .v14 (by simp) h (by simp))
    (by simpa only [uk .v11 (by simp)] using h11)
    (by simpa only [uk .v12 (by simp)] using h12)
    (by simpa only [uk .v13 (by simp)] using h13)
    (by simpa only [uk .v14 (by simp)] using h14)
    fun v hv hhigh => ?_
  have hkeep : VChg [other,a,t,h] s v := (hu.trans hv).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  have vk (r : VReg) (hr : r∈[.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30,.v31]) : v.v r=s.v r :=
    hkeep.get r (havoid r hr)
  have va (e : Nat) (he : e<4) : vword (v.v a) e=lowInputWord s raw off e := by
    rw [hv.get a (by simp [hah,hat])]; exact hw e he
  have vh (e : Nat) (he : e<4) : vword (v.v h) e=lowHighWord g (lowInputWord s raw off e) := by
    rw [hhigh e he,hw e he]
  have hp : ∀r∈preservedV,r∉[other,a,t,h] := by
    intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  have frame := hkeep.keep hp
  refine lowTail_ok hat (avoid .v31 (by simp) a (by simp))
    (avoid .v8 (by simp) a (by simp)) (avoid .v31 (by simp) t (by simp))
    (by
      intro r hr hm
      exact havoid r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    (by intro r hr hm; exact hpres r hr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
    ho (by rw [frame.wr,frame.get .x15]; exact hr)
    (by rw [frame.wr,frame.get .x16]; exact hl)
    (by simpa only [vk .v31 (by simp)] using hq)
    (by simpa only [vk .v8 (by simp)] using hc)
    fun w low hwkeep hm hlw hf => k w (v.v h) low
      (((StepKeep.ofChg hkeep hp).trans hwkeep).mono (by
        intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ vh ?_ ?_
  · rw [hm,hkeep.mem,frame.get .x15,frame.get .x16]
  · intro e he; rw [hlw e he,va e he,vh e he,vk .v15 (by simp)]
  · intro e he; rw [hf e he,vk .v30 (by simp),vk .v9 (by simp),vk .v10 (by simp)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
