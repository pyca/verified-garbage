import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowHigh

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowInput (raw a t other : VReg) (off : Nat) : List Instr :=
 ([.ldrq other .x15 off,.vop (.sub .s4 a other raw)] : List Instr) ++
 reduceRegs a t ++ lowCadd a t

def lowInputWord (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
 Inverse.signCorrected (Response.reduceWord
  (vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v raw) e))

/-- The second lane may reuse its raw-product register as a temporary after subtraction. -/
theorem lowInput_ok {raw a t other : VReg} {off : Nat}
    (hat : a≠t) (hor : other≠raw)
    (hregs : ∀r∈[other,a,t],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,VChg [other,a,t] s u →
      (∀e<4,vword (u.v a) e=lowInputWord s raw off e) → WP isa (.block rest) u Q) :
    WP isa (.block (lowInput raw a t other off++rest)) s Q := by
  simp only [lowInput,List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun u hu => wp_vop (d := a) rfl fun v hv => ?_
  have hk : VChg [other,a] s v := (hu.chg.trans hv.chg).mono (by simp)
  have hq' : ∀e<4,vword (v.v .v31) e=8380417#32 := by
    intro e he; rw [hk.get .v31 (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨Ne.symm (hregs other (by simp)).2,Ne.symm (hregs a (by simp)).2⟩)]
    exact hq e he
  have hc' : ∀e<4,vword (v.v .v8) e=4194304#32 := by
    intro e he; rw [hk.get .v8 (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨Ne.symm (hregs other (by simp)).1,Ne.symm (hregs a (by simp)).1⟩)]
    exact hc e he
  refine reduceRegs_ok hat (hregs t (by simp)).2 hq' hc' fun w hw hval => ?_
  have hk' : VChg [other,a,t] s w := (hk.trans hw).mono (by
    intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  refine lowCadd_ok hat (hregs t (by simp)).2
    (by intro e he; rw [hk'.get .v31 (by intro hm; exact (hregs .v31 hm).2 rfl)]; exact hq e he)
    fun y hy hcorr => k y ((hk'.trans hy).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  intro e he
  rw [hcorr e he,hval e he,hv.v,VG.AArch64.vword_map2 _ _ _ he,hu.v,hu.get raw (Ne.symm hor)]
  rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired
