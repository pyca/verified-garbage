import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackCounter
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackGroups
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

def bodyTemps : List VReg := [.v0,.v1,.v2,.v4,.v5,.v6,.v7,.v24]

structure ParseReady (d : Nat) (s : State) : Prop where
  constants : ParseConstants d s
  indices : ∀ g<4, s.v Unpack.idxRegs[g]! = gatherIndex d g

theorem ParseReady.keep {d : Nat} {s t : State} (h : ParseReady d s)
    (hv : ∀ v, v∈initVectors → t.v v=s.v v) : ParseReady d t := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro e he; rw [hv .v23 (by decide)]; exact h.constants.powers e he
  · intro e he; rw [hv .v22 (by decide)]; exact h.constants.mask e he
  · intro e he; rw [hv .v21 (by decide)]; exact h.constants.bound e he
  · intro e he; rw [hv .v20 (by decide)]; exact h.constants.modulus e he
  · intro g hg
    rw [hv _ (by rcases (show g=0 ∨ g=1 ∨ g=2 ∨ g=3 by omega) with rfl | rfl | rfl | rfl <;> decide)]
    exact h.indices g hg

structure BodyPost (d : Nat) (s t : State) : Prop where
  ready : ParseReady d t
  input : t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (2*d)
  output : t.gpr .x4=s.gpr .x4+64
  count : t.gpr .x11=s.gpr .x11-1
  gpr : ∀ r, r≠.x0 → r≠.x4 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ v, v∉bodyTemps → t.v v=s.v v
  frame : Frame [⟨s.gpr .x4,64⟩] s.mem t.mem
  values : ∀ g<4, ∀ e<4,
    (vword (t.mem.read (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) e).toNat =
      (2^(d-1)+8380417-fieldValue s.mem (s.gpr .x0) d (4*g+e))%8380417
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

private theorem body_code {d : Nat} (hd : d=18 ∨ d=20) : Unpack.body d =
    ([.ldrq .v0 .x0 0,.ldrq .v1 .x0 16,.addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0] : List Instr) ++
    ((List.range 4).flatMap (Unpack.one d)) ++
    ([.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,.subImm .x .x11 .x11 1] : List Instr) := by
  simp only [Unpack.body,ite_eq_right (by omega : ¬ d=10),List.cons_append,List.nil_append]

/-- One fixed-count parser iteration consumes sixteen packed fields and
produces their canonical coefficients in sixty-four bytes. -/
theorem body_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) (hr : ParseReady d s)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16)
    (hw : ∀ g<4, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block (Unpack.body d)) s (BodyPost d s) := by
  rw [body_code hd,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok s hd h0 h1 h2) ?_
  intro a ha
  have ac : ParseReady d a := hr.keep fun v hv => ha.2.2.2.2.1 v
    (by intro h; subst v; simp [initVectors] at hv)
    (by intro h; subst v; simp [initVectors] at hv)
    (by intro h; subst v; simp [initVectors] at hv)
  rw [WP.block_append_iff]
  refine WP.mono (groups_ok a hd (Nat.le_refl 4) ac.indices ?_) ?_
  · intro g hg
    simpa only [ha.2.2.2.2.2.2.2.1,ha.2.2.2.1 .x4 (by decide)] using hw g hg
  intro b hb
  have bc : ParseReady d b := ac.keep fun v hv => hb.1.vec v
    (by simp only [initVectors,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (advance_ok b hd) ?_
  intro t ht
  refine ⟨bc.keep (fun v _ => congrFun ht.2.2.2.2.1 v),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.1,hb.1.gpr,ha.2.2.2.1 .x0 (by decide)]
  · rw [ht.2.1,hb.1.gpr,ha.2.2.2.1 .x4 (by decide)]
  · rw [ht.2.2.1,hb.1.gpr,ha.2.2.2.1 .x11 (by decide)]
  · intro r h0 h4 h9 h11
    rw [ht.2.2.2.1 r h0 h4 h11,hb.1.gpr,ha.2.2.2.1 r h9]
  · intro v hv
    have hn : v≠.v0 ∧ v≠.v1 ∧ v≠.v2 ∧ v∉groupTemps := by
      simpa only [bodyTemps,groupTemps,List.mem_cons,List.not_mem_nil,or_false,not_or] using hv
    rw [ht.2.2.2.2.1,hb.1.vec v hn.2.2.2,ha.2.2.2.2.1 v hn.1 hn.2.1 hn.2.2.1]
  · rw [ht.2.2.2.2.2.1,hb.2,← ha.2.2.2.2.2.1,← ha.2.2.2.1 .x4 (by decide)]
    exact groupMem_frame a d (Nat.le_refl 4)
  · intro g hg e he
    rw [ht.2.2.2.2.2.1,hb.2,← ha.2.2.2.1 .x4 (by decide),groupMem_read a d (Nat.le_refl 4) hg]
    exact parsed_word hd hg he ac.constants ha.1 ha.2.1 ha.2.2.1
  · exact ht.2.2.2.2.2.2.1.trans (hb.1.rd.trans ha.2.2.2.2.2.2.1)
  · exact ht.2.2.2.2.2.2.2.1.trans (hb.1.wr.trans ha.2.2.2.2.2.2.2.1)
  · exact ht.2.2.2.2.2.2.2.2.trans (hb.1.sp.trans ha.2.2.2.2.2.2.2.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
