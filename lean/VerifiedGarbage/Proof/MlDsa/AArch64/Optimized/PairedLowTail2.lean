import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowMls2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowTailTwo (r q : VReg) (off : Nat) : List Instr :=
 storeTwo .v26 .v28 .x15 off ++ lowMlsTwo r q ++ storeTwo .v24 r .x16 off ++ normTwo r q

def lowPairWrites (s : State) (off : Nat) (ha hb la lb : BitVec 128) : Mem :=
 (((s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 ha).write
   (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16 hb).write
   (s.gpr .x16+BitVec.ofNat 64 off) 16 la).write
   (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16 lb

theorem lowPair_preserved {r q : VReg} (hr : r∉lowReserved) (hq : q∉lowReserved) :
    ∀d∈preservedV,d∉[.v24,.v25,r,q,.v30] := by
  have hp : ∀d∈preservedV,d∈lowReserved := by decide
  have ht : ∀d∈preservedV,d∉[.v24,.v25,.v30] := by decide
  intro d hd hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact ht .v24 hd (by simp)
  · exact ht .v25 hd (by simp)
  · exact hr (hp _ hd)
  · exact hq (hp _ hd)
  · exact ht .v30 hd (by simp)

theorem lowTailTwo_ok {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v la lb,StepKeep [.v24,.v25,r,q,.v30] s v →
      v.mem=lowPairWrites s off (s.v .v26) (s.v .v28) la lb →
      (∀e<4,vword la e=Response.reduceWord
        (vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e)) →
      (∀e<4,vword lb e=Response.reduceWord
        (vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| Response.normMask (vword la e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        Response.normMask (vword lb e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowTailTwo r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hp := lowPair_preserved hr hq
  unfold lowTailTwo
  simp only [List.append_assoc]
  refine storeTwo_ok ho wh0 wh1 fun u hu huv hum => ?_
  refine lowMlsTwo_ok hr hq hrq (by simpa only [huv] using hmod)
    (by simpa only [huv] using hc) fun v hv hva hvb => ?_
  have hvkeep : StepKeep [.v24,.v25,r,q] u v := StepKeep.ofChg hv (by
    intro d hd hm; exact hp d hd (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  have hk : StepKeep [.v24,.v25,r,q] s v := (hu.trans hvkeep).mono (by simp)
  refine storeTwo_ok ho
    (by rw [hk.keep.wr,hk.keep.get .x16]; exact wl0)
    (by rw [hk.keep.wr,hk.keep.get .x16]; exact wl1) fun w hw hwv hwm => ?_
  refine normTwo_ok (rn .v25 (by decide)) (qn .v25 (by decide))
    (qn .v10 (by decide)) (qn .v30 (by decide)) fun z hz hzf => ?_
  have hzkeep : StepKeep [.v25,q,.v30] w z := StepKeep.ofChg hz (by
    intro d hd hm; exact hp d hd (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  refine k z (v.v .v24) (v.v r) (((hk.trans hw).trans hzkeep).mono (by
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_ ?_ ?_
  · rw [hz.mem,hwm,hv.mem,hum,hk.keep.get .x16]
    rfl
  · simpa only [huv] using hva
  · simpa only [huv] using hvb
  · intro e he
    rw [hzf e he,hwv,
      hk.vec .v30 (by simp [Ne.symm (rn .v30 (by decide)),Ne.symm (qn .v30 (by decide))]),
      hk.vec .v9 (by simp [Ne.symm (rn .v9 (by decide)),Ne.symm (qn .v9 (by decide))]),
      hk.vec .v10 (by simp [Ne.symm (rn .v10 (by decide)),Ne.symm (qn .v10 (by decide))])]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
