import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowTail2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

def lowPairClobs (r q : VReg) : List VReg := [.v27,.v29,.v24,.v25,r,q,.v26,.v28,.v30]

theorem lowPair_compose (g : Nat) (r q : VReg) (off : Nat) :
    lowPairBlocks g r q off=lowInputTwo r q off++lowHbTwo g r q++lowTailTwo r q off := by
  simp only [lowPairBlocks,lowInputTwo,lowHbTwo,lowTailTwo,lowMlsTwo,List.append_assoc]

theorem lowPair_ok {g : Nat} (hg : IsG g) {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (rd0 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (rd1 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v ha hb la lb,StepKeep (lowPairClobs r q) s v →
      v.mem=lowPairWrites s off ha hb la lb →
      (∀e<4,vword ha e=lowHighWord g (lowInputWord s r off e)) →
      (∀e<4,vword hb e=lowHighWord g (lowInputWord s q (off+128) e)) →
      (∀e<4,vword la e=Response.reduceWord
        (lowInputWord s r off e-lowHighWord g (lowInputWord s r off e)*vword (s.v .v15) e)) →
      (∀e<4,vword lb e=Response.reduceWord
        (lowInputWord s q (off+128) e-lowHighWord g (lowInputWord s q (off+128) e)*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| Response.normMask (vword la e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        Response.normMask (vword lb e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowPairBlocks g r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  rw [lowPair_compose]
  simp only [List.append_assoc]
  refine lowInputTwo_ok hr hq hrq ho rd0 rd1 hmod hc fun u hu hua hub => ?_
  have uk (d : VReg) (hd : d∈[.v11,.v12,.v13,.v14]) : u.v d=s.v d := by
    refine hu.get d ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · simp [Ne.symm (rn .v11 (by decide)),Ne.symm (qn .v11 (by decide))]
    · simp [Ne.symm (rn .v12 (by decide)),Ne.symm (qn .v12 (by decide))]
    · simp [Ne.symm (rn .v13 (by decide)),Ne.symm (qn .v13 (by decide))]
    · simp [Ne.symm (rn .v14 (by decide)),Ne.symm (qn .v14 (by decide))]
  refine lowHbTwo_ok hg (rn .v26 (by decide)) (qn .v25 (by decide))
    (qn .v26 (by decide)) (qn .v28 (by decide))
    (by simpa only [uk .v11 (by simp)] using h11)
    (by simpa only [uk .v12 (by simp)] using h12)
    (by simpa only [uk .v13 (by simp)] using h13)
    (by simpa only [uk .v14 (by simp)] using h14) fun v hv hva hvb => ?_
  have hk : VChg [.v27,.v29,.v24,.v25,r,q,.v26,.v28] s v := (hu.trans hv).mono (by
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  have vk (d : VReg) (hd : d∈[.v8,.v9,.v10,.v15,.v30,.v31]) : v.v d=s.v d := by
    refine hk.get d ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Ne.symm (rn .v8 (by decide)),Ne.symm (qn .v8 (by decide))]
    · simp [Ne.symm (rn .v9 (by decide)),Ne.symm (qn .v9 (by decide))]
    · simp [Ne.symm (rn .v10 (by decide)),Ne.symm (qn .v10 (by decide))]
    · simp [Ne.symm (rn .v15 (by decide)),Ne.symm (qn .v15 (by decide))]
    · simp [Ne.symm (rn .v30 (by decide)),Ne.symm (qn .v30 (by decide))]
    · simp [Ne.symm (rn .v31 (by decide)),Ne.symm (qn .v31 (by decide))]
  have va (e : Nat) (he : e<4) : vword (v.v .v24) e=lowInputWord s r off e := by
    rw [hv.get .v24 (by simp [Ne.symm (qn .v24 (by decide))])]; exact hua e he
  have vb (e : Nat) (he : e<4) : vword (v.v r) e=lowInputWord s q (off+128) e := by
    rw [hv.get r (by simp [rn .v25 (by decide),hrq,rn .v26 (by decide),rn .v28 (by decide)])]; exact hub e he
  have higha (e : Nat) (he : e<4) : vword (v.v .v26) e=lowHighWord g (lowInputWord s r off e) := by rw [hva e he,hua e he]
  have highb (e : Nat) (he : e<4) : vword (v.v .v28) e=lowHighWord g (lowInputWord s q (off+128) e) := by rw [hvb e he,hub e he]
  have hp : ∀d∈preservedV,d∉[.v27,.v29,.v24,.v25,r,q,.v26,.v28] := by
    intro d hd hm
    have h1 := lowPair_preserved hr hq d hd
    have h2 := (by decide : ∀d∈preservedV,d∉[.v26,.v27,.v28,.v29]) d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  have frame := hk.keep hp
  refine lowTailTwo_ok hr hq hrq ho
    (by rw [frame.wr,frame.get .x15]; exact wh0)
    (by rw [frame.wr,frame.get .x15]; exact wh1)
    (by rw [frame.wr,frame.get .x16]; exact wl0)
    (by rw [frame.wr,frame.get .x16]; exact wl1)
    (by simpa only [vk .v31 (by simp)] using hmod)
    (by simpa only [vk .v8 (by simp)] using hc) fun w la lb hw hm hla hlb hf =>
      k w (v.v .v26) (v.v .v28) la lb (((StepKeep.ofChg hk hp).trans hw).mono (by
        intro d hd; simp only [lowPairClobs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ higha highb ?_ ?_ ?_
  · rw [hm]
    simp only [lowPairWrites,hk.mem,hk.gpr]
  · intro e he; rw [hla e he,va e he,higha e he,vk .v15 (by simp)]
  · intro e he; rw [hlb e he,vb e he,highb e he,vk .v15 (by simp)]
  · intro e he; rw [hf e he,vk .v30 (by simp),vk .v9 (by simp),vk .v10 (by simp)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
