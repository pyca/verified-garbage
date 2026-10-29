module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRound
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFlags
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskFour

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitialized
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
/-! ## From `BoundedFourCore.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourAdaptive.lean`, which only this module imported.
section

/-! ## From `BoundedFourRunFlags.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

theorem SamplerRun.only {σ s t : State} {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (h : SamplerRun σ s A L) {rs : List Reg} (ht : Only rs s t)
    (hr : ∀r∈[Reg.x19,.x20,.x21,.x30],r∉rs) : SamplerRun σ t A L := by
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp)
    ht.rd ht.wr ht.sp (fun r h=>ht.get r (hr r h)),?_,?_,?_,?_⟩ <;>
    rw [ht.mem]
  · exact h.pair0
  · exact h.pair1
  · exact h.table
  · exact h.fields

def countFlag (L : Nat→List Zq) : BitVec 64 := foldedFlags (fun i=>BitVec.ofNat 64 (256-(L i).length)) 3

theorem countFlag_zero {L : Nat→List Zq} (h : ∀i<4,(L i).length≤256) :
    countFlag L=0#64 ↔∀i<4,(L i).length=256 := by
  rw [countFlag,ResidentRej.foldedFlags_zero]
  constructor
  · intro hz i hi
    have hh:=congrArg BitVec.toNat (hz i hi)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hh
    change 256-(L i).length=0 at hh
    have:=h i hi
    omega
  · intro hz i hi
    rw [hz i hi]

theorem flagsStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) s fun t=>
      SamplerRun σ t A L ∧t.gpr .x27=countFlag L := by
  refine WP.mono (flags_ok hs.env.x19 hs.fields.count
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega))) fun t ⟨⟨ht,hflag⟩,_⟩=>?_
  exact ⟨hs.only ht (by decide),hflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAdaptive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem SamplerRun.congr {σ s : State} {A : Nat→Spec.Sha3.State} {L K : Nat→List Zq}
    (h : SamplerRun σ s A L) (he : ∀i<4,L i=K i) : SamplerRun σ s A K := by
  refine ⟨h.env,h.pair0,h.pair1,h.table,⟨?_,?_,?_⟩⟩
  · intro i hi; rw [←he i hi]; exact h.fields.bound i hi
  · intro i hi; rw [←he i hi]; exact h.fields.stored i hi
  · intro i hi; rw [←he i hi]; exact h.fields.count i hi

theorem countFlag_congr {L K : Nat→List Zq} (he : ∀i<4,L i=K i) : countFlag L=countFlag K := by
  unfold countFlag foldedFlags
  change ((BitVec.ofNat 64 (256-(L 0).length)|||BitVec.ofNat 64 (256-(L 1).length))|||
    BitVec.ofNat 64 (256-(L 2).length))|||BitVec.ofNat 64 (256-(L 3).length)=_
  rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]
  rfl

def secondBatch (sha3 : Bool) (η : Nat) : Prog isa :=
 .ite (.zero .x .x27) (.block [])
  (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 272)
   (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η 272)
    (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags)))

theorem secondBatch_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ s : State}
    (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State} {L : Nat→List Zq}
    (hs : SamplerRun σ s A L) (hflag : s.gpr .x27=countFlag L) :
    WP isa (secondBatch sha3 η) s fun t=>
      ∃A',SamplerRun σ t A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        t.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) := by
  unfold secondBatch
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _=>?_) (by simp)
    have hfull := (countFlag_zero hs.fields.bound).mp (hflag.symm.trans hz)
    have he : ∀i<4,L i=rbFold η (L i) (chunkBytes (A i)) := fun i hi=>
      (rbFold_full (hfull i hi) _).symm
    exact WP.block_nil_iff.mpr ⟨A,hs.congr he,hflag.trans (countFlag_congr he)⟩
  · refine WP.ite false (by rw [eval_zero,show (s.gpr .x27 == 0)=false from beq_eq_false_iff_ne.mpr hz])
      (by simp) (fun _=>?_)
    have hc:=WP.seq (WP.mono (sampleRound_ok sha3 hη hp hs (by decide : 272≤272)) fun t ht=>
      WP.mono (flagsStage_ok hp ht) fun u ⟨hu,hf⟩=>
        (show ∃A',SamplerRun σ u A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
          u.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i))) from ⟨_,hu,hf⟩))
    simpa only [WP.seq_iff (M := isa)] using hc

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourFinish.lean`, which only this module imported.
section

/-! ## From `BoundedFourMasked.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def resultWord (L : List Zq) (j : Nat) : BitVec 32 := if L.length=256 then zw (L.getD j 0) else 0#32

structure Sampled (σ s : State) (L : Nat→List Zq) : Prop where
 env : SamplerEnv σ s
 bound : ∀i<4,(L i).length≤256
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 flag : s.gpr .x27=countFlag L

theorem maskStage_ok {σ s : State} (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State}
    {L : Nat→List Zq} (hs : SamplerRun σ s A L) (hf : s.gpr .x27=countFlag L) :
    WP isa maskFour s (fun t=>Sampled σ t L) := by
  have hout (i j : Nat) (hi : i<4) (hj : j<64) :
      InRegions s.wr (outputAt (samplerOut σ) i+BitVec.ofNat 64 (16*j)) 16 := by
    rw [hs.env.wr,hp.wr]
    refine ⟨samplerOutput σ,by simp,?_⟩
    unfold outputAt
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (maskFour_ok hs.env.x19 hs.env.x21
    (fun i hi=>by rw [hs.fields.count i hi,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega)
    (fun i hi=>sampler_work_read hp hs.env.wr (by omega))
    (fun i hi j hj=>by obtain ⟨r,hr,hc⟩:=hout i j hi hj; exact ⟨r,List.mem_append_right _ hr,hc⟩)
    (fun i hi j hj=>hout i j hi hj)
    (fun i hi j hj=>(hp.output_work.symm.sub_left
      (Offset.sub_base _ (d := 7904+8*i) (n := 8) (k := 8192) (by omega))).sub_right (outputAt_sub _ hj)))
    fun t ht=>?_
  refine ⟨?_,hs.fields.bound,?_,(ht.keep.get .x27).trans hf⟩
  · exact hs.env.frameStep ht.frame (fun r hr=>by
      rw [List.mem_singleton.mp hr]
      exact ⟨ResidentRej.aR 4 σ,by simp,fun _ h=>h⟩)
      (fun r hr=>by rw [List.mem_singleton.mp hr]; exact
        (hp.output_work.sub_right (Offset.sub_base _ (d := 7968) (n := 144) (k := 8192) (by decide))).symm)
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · intro i hi j hj
    rw [ht.words i hi j hj,ite_eq_left hi]
    unfold maskedWord resultWord
    rw [hs.fields.count i hi]
    by_cases hfull : (L i).length=256
    · rw [hfull,ite_eq_left rfl,ite_eq_left rfl]
      exact hs.fields.stored i hi j (by omega)
    · have hn : BitVec.ofNat 64 (256-(L i).length)≠0#64 := by
        intro he
        have hh:=congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hh
        change 256-(L i).length=0 at hh
        have:=hs.fields.bound i hi
        omega
      rw [ite_eq_right hn,ite_eq_right hfull]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64

local instance (L : Nat→List Zq) : Decidable (∀i<4,(L i).length=256) :=
 Nat.decidableBallLT 4 (fun i _=>(L i).length=256)

structure Result (σ t : State) (L : Nat→List Zq) : Prop where
 abi : abiPreserved σ t
 frame : Frame [samplerOutput σ,samplerWorkspace σ] σ.mem t.mem
 rd : t.rd=σ.rd
 wr : t.wr=σ.wr
 words : ∀i<4,∀j<256,coeffAt t.mem (outputAt (samplerOut σ) i) j=resultWord (L i) j
 status : t.gpr .x0=if (∀i<4,(L i).length=256) then 1#64 else 0#64

theorem finish_ok {σ s : State} (hp : SamplerPre σ) {L : Nat→List Zq} (h : Sampled σ s L) :
    WP isa (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
      Impl.MlDsa.AArch64.Sample.Rej4.epi)) s (fun t=>Result σ t L) := by
  refine wp_subImm (by decide) fun a ha ea=>wp_lsr (by decide) fun b hb eb=>?_
  have he : SamplerEnv σ b := h.env.lowStep (rs := [])
    (by rw [hb.mem,ha.mem]; exact Frame.refl _ _) (by simp)
    (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.sp.trans ha.sp)
    (fun r hr=>by
      have hn : r∉[Reg.x27] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      rw [hb.get r hn,ha.get r hn])
  have hbound : (countFlag L).toNat<512 := ResidentRej.foldedFlags_bound _ _ (fun i hi=>by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega)
  have eflag : b.gpr .x27=if (∀i<4,(L i).length=256) then 1#64 else 0#64 := by
    rw [eb,ea,h.flag,ResidentRej.smallFlag_status _ hbound]
    by_cases hz : countFlag L=0#64
    · rw [ite_eq_left hz,ite_eq_left ((countFlag_zero h.bound).mp hz)]
    · rw [ite_eq_right hz,ite_eq_right (fun hh=>hz ((countFlag_zero h.bound).mpr hh))]
  refine WP.mono (ResidentRej.epi_with he (fun d n hn=>sampler_work_read hp he.wr hn)) fun t ht=>?_
  exact ⟨ht.1,by rw [ht.2.1]; exact he.frame,ht.2.2.2.1.trans he.rd,
    ht.2.2.2.2.trans he.wr,by simpa only [ht.2.1,hb.mem,ha.mem] using h.words,
    ht.2.2.1.trans eflag⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def sampledRows (σ : State) (η : Nat) (i : Nat) : List Zq :=
 rbFold η (rbFold η [] (chunkBytes (samplerA σ i)))
  (chunkBytes (Resident.permuted (samplerA σ i) 2))

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State→Prop} :
    WP isa (.seq a (.seq b c)) s Q↔WP isa (.seq (.seq a b) c) s Q := by
  simp only [WP.seq_iff (M := isa)]

theorem sampler_machine_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ : State}
    (hp : SamplerPre σ) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) σ
      (fun t=>Result σ t (sampledRows σ η)) := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change WP isa (.seq (.block samplerSetup) _) σ _
  refine WP.seq (WP.mono (samplerSetup_ok hp) fun a ha=>?_)
  rw [wp_seq_assoc]
  refine WP.seq (WP.mono (sampleRound_ok sha3 hη hp ha.running (by decide : 0≤272)) fun b hb=>?_)
  refine WP.seq (WP.mono (flagsStage_ok hp hb) fun c ⟨hc,hflag⟩=>?_)
  change WP isa (.seq (secondBatch sha3 η) _) c _
  refine WP.seq (WP.mono (secondBatch_ok sha3 hη hp hc hflag) fun d ⟨A,hd,hdf⟩=>?_)
  change WP isa (.seq maskFour _) d _
  refine WP.seq (WP.mono (maskStage_ok hp hd hdf) fun e he=>?_)
  exact finish_ok hp he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourShake.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

theorem permuted_add (A : Spec.Sha3.State) (i j : Nat) :
    Resident.permuted (Resident.permuted A i) j=Resident.permuted A (i+j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Resident.permuted,ih]; rfl

theorem chunks_squeeze (A : Spec.Sha3.State) :
    chunkBytes A++chunkBytes (Resident.permuted A 2)=
      Spec.Sha3.squeezeBlocks 136 (Spec.Sha3.keccakF A) 4 := by
  apply List.ext_getElem
  · rw [List.length_append,chunkBytes_length,chunkBytes_length,
      VG.Proof.Sha3.length_squeezeBlocks (by decide)]
  · intro j hj hj'
    have hj544 : j<544:=by simpa only [List.length_append,chunkBytes_length] using hj
    rw [VG.Proof.Sha3.getElem_squeezeBlocks (by decide) (by decide),
      VG.Proof.Sha3.iterF_keccakF,←Resident.permuted_eq_iterF]
    by_cases h : j<272
    · rw [List.getElem_append_left (by simpa only [chunkBytes_length] using h)]
      simpa only [getElem!_pos (chunkBytes A) j (by rw [chunkBytes_length]; exact h)] using chunkBytes_get A h
    · rw [List.getElem_append_right (by simpa only [chunkBytes_length] using (by omega : 272≤j))]
      simp only [chunkBytes_length]
      rw [←getElem!_pos (chunkBytes (Resident.permuted A 2)) (j-272) (by rw [chunkBytes_length]; omega),
        chunkBytes_get _ (by omega),permuted_add]
      have hd : 2+((j-272)/136+1)=j/136+1:=by omega
      have hm : (j-272)%136=j%136:=by omega
      rw [hd,hm]

theorem chunks_H (m : Mem) (p : Addr) :
    chunkBytes (ResidentMask.seedState m p)++
      chunkBytes (Resident.permuted (ResidentMask.seedState m p) 2)=
      Spec.MlDsa.H (Spec.Sha3.bytesAt m p 66) 544 := by
  rw [chunks_squeeze,ResidentMask.seedState_eq]
  change _=Spec.Sha3.squeeze 136
    (VG.Proof.MlKem.padded 136 Spec.Sha3.shakeSuffix (Spec.Sha3.bytesAt m p 66)) 544
  rw [ResidentSeed66.padded_A0 (VG.Proof.Sha3.bytesAt_length _ _ _),Spec.Sha3.squeeze]
  change _=(Spec.Sha3.squeezeBlocks 136
    (Spec.Sha3.keccakF (ResidentSeed66.A0 (Spec.Sha3.bytesAt m p 66))) 4).take 544
  rw [List.take_of_length_le (by rw [VG.Proof.Sha3.length_squeezeBlocks (by decide)])]

theorem sampledRows_H (σ : State) (η i : Nat) :
    sampledRows σ η i=rbFold η []
      (Spec.MlDsa.H (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) 544) := by
  unfold sampledRows samplerA
  rw [←rbFold_append,chunks_H]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
