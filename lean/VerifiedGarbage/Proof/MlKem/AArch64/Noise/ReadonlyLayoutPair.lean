module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPairTail
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
/-! # Execute a pair using only the public scratch allocation -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyPair.lean`, which only this module imported.
section

/-! # Complete paired-noise operation -/
section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noisePair_ok {s : State} {L : KemLay} (kg : Bool) {n : Nat} {p a f g w : Addr}
    (hn : n+1<256)
    (h0 : outOff L kg n <65536) (h1 : outOff L kg (n+1)<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SS else KEM.SS)=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SG else KEM.RB)=a)
    (hf : s.gpr .x28+BitVec.ofNat 64 (outOff L kg n)=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 (outOff L kg (n+1))=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.NS else KEM.NS)=w)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk a 32).Disjoint (savedR p))
    (hap : (Region.mk a 32).Disjoint (pairR p))
    (hs : TailSetup s p f g w)
    (ht0 : NttR.FastReady s f w)
    (ht1 : NttR.FastReady s g w)
    (hfar : ∀r∈pairWrites p f g w,(NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites p f g w) s t ∧
      PolyIsW (cw true) t.mem f (sampled s.mem a n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem g (sampled s.mem a (n+1) (transformed L kg (n+1))) := by
  change WP isa (.seq (.block (Impl.MlKem.AArch64.Noise.noiseInit L kg n))
    (seqs [Impl.MlKem.AArch64.Noise.squeezePair,
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg n) (if kg then KG.NS else KEM.NS) 400 (transformed L kg n),
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg (n+1)) (if kg then KG.NS else KEM.NS) 528 (transformed L kg (n+1)),
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))])) s _
  refine WP.seq (WP.mono_syms (init_ok (by cases kg <;> decide) hn
    (by cases kg <;> decide) (by cases kg <;> decide) hp ha hin hwr hsv has hap
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,pair⟩ us => ?_)
  have pu : Partial (pairWrites p f g w) s u :=
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,ku.vcs,
      fu.mono (by simp [pairWrites])⟩
  have t0 := ht0.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  have t1 := ht1.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  exact readonly_pair_tail_ok (transformed L kg n) (transformed L kg (n+1)) hn h0 h1
    (by cases kg <;> decide) pu sv h19 h20 h21
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hg)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    (hs.regions ku.rd ku.wr) pair t0 t1 (by simpa only [NttR.fastRegion, NttR.sRegion, us] using hfar)

end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)
open VG.Proof.Sha3.AArch64.Neon


theorem readonly_noisePair_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} {n : Nat} (hn : n+1<2*L.k) (hB : s.gpr .x28=B)
    (hc : Covers [⟨B,L.scl⟩] s.wr)
    (ht0 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (nttOff kg)))
    (ht1 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg (n+1))) (B+BitVec.ofNat 64 (nttOff kg)))
    (hfar : ∀r∈pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
      (B+BitVec.ofNat 64 (nttOff kg)), (NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
        (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (B+BitVec.ofNat 64 (nttOff kg))) s t ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg n))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) (n+1) (transformed L kg (n+1))) := by
  have lim := layout_limits wf kg
  have fit0 := outOff_fits wf room kg (by omega : n<2*L.k)
  have fit1 := outOff_fits wf room kg hn
  have low0 := outOff_low wf room kg n
  have low1 := outOff_low wf room kg (n+1)
  change nttOff kg+1024≤outOff L kg n at low0
  change nttOff kg+1024≤outOff L kg (n+1) at low1
  have order := outOff_order wf room kg (Nat.lt_succ_self n)
  have size : L.scl<2^64 := by omega
  have iw {o l : Nat} (h : o+l≤L.scl) := inScratch hc h size
  have ir {o l : Nat} (h : o+l≤L.scl) : InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 o) l :=
    by obtain ⟨r,hr,hc⟩ := iw h; exact ⟨r,List.mem_append_right _ hr,hc⟩
  have cw {o l : Nat} (h : o+l≤L.scl) := coversScratch hc h
  have sep {o l d k : Nat} (h : o+l≤d ∨ d+k≤o) (ho : o+l≤L.scl) (hd : d+k≤L.scl) :=
    Offset.disjoint B h (by omega : o+l≤2^64) (by omega : d+k≤2^64)
  have snorm (k : Nat) : B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 k =
      B+BitVec.ofNat 64 (scratchOff kg+k) := by rw [BitVec.add_assoc,← BitVec.ofNat_add]
  refine readonly_noisePair_ok kg (by have := wf.facts; omega) (by omega) (by omega)
    (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]) (by rw [hB]) (by rw [hB]; rfl)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_ ht0 ht1 hfar
  · rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact ir (by omega)
  · change InRegions s.wr (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*j)) 16
    rw [snorm]; exact iw (by omega)
  · rw [snorm]; exact iw (by omega)
  · change (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [snorm]; exact sep (Or.inl (by omega)) (by omega) (by omega)
  · exact sep (Or.inl lim.2.1) (by omega) (by omega)
  · constructor
    · intro i hi
      change InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*i)) 16
      rw [snorm]; exact ir (by omega)
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega)
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega)
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg),400⟩,
        ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩] s.wr
      rw [snorm]; exact coversTwo (cw (by omega)) (cw (by omega))
    · intro i hi; rw [snorm]; exact ir (by omega)
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg n),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega)) (cw fit0))
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg (n+1)),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega)) (cw fit1))
    · exact coversTwo (cw fit0) (cw lim.2.2.1)
    · exact coversTwo (cw fit1) (cw lim.2.2.1)
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega)) (by omega) fit0
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega)) (by omega) fit1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl
      · exact sep (Or.inl (by omega)) (by omega) fit0
      · exact sep (Or.inl (by omega)) (by omega) lim.2.2.1
    · exact sep (Or.inl order) fit0 fit1
    · exact sep (Or.inr low0) fit0 lim.2.2.1
    · exact sep (Or.inr low1) fit1 lim.2.2.1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800) 48).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl | rfl
      · exact sep (Or.inl (by omega)) (by omega) fit0
      · exact sep (Or.inl (by omega)) (by omega) fit1
      · exact sep (Or.inl (by omega)) (by omega) lim.2.2.1

end VG.Proof.MlKem.AArch64.Noise
