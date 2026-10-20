module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTables

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets

/-! # Readonly artifact tables are separate from every writable operand -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

theorem apart_of_covers {r q : Region} {wr : List Region}
    (h : ∀p∈wr,r.Disjoint p) (hc : Covers [q] wr) : r.Disjoint q := by
  intro a ha hb
  obtain ⟨p,hp,hb⟩ := hc a 1 ⟨q,by simp,hb⟩
  exact h p hp a ha hb

end VG.Proof.MlKem.AArch64.Optimized

namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG
variable {P : KemLay}

theorem readonly_rows {s₀ s : State} (hp : Pre P s₀) (h : KB P s₀ s)
    (ta : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (tr : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (td : ∀r∈s.wr,(Region.mk (s.syms "VG_MLKEM_GAMMA") 512).Disjoint r) : RowTable P s₀ s := by
  have hw := hp.wf
  refine ⟨ta,tr,?_⟩
  intro i hi r hr
  simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=3) (o:=TP P) (l:=1024) (by decide) (by kl))
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=1) (o:=384*i) (l:=384) (by decide) (by kl))
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=2) (o:=384*P.k+384*i) (l:=384) (by decide) (by kl))

theorem readonly_noise {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (h : KB P s₀ s)
    {r : Region} (td : ∀q∈s.wr,r.Disjoint q) :
    ∀q∈Noise.allWrites P true (kA s₀ 3),r.Disjoint q := by
  have hw := hp.wf
  apply Noise.allWrites_apart
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=3) (o:=SS) (l:=2048) (by decide) (by kl))
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=3) (o:=NS) (l:=1024) (by decide) (by kl))
  · intro j hj
    exact Optimized.apart_of_covers td (cov_w hp h (b:=3) (o:=Noise.outOff P true j) (l:=1024)
      (by decide) (Noise.outOff_fits hw hr true hj))

end VG.Proof.MlKem.AArch64.KeyGen

namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
variable {P : KemLay} {L : Layout}

theorem readonly_noise {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s)
    {r : Region} (td : ∀q∈s.wr,r.Disjoint q) :
    ∀q∈Noise.allWrites P false (kA s₀ L.sc),r.Disjoint q := by
  have hw := hp.wf
  apply Noise.allWrites_apart
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=SS) (l:=2048) (by lom))
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=NS) (l:=1024) (by lom))
  · intro j hj
    have fits : Noise.outOff P false j+1024≤L.len L.sc := by
      rw [hp.scl]; exact Noise.outOff_fits hw hr false hj
    exact Optimized.apart_of_covers td (cov_w hp h (b:=L.sc) (o:=Noise.outOff P false j) (l:=1024)
      ⟨hp.scw,hp.scb⟩ fits)

theorem readonly_enc {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s)
    {kE eo kC co : Nat} (ha : EncArgs P L kE eo kC co)
    {r : Region} (td : ∀q∈s.wr,r.Disjoint q) (ts : r.Disjoint (below s.sp 16)) :
    ∀q∈encW P L s₀ kC co,r.Disjoint q := by
  have hw := hp.wf
  intro q hq
  simp only [encW,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=0) (l:=840) (by lom))
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=RB+32) (l:=1) (by lom))
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=PB) (l:=SV P-PB) (by lom))
  · rwa [h.sp] at ts
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=L.slot kC) (o:=co) (l:=P.ctLen)
      ⟨ha.wC,hp.lt ha.hkC⟩ ha.fC)

end VG.Proof.MlKem.AArch64.Kem
