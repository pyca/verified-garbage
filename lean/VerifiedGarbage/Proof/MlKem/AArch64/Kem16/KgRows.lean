module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgOps
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTables
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block

/-! # The 16-bit key generation is correct

As `Optimized/KeyGen*.lean` and `FixedHash/KeyGenUsing.lean`, for
`Kem16.keyGen`: the noise with 16 bits, the encodings of `ŝ` (`encode_okW`),
the rows of `t̂` (`rows_okW`: the fused dot product, the sum with `ê` and the
encodings, all with 16 bits), the end, and the whole (`using_correctW`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
open VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay}


def rowFW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.1)
def rowGW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.2)

theorem row_sumW {s₀ s : State} {mB : Mem} {v : BitVec 64} {i : Nat}
    (hi : i < P.k) (h : TLW P s₀ mB v i s) :
    Dot.polySum (rowTerms P i) (rowFW s₀ s) (rowGW s₀ s) =
      KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj
    exact (h.c.ahat (P.k*i+j) (ij_lt hi hj)).2
  · intro j hj
    exact (h.sp j hj).2

theorem row_readyW {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat}
    (hi : i < P.k) (h : TLW P s₀ mB v i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (rowFW s₀ s) (rowGW s₀ s) := by
  have hw := hp.wf
  have term : ∀ fg ∈ rowTerms P i, ∃ j<P.k, fg=(aOff P i j,sOff P j) := by
    intro fg hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ha,hc,ht⟩
  · simp only [rowTerms,List.length_map,List.length_range]; exact hw.facts.2.1
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change aOff P i j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change sOff P j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.c.ahat (P.k*i+j) (ij_lt hi hj)).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.sp j hj).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · rw [h.c.kb.x28]
    exact cov_w hp h.c.kb (b := 3) (by decide) (by kl)



theorem fused_rowW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : TLW P s₀ mB v i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (rowTerms P i) F G = KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k)
    (he : PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P i)) (KPke.kgE P.params (dB s₀) i)) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v (i+1) t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  have hw := hp.wf
  have eg := Noise.noise_fits hr hi
  have ep := Noise.noise_past_kg hr i
  change WP isa (seqs [_,_,_,_]) s _
  refine WP.seq (WP.mono (fusedW_tl hp hi h (rowTerms P i) hd) fun s₂ ⟨tl₂,f₂,t₂⟩ => ?_)
  rw [hsum] at t₂
  have e₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)) he
  refine WP.seq (WP.mono (addW_read_okK hp (f := TP P) (g := noiseOff P i) (po_TP hw) eg
    (.inl (by lom)) tl₂.c.kb t₂.1 e₂.1) fun s₇ ⟨kb₇,f₇,t₇,x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (apart_TP hp hi)
  rw [t₂.2,e₂.2] at t₇
  have tv : PolyIsW 16 s₇.mem (kA s₀ 3+BitVec.ofNat 64 (TP P)) (tVW P s₀ mB i) := t₇
  refine WP.seq (WP.mono (enc12W_okK hp (off := TP P) (b := 1) (o := 384*i) (po_TP hw) (.inl rfl)
    (by kl) kb₇ tv) fun s₈ ⟨kb₈,f₈,b₈,x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_ek hp hi
  have tv₈ : PolyIsW 16 s₈.mem _ _ := polyIsW_frame_poly (w16 := true) f₈ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WP.mono (enc12W_okK hp (off := TP P) (b := 2) (o := 384*P.k+384*i) (po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈) fun s₉ ⟨kb₉,f₉,b₉,x₉⟩ => ?_
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_dk hp hi
  refine ⟨⟨tl₉.c,tl₉.sp,tl₉.dk,fun i' hi' => ?_⟩,?_⟩
  · rcases (by omega : i'<i ∨ i'=i) with hi' | rfl
    · exact tl₉.ek i' hi'
    · refine ⟨?_,b₉⟩
      rw [bytesAt_frame f₉ (fun r hr' => by
        rw [List.mem_singleton.mp hr']
        exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide),b₈]
  · exact (((f₂.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites])).trans
      (f₇.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₈.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₉.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))

def ErrorsK (P : KemLay) (s₀ s : State) : Prop :=
  ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P j)) (KPke.kgE P.params (dB s₀) j)

theorem errors_rowW {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {i : Nat} (hi : i < P.k) (he : ErrorsK P s₀ s)
    (hf : Frame (rowWrites P s₀ i) s.mem t.mem) : ErrorsK P s₀ t := by
  have hw := hp.wf
  intro j hj
  have eg := Noise.noise_fits hr hj
  have ep := Noise.noise_past_kg hr j
  apply polyIsW_frame_poly (w16 := true) hf _ (he j hj)
  intro r hm
  simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))
  · exact hp.args.rdisj (by decide) (by decide) eg (by kl) (.inl (by decide))

theorem fused_row_readyW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : TLW P s₀ mB v i s)
    (he : ErrorsK P s₀ s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v (i+1) t ∧ ErrorsK P s₀ t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  exact WP.mono (fused_rowW hp hr hi h (row_readyW hp hi h ht hc ha).data (row_sumW hi h) (he i hi))
    fun t ⟨h',hf⟩ => ⟨h',errors_rowW hp hr hi he hf,hf⟩


def RowsInvW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop :=
  TLW P s₀ mB v i s ∧ ErrorsK P s₀ s ∧ RowTable P s₀ s

theorem rows_stepW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : RowsInvW P s₀ mB v i s) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s (RowsInvW P s₀ mB v (i+1)) := by
  have ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint
      ⟨s.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [h.1.c.kb.x28]
    exact (h.2.2.apart i hi _ (by simp [rowWrites])).symm
  refine WP.mono_syms (fused_row_readyW hp hr hi h.1 h.2.1 h.2.2.table h.2.2.read ha) ?_
  intro t ht hs
  exact ⟨ht.1,ht.2.1,h.2.2.frame hi hs h.1.c.kb ht.1.c.kb ht.2.2⟩

theorem rows_okW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : RowsInvW P s₀ mB v 0 s) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Kem16.kgRow P)) s (RowsInvW P s₀ mB v P.k) :=
  WPs.range (fun _ hi _ h => rows_stepW hp hr hi h) h



structure EncodeInvW (P : KemLay) (s₀ : State) (mB mN : Mem) (v : BitVec 64) (j : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : ErrorsK P s₀ s
  dk : ∀ j' < j, Spec.Sha3.bytesAt s.mem (kA s₀ 2+BitVec.ofNat 64 (384*j')) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j')
  frame : Frame [R (kA s₀) 2 0 (384*j)] mN s.mem

theorem encode_stepW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} {j : Nat} (hj : j < P.k) (h : EncodeInvW P s₀ mB mN v j s) :
    WP isa (Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v (j+1)) := by
  have hw := hp.wf
  have fd : 384*j+384 ≤ kL P 2 := by kl
  refine WP.mono (enc12W_okK hp (off := sOff P j) (b := 2) (o := 384*j)
    (po_s hw hj) (.inr rfl) fd h.c.kb (h.sp j hj)) fun t ⟨kt,ft,bt,xt⟩ => ?_
  refine ⟨h.c.frame kt xt ft (one_far hp (by decide) fd (.inl (by decide))),?_,?_,?_,?_⟩
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inl (by decide))) (h.sp i hi)
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (Noise.noise_fits hr hi) fd (.inl (by decide))) (h.errors i hi)
  · intro i hi
    rcases (by omega : i<j ∨ i=j) with hi | rfl
    · rw [bytesAt_frame ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inr (.inl (by omega)))) (by decide)]
      exact h.dk i hi
    · exact bt
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩))

theorem encode_okW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} (h : EncodeInvW P s₀ mB mN v 0 s) :
    WPs ((List.range P.k).map fun j => Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v P.k) :=
  WPs.range (fun _ hj _ h => encode_stepW hp hr hj h) h

theorem EncodeInvW.tl {s₀ s : State} {mB mN : Mem} {v : BitVec 64}
    (h : EncodeInvW P s₀ mB mN v P.k s) : TLW P s₀ mB v 0 s :=
  ⟨h.c,h.sp,h.dk,fun _ hi => by omega⟩



theorem noise_cinvW {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : CInvW P s₀ mB v s)
    (ht : Kept (Noise.allWrites P true (kA s₀ 3)) s t) : CInvW P s₀ mB v t := by
  have hw := hp.wf
  have hroom := hr.kg
  refine h.frame (noise_kb hp hr h.kb ht) (ht.cs .x24 (by decide) (by decide)) ht.frame ?_
  intro r hh
  exact ⟨noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh,
    noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh,
    noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh⟩

theorem readonly_noise_encodeW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (ht : Optimized.TransformTables s)
    {mB : Mem} {v : BitVec 64} (h : CInvW P s₀ mB v s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWithW P true) s fun t =>
      Kept (Noise.allWrites P true (kA s₀ 3)) s t ∧ EncodeInvW P s₀ mB t.mem v 0 t := by
  have hc : Covers [⟨kA s₀ 3,P.scl⟩] s.wr := by
    have hh := cov_w hp h.kb (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (Noise.readonly_noiseAll_tables hp.wf hr true h.kb.x28 hc ht) fun t ⟨kt,pt⟩ => ?_
  refine ⟨kt,noise_cinvW hp hr h kt,?_,?_,fun _ hj => by omega,Frame.refl _ _⟩
  · intro j hj
    have p : PolyIsW 16 _ _ _ := pt j (by omega)
    simpa only [Noise.outOff,ite_eq_left hj,ite_true,Noise.sampled,Noise.seedOff,Noise.transformed,
      Bool.true_or,h.sig,KPke.kgS,cbd] using p
  · intro j hj
    have p : PolyIsW 16 _ _ _ := pt (P.k+j) (by omega)
    have hn : ¬P.k+j<P.k := by omega
    simpa only [Noise.outOff,ite_eq_right hn,Nat.add_sub_cancel_left,Noise.sampled,Noise.seedOff,
      Noise.transformed,Bool.true_or,ite_true,h.sig,KPke.kgE,cbd,KemLay.params] using p


theorem finish_using_okW (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : EncodeInvW P s₀ mB s.mem v 0 s)
    (ht : RowTable P s₀ s)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (seqs (((List.range P.k).map fun j => Kem16.enc12WAt (sOff P j) .x27 (384*j)) ++
      ((List.range P.k).map (Impl.MlKem.AArch64.Kem16.kgRow P)) ++ [FixedHashCallers.kgEndUsing hash P]))
      s (DoneW P s₀ mB v) := by
  apply WPs.seqs (by simp)
  rw [List.append_assoc]
  apply WPs.append
  have he := WPs.seqs (map_range_ne_nil hp.wf.facts.1 _) (encode_okW hp hr h)
  have he' := WP.mono_syms he (fun t he hs =>
    show EncodeInvW P s₀ mB s.mem v P.k t ∧ RowTable P s₀ t from
      ⟨he,ht.encode_frame hs h.c.kb he.c.kb he.frame ha⟩)
  -- The encode loop's abstract list carries symbol preservation as well.
  have hseq : WPs ((List.range P.k).map fun j => Kem16.enc12WAt (sOff P j) .x27 (384*j)) s
      (fun t => EncodeInvW P s₀ mB s.mem v P.k t ∧ RowTable P s₀ t) := by
    have hkeep : ∀ cs s Q, WP isa (seqs cs) s Q → cs≠[] → WPs cs s Q := by
      intro cs
      induction cs with
      | nil => intro s Q _ hn; exact False.elim (hn rfl)
      | cons c cs ih =>
        intro s Q hw hn
        cases cs with
        | nil => exact WP.mono hw (fun _ h => h)
        | cons d ds =>
          exact WP.mono (WP.seq_iff.mp hw) fun _ h => ih _ _ h (List.cons_ne_nil _ _)
    exact hkeep _ _ _ he' (map_range_ne_nil hp.wf.facts.1 _)
  exact WPs.mono hseq fun t ⟨he,ht'⟩ => WPs.append
    (WPs.mono (rows_okW hp hr ⟨he.tl,he.errors,ht'⟩) fun u hu => WPs.single (end_using_okW hash hH hp hu.1))

theorem rest_using_okW (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    (htr : Optimized.TransformTables s)
    (h : BInvW true P s₀ (P.k*P.k) s) (ht : RowTable P s₀ s)
    (hd : ∀r∈Noise.allWrites P true (kA s₀ 3), (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (Kem16.kgRest hash P) s (DoneW P s₀ s.mem (s.gpr .x24)) := by
  have c : CInvW P s₀ s.mem (s.gpr .x24) s := ⟨h.kb,h.rho,h.sig,rfl,fun e he => ⟨h.red e he,rfl⟩⟩
  refine WP.seq (WP.mono_syms (readonly_noise_encodeW hp hr htr c) fun t ⟨kt,et⟩ hs => ?_)
  have tt : RowTable P s₀ t := by
    refine ⟨?_,?_,?_⟩
    · rw [hs]
      intro j hj
      rw [←ht.table j hj]
      exact kt.frame.readW (r := ⟨s.syms "VG_MLKEM_GAMMA",512⟩)
        (contains_off (by omega) (by decide)) hd (by decide)
    · simpa only [hs,kt.rd,kt.wr] using ht.read
    · simpa only [hs] using ht.apart
  exact finish_using_okW hash hH hp hr et tt (by simpa only [hs] using ha)

theorem using_correctW (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩]) {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) (tables : Tables s₀)
    (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Paired.matrix P true true).aarch64Depth≤1) :
    WP isa (Kem16.keyGen hash P) s₀ fun t=>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  refine WP.seq (WP.mono (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA,ta⟩=>?_)
  have scratchA : Covers [⟨kA s₀ 3,P.scl⟩] sA.wr := by
    simpa only [R,ptr_zero] using (cov_w hp hA.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl))
  have mt : MatrixTable P s₀ sA :=
    ⟨ta.shuffle,ta.shuffleRead,apart_of_covers ta.shuffleApart scratchA⟩
  refine WP.seq (WP.mono (WP.tablesDepth (paired_matrix_ok hp (binvW_zero (w16 := true) hA) mt) ta depthB)
    fun sB ⟨⟨hB,_⟩,tb⟩=>?_)
  have hw := hp.wf
  refine WP.mono (rest_using_okW hash hH hp hr tb.transforms hB
    (readonly_rows hp hB.kb tb.gamma tb.gammaRead tb.gammaApart)
    (readonly_noise hp hr hB.kb tb.gammaApart)
    (apart_of_covers tb.gammaApart (cov_w hp hB.kb (b:=2) (o:=0) (l:=384*P.k) (by decide) (by kl))))
    fun t ht=>⟨ht.abi,post_ofW hB ht⟩

end VG.Proof.MlKem.AArch64.KeyGen
