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

/-! # The 16-bit key generation's steps

As `Optimized/KeyGen*.lean`, with 16 bits: the noise, the encodings of `ŝ`
(`encode_okW`), and a row of `t̂` (`row_readyW`, `fused_row_readyW`: the
fused dot product, the sum with `ê` and the encodings), which
`KgH/` composes into `Kem16P.keyGen`. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
open VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay}


def rowFW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.1)
def rowGW (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 fg.2)

/-- Entry `j` of row `i` is among the first `n`, once the first `i + 1` rows are. -/
theorem lt_row {i j n : Nat} (hn : P.k * (i + 1) ≤ n) (hj : j < P.k) : P.k * i + j < n := by
  rw [Nat.mul_succ] at hn; omega

theorem row_sumW {s₀ s : State} {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hn : P.k * (i + 1) ≤ n) (h : TLW P s₀ mB v n i s) :
    Dot.polySum (rowTerms P i) (rowFW s₀ s) (rowGW s₀ s) =
      KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj
    exact (h.c.ahat (P.k*i+j) (lt_row hn hj)).2
  · intro j hj
    exact (h.sp j hj).2

theorem row_readyW {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hi : i < P.k) (hn : P.k * (i + 1) ≤ n) (h : TLW P s₀ mB v n i s)
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
    exact ⟨(h.c.ahat (P.k*i+j) (lt_row hn hj)).1,rfl⟩
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
    {mB : Mem} {v : BitVec 64} {n i : Nat} (hi : i < P.k) (h : TLW P s₀ mB v n i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (rowTerms P i) F G = KPke.dotK (aMW P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k)
    (he : PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P i)) (KPke.kgE P.params (dB s₀) i)) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v n (i+1) t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
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
    {mB : Mem} {v : BitVec 64} {n i : Nat} (hi : i < P.k) (hn : P.k * (i + 1) ≤ n)
    (h : TLW P s₀ mB v n i s) (he : ErrorsK P s₀ s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P i) s fun t =>
      TLW P s₀ mB v n (i+1) t ∧ ErrorsK P s₀ t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  exact WP.mono (fused_rowW hp hr hi h (row_readyW hp hi hn h ht hc ha).data (row_sumW hn h) (he i hi))
    fun t ⟨h',hf⟩ => ⟨h',errors_rowW hp hr hi he hf,hf⟩


structure EncodeInvW (P : KemLay) (s₀ : State) (mB mN : Mem) (v : BitVec 64) (n j : Nat) (s : State) : Prop where
  c : CInvW P s₀ mB v n s
  sp : ∀ j < P.k, PolyIsW 16 s.mem (kA s₀ 3+BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : ErrorsK P s₀ s
  dk : ∀ j' < j, Spec.Sha3.bytesAt s.mem (kA s₀ 2+BitVec.ofNat 64 (384*j')) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j')
  frame : Frame [R (kA s₀) 2 0 (384*j)] mN s.mem

theorem encode_stepW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} {n j : Nat} (hj : j < P.k) (h : EncodeInvW P s₀ mB mN v n j s) :
    WP isa (Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v n (j+1)) := by
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
    {mB mN : Mem} {v : BitVec 64} {n : Nat} (h : EncodeInvW P s₀ mB mN v n 0 s) :
    WPs ((List.range P.k).map fun j => Kem16.enc12WAt (sOff P j) .x27 (384*j)) s (EncodeInvW P s₀ mB mN v n P.k) :=
  WPs.range (fun _ hj _ h => encode_stepW hp hr hj h) h

theorem EncodeInvW.tl {s₀ s : State} {mB mN : Mem} {v : BitVec 64} {n : Nat}
    (h : EncodeInvW P s₀ mB mN v n P.k s) : TLW P s₀ mB v n 0 s :=
  ⟨h.c,h.sp,h.dk,fun _ hi => by omega⟩



theorem noise_cinvW {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {n : Nat} (h : CInvW P s₀ mB v n s)
    (ht : Kept (Noise.allWrites P true (kA s₀ 3)) s t) : CInvW P s₀ mB v n t := by
  have hw := hp.wf
  have hroom := hr.kg
  refine h.frame (noise_kb hp hr h.kb ht) (ht.cs .x24 (by decide) (by decide)) ht.frame ?_
  intro r hh
  exact ⟨noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh,
    noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh,
    noise_far hp hr (by decide) (by kl) (.inr (by lom)) r hh⟩

theorem readonly_noise_encodeW {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (ht : Optimized.TransformTables s)
    {mB : Mem} {v : BitVec 64} {n : Nat} (h : CInvW P s₀ mB v n s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWithW P true) s fun t =>
      Kept (Noise.allWrites P true (kA s₀ 3)) s t ∧ EncodeInvW P s₀ mB t.mem v n 0 t := by
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


end VG.Proof.MlKem.AArch64.KeyGen
