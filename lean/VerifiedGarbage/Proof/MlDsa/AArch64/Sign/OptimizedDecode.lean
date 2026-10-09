import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

/-- The matrix remains canonical while secret transforms retain their
positive representatives, ready for the fused multiply/inverse kernels. -/
structure PositiveID (p : Params) (S : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : IM p S σ s
  roots : StaticRoots S s
  s1 : PosFam s (s1Base p) a (S1v p σ)
  s2 : PosFam s (s2Base p) b (S2v p σ)
  t0 : PosFam s (t0Base p) c (T0v p σ)

theorem PositiveID.step {p : Params} {S : Nat} {σ s t : State} {a b c : Nat}
    (h : PositiveID p S σ a b c s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s t ws) (hy : t.syms=s.syms) (hc : idChk p ws a b c=true)
    (hw : ∀ w∈ws,inB (sgW p) w.1 w.2=true) : PositiveID p S σ a b c t := by
  simp only [idChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hi,h1⟩,h2⟩,h0⟩ := hc
  exact ⟨h.im.step hP hi,h.roots.step_layout h.im.st.lay hP hy hw,
    h.s1.keep h.im.st.lay hP h1,h.s2.keep h.im.st.lay hP h2,h.t0.keep h.im.st.lay hP h0⟩

theorem positiveDecode_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    {σ s : State} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x,y)∈bitPackParams) (hl : len=32*bitlen (x+y))
    (hc : decChk p a b c src len j=true) (h : PositiveID p S σ a b c s) :
    WP isa (positiveDecode P src len x y j) s fun t => PositiveID p S σ a b c t ∧
      PosPl t j (ntt (toRq (bitUnpack (bytesAt s.mem (pa s src) len) x y))) := by
  simp only [decChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hu,hn⟩,hk⟩,_⟩ := hc
  have hn' := hn
  simp only [ipChkS,ipChk,Bool.and_eq_true] at hn'
  obtain ⟨⟨⟨⟨_,hin⟩,_⟩,hw⟩,_⟩ := hn'
  have hws : ∀ w∈[(pS j,1024)],inB (sgW p) w.1 w.2=true := by simpa using hw
  refine WP.seq (WP.mono_syms (bupAt_ok hP h.im.st.lay hp hl hu)
    fun s1 ⟨hP1,_,hq1⟩ hy1 => ?_)
  have I1 := h.step hP1 hy1 hk hws
  have ht : ForwardRoots s1 (pa s1 (pS j)) :=
    ⟨I1.roots.nttTableAt (I1.im.st.lay.inW hw),I1.roots.forward.readable⟩
  have hr : Reduced s1.mem (pa s1 (pS j)) := by
    rw [hP1.pa (pS_bases j)]; exact hq1.1
  refine WP.mono_syms (positiveNttAt_layout I1.im.st.lay hin hw ht hr)
    fun s2 ⟨hP2,_,hq2⟩ hy2 => ⟨I1.step hP2 hy2 hk hws,?_⟩
  change PosPolyIs s2.mem (pa s2 (pS j)) _
  rw [hP2.pa (pS_bases j)]
  rw [hP1.pa (pS_bases j),hq1.2] at hq2
  rw [hP1.pa (pS_bases j)]
  exact hq2

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
  (hc : dChk p=true) {σ s : State}
include hP hc

theorem positiveDecodeS1_ok {r : Nat} (hr : r<p.ℓ) (hs : PositiveID p S σ r 0 0 s) :
    WP isa (positiveDecode P (.x25,skS1 p r) (sLen p) p.η p.η (s1Base p+r)) s
      (PositiveID p S σ (r+1) 0 0) := by
  obtain ⟨c,ck⟩ := (dChk_spec hc).1 r hr
  refine WP.mono (positiveDecode_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs)
    fun t ⟨I,hq⟩ => ⟨I.im,I.roots,I.s1.snoc ?_,I.s2,I.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem positiveDecodeS2_ok {i : Nat} (hi : i<p.k) (hs : PositiveID p S σ p.ℓ i 0 s) :
    WP isa (positiveDecode P (.x25,skS2 p i) (sLen p) p.η p.η (s2Base p+i)) s
      (PositiveID p S σ p.ℓ (i+1) 0) := by
  obtain ⟨c,ck⟩ := (dChk_spec hc).2.1 i hi
  refine WP.mono (positiveDecode_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs)
    fun t ⟨I,hq⟩ => ⟨I.im,I.roots,I.s1,I.s2.snoc ?_,I.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem positiveDecodeT0_ok {i : Nat} (hi : i<p.k) (hs : PositiveID p S σ p.ℓ p.k i s) :
    WP isa (positiveDecode P (.x25,skT0 p i) 416 4095 4096 (t0Base p+i)) s
      (PositiveID p S σ p.ℓ p.k (i+1)) := by
  obtain ⟨c,ck⟩ := (dChk_spec hc).2.2.1 i hi
  refine WP.mono (positiveDecode_ok hP (by decide) (by decide) c hs)
    fun t ⟨I,hq⟩ => ⟨I.im,I.roots,I.s1,I.s2,I.t0.snoc ?_⟩
  have e : skT0 p i = 128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * p.k + 32 * 13 * i := by
    unfold skT0 VG.Proof.MlDsa.Sign.lenS sLen; rw [Nat.mul_add]; omega
  rw [sk_slice hs.im.st ck,e] at hq
  exact hq


theorem positiveDecodeSecrets_ok (hs : PositiveID p S σ 0 0 0 s) :
    WP isa (.seq
      (VG.Impl.MlDsa.AArch64.Call.seqR (fun r => positiveDecode P (.x25,skS1 p r)
        (sLen p) p.η p.η (s1Base p+r)) 0 p.ℓ)
      (.seq (VG.Impl.MlDsa.AArch64.Call.seqR (fun i => positiveDecode P (.x25,skS2 p i)
        (sLen p) p.η p.η (s2Base p+i)) 0 p.k)
        (VG.Impl.MlDsa.AArch64.Call.seqR (fun i => positiveDecode P (.x25,skT0 p i)
          416 4095 4096 (t0Base p+i)) 0 p.k))) s (PositiveID p S σ p.ℓ p.k p.k) := by
  refine WP.seq (WP.mono (seqR_ok (I := fun r s => PositiveID p S σ r 0 0 s) p.ℓ 0
    (fun r _ hr s h => positiveDecodeS1_ok hP hc (by omega) h) s hs) fun s1 h1 => ?_)
  simp only [Nat.zero_add] at h1
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => PositiveID p S σ p.ℓ i 0 s) p.k 0
    (fun i _ hi s h => positiveDecodeS2_ok hP hc (by omega) h) s1 h1) fun s2 h2 => ?_)
  simp only [Nat.zero_add] at h2
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s => PositiveID p S σ p.ℓ p.k i s) p.k 0 (fun i _ hi s h => positiveDecodeT0_ok hP hc (by omega) h) s2 h2

end

end VG.Proof.MlDsa.AArch64.Sign
