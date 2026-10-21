module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

/-! # A main squeeze computing `PRF₂(r, N)` in the third state

`prfOut_ok`: the first 16 words of the third state to buffer `N`.
`slotPrf_ok`: `PRF₂(r, N)`'s padded block into the third state, the `x3` call,
both SHAKE128 states' 21 words to their stream buffers, and the first 128
bytes of the third state to buffer `N` (`Rate128`, which `Noise.output_prf`
takes to `PRF₂`'s output). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Proof.MlKem.AArch64.Hybrid (clobbered stepRegs step3Writes frame)
open VG.Spec.Sha3 (stateAt keccakF)

theorem rate21_frame {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate21 m p A) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (rateR21 p).Disjoint r) : Rate21 m' p A :=
  fun i hi => by
    show m'.readW (p + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [hf.readW (r := rateR21 p) (Offset.contains_base p (by omega) (by omega)) hd (by decide)]
    exact h i hi

/-- **The first 16 words of the third state at `st` to buffer `N`.** -/
theorem prfOut_ok (bt N : Nat) {s : State} {st Bf : Addr} {S : Spec.Sha3.State}
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt N < 65536)
    (h28 : s.gpr .x28 = st) (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N) = Bf)
    (hS : stateAt s.mem st = S) (hin : Covers [stR st] (s.rd ++ s.wr)) (hout : Covers [rateR Bf] s.wr)
    (hd : (stR st).Disjoint (rateR Bf)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfOut bt N)) s fun t =>
      Keep [.x2, .x9] s t ∧ Frame [rateR Bf] s.mem t.mem ∧ Rate128 t.mem Bf S := by
  unfold Impl.MlKem.AArch64.Kem16P.prfOut
  refine wp_ptrTo (by decide) hbo fun s₁ h₁ e₁ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) (fun k (t : State) =>
      Keep [.x2, .x9] s t ∧ t.gpr .x2 = Bf ∧ Frame [rateR Bf] s.mem t.mem ∧
        ∀ j < k, t.mem.readW (outAddr Bf j) 64 = S[j]!)
    (fun k t hk ⟨kt, xt, ft, wt⟩ => ?_) 16 (Nat.le_refl _) s₁
    ⟨h₁.keep.mono (by simp), by rw [e₁, h28, hB], by rw [h₁.mem]; exact Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun t ⟨kt, _, ft, wt⟩ => ⟨kt, ft, wt⟩
  have hc : (stR st).Contains (st + BitVec.ofNat 64 (Impl.MlKem.AArch64.KEM.ST + 8 * k)) 8 :=
    Offset.contains_base st (by simp only [Impl.MlKem.AArch64.KEM.ST]; omega) (by simp only [Impl.MlKem.AArch64.KEM.ST]; omega)
  have hbc : (rateR Bf).Contains (outAddr Bf k) 8 := Offset.contains_base Bf (by omega) (by omega)
  refine wp_ldrx (a := st + BitVec.ofNat 64 (Impl.MlKem.AArch64.KEM.ST + 8 * k))
    ⟨by simp only [Impl.MlKem.AArch64.KEM.ST]; omega, by simp only [Impl.MlKem.AArch64.KEM.ST]; omega⟩
    (by rw [kt.get .x28 (by decide), h28])
    (by rw [kt.rd, kt.wr]; exact hin _ _ ⟨_, List.mem_singleton_self _, hc⟩) fun u hu e => ?_
  refine wp_strx (a := outAddr Bf k) ⟨by omega, by omega⟩ (by rw [hu.get .x2 (by decide), xt]; rfl)
    (by rw [hu.wr, kt.wr]; exact hout _ _ ⟨_, List.mem_singleton_self _, hbc⟩) fun v hv => wp_nil ?_
  have hm : v.mem = u.mem.writeW (outAddr Bf k) (u.gpr .x9) := hv.mem
  have hv9 : u.gpr .x9 = S[k]! := by
    rw [e, ft.readW hc (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide), ← hS]
    simp only [stateAt, Impl.MlKem.AArch64.KEM.ST, Nat.zero_add]
    rw [getElem!_pos _ k (by omega), Vector.getElem_ofFn]
  refine ⟨(kt.trans (hu.keep.trans hv.keep)).mono (by simp), by rw [hv.gpr, hu.get .x2 (by decide), xt], ?_,
    fun j hj => ?_⟩
  · rw [hm, hu.mem]; exact ft.writeW (List.mem_singleton_self _) _ hbc
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show outAddr Bf j = Bf + BitVec.ofNat 64 (8 * j) from rfl,
        show outAddr Bf k = Bf + BitVec.ofNat 64 (8 * k) from rfl,
        Mem.readW_writeW_sep (sep_off Bf (.inl (by omega)) (by omega) (by omega)) (by decide), hu.mem]
      exact wt j hj
    · rw [Mem.readW_writeW_self64, hv9]

/-- What a PRF slot needs of its memory: a main squeeze's, `r` at `R`, and buffer `N` at `Bf`. -/
structure SlotLay (p a b st R Bf : Addr) (s : State) : Prop where
  cov : Covers [pairR p, stR st, callR (p + 1536)] s.wr
  hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (Proof.Sha3.AArch64.Neon.wordAddr p i) 16
  hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8
  hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8
  sp : 128 ≤ s.sp.toNat
  dAB : (rateR21 a).Disjoint (rateR21 b)
  dPA : (pairR p).Disjoint (rateR21 a)
  dPB : (pairR p).Disjoint (rateR21 b)
  dPS : (pairR p).Disjoint (stR st)
  dPC : (pairR p).Disjoint (callR (p + 1536))
  dSC : (stR st).Disjoint (callR (p + 1536))
  dSA : (stR st).Disjoint (rateR21 a)
  dSB : (stR st).Disjoint (rateR21 b)
  fP : (frame s.sp).Disjoint (pairR p)
  fS : (frame s.sp).Disjoint (stR st)
  fC : (frame s.sp).Disjoint (callR (p + 1536))
  rin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)
  dSR : (stR st).Disjoint ⟨R, 32⟩
  bout : Covers [rateR Bf] s.wr
  dSF : (stR st).Disjoint (rateR Bf)
  dAF : (rateR21 a).Disjoint (rateR Bf)
  dBF : (rateR21 b).Disjoint (rateR Bf)
  dPF : (pairR p).Disjoint (rateR Bf)

/-- **A main squeeze computing `PRF₂(r, N)` in the third state.** -/
theorem slotPrf_ok (sd bt : Nat) {N : Nat} (hN : N < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt N < 65536) {s : State} {p a b st R Bf : Addr}
    {A B : Spec.Sha3.State}
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = a) (h21 : s.gpr .x21 = b) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N) = Bf)
    (pair : PairAt s.mem p A B) (hl : SlotLay p a b st R Bf s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.slotPrf sd bt N) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p a b st s.sp ++ [rateR Bf]) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem a (keccakF A) ∧ Rate21 t.mem b (keccakF B) ∧
      t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 ∧
      Rate128 t.mem Bf (keccakF (Noise.seedState s.mem R N)) := by
  unfold Impl.MlKem.AArch64.Kem16P.slotPrf
  refine WP.seq (WP.mono (prfBlock_ok hN (by rw [h28]; exact hR) (hsd := hsd) (hsd' := hsd')
    (by rw [h28]; exact Hybrid.covers_mono hl.cov (by simp)) (by rw [h28]; exact hl.dSR) hl.rin)
    fun u ⟨ku, fu, su⟩ => ?_)
  rw [h28] at fu su
  have pu : PairAt u.mem p A B :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dPS)
  refine WP.seq (WP.mono (Hybrid.x3call_ok (q := p + 1536) (S := Noise.seedState s.mem R N)
    (by rw [ku.get .x19, h19]) rfl (by rw [ku.get .x28, h28]) pu su hl.dPS hl.dPC hl.dSC
    (by rw [ku.sp]; exact hl.sp) (by rw [ku.sp]; exact hl.fP) (by rw [ku.sp]; exact hl.fS)
    (by rw [ku.sp]; exact hl.fC) (by rw [ku.wr]; exact hl.cov)) fun v ⟨kv, fv, pv, sv⟩ => ?_)
  rw [ku.sp] at fv
  have kuv := ku.trans kv
  rw [WP.block_append_iff]
  refine WP.mono (Hybrid.tail_ok (by rw [kuv.get .x19, h19]) (by rw [kuv.get .x20, h20])
    (by rw [kuv.get .x21, h21]) pv
    (fun i hi => by rw [kuv.rd, kuv.wr]; exact hl.hin i hi)
    (fun i hi => by rw [kuv.wr]; exact hl.hwa i hi) (fun i hi => by rw [kuv.wr]; exact hl.hwb i hi)
    hl.dAB hl.dPA hl.dPB) fun w ⟨kw, fw, aw, bw, w20, w21⟩ => ?_
  have svt : ∀ r ∈ [rateR21 a, rateR21 b], (stR st).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dSA; exact hl.dSB
  have sw : stateAt w.mem st = keccakF (Noise.seedState s.mem R N) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fw svt, sv]
  have kuw := kuv.trans kw
  refine WP.mono (prfOut_ok bt N hbo (by rw [kuw.get .x28, h28]) hB sw
    (by rw [kuw.rd, kuw.wr]; exact Covers.right (Hybrid.covers_mono hl.cov (by simp)))
    (by rw [kuw.wr]; exact hl.bout) hl.dSF) fun t ⟨kt, ft, rt⟩ => ?_
  have fpt : ∀ r ∈ [rateR Bf], (pairR p).Disjoint r := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact hl.dPF
  refine ⟨(kuw.trans kt).mono (by simp [stepRegs, clobbered]), ?_, ?_,
    rate21_frame aw ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dAF),
    rate21_frame bw ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dBF),
    by rw [kt.get .x20 (by decide), w20], by rw [kt.get .x21 (by decide), w21], rt⟩
  · refine (((fu.mono (by simp [step3Writes])).trans (fv.mono (by simp [step3Writes]))).trans
      (fw.mono (by simp [step3Writes]))).trans (ft.mono (by simp))
  · exact VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame
      (VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pv fw (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl; exact hl.dPA; exact hl.dPB)) ft fpt

end VG.Proof.MlKem.AArch64.Kem16P
