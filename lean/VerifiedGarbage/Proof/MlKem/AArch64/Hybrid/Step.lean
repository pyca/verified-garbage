module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.X3Call
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Absorb
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeBlock

/-!
# One main squeeze of a hashing pair

`step3_ok`: block `blk` of the message's padding XORed into the third state, the `x3`
call, then both SHAKE128 states' 21 words to their stream buffers.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

theorem covers_mono {xs ys X : List Region} (h : Covers ys X) (hs : ∀ r ∈ xs, r ∈ ys) : Covers xs X :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, hs r hr, hc⟩

/-- The squeeze's tail. -/
theorem tail_ok {s : State} {p a b : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19 = p) (ha : s.gpr .x20 = a) (hb : s.gpr .x21 = b)
    (pair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16)
    (hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8)
    (hd : (rateR21 a).Disjoint (rateR21 b))
    (hpa : (pairR p).Disjoint (rateR21 a)) (hpb : (pairR p).Disjoint (rateR21 b)) :
    WP isa (.block Impl.MlKem.AArch64.Hybrid.squeezeTail) s fun t =>
      Keep [.x6, .x7, .x20, .x21] s t ∧ Frame [rateR21 a, rateR21 b] s.mem t.mem ∧
      Rate21 t.mem a A ∧ Rate21 t.mem b B ∧ t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 := by
  unfold Impl.MlKem.AArch64.Hybrid.squeezeTail
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.X2.squeeze_ok (n := 21) (by decide) hp ha hb
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) pair hd hpa hpb hin hwa hwb)
    fun u ⟨hu, hfu, hau, hbu⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  have ku : Keep [.x6, .x7] s u := ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hu.gpr r hr.1 hr.2,
    hu.rd, hu.wr, hu.sp, fun r _ => by rw [hu.vec]⟩
  have ot : Only [.x20, .x21] u t := (h1.trans h2).mono (by simp)
  have hm : t.mem = u.mem := ot.mem
  refine ⟨(ku.trans ot.keep).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact hfu
  · rw [hm]; exact hau
  · rw [hm]; exact hbu
  · rw [h2.get .x20 (by decide), e1, hu.gpr .x20 (by decide) (by decide), ha]; rfl
  · rw [e2, h1.get .x21 (by decide), hu.gpr .x21 (by decide) (by decide), hb]; rfl

/-- The registers a main squeeze may change. -/
def stepRegs : List Reg := clobbered ++ [.x20, .x21]

/-- The regions a main squeeze writes. -/
def step3Writes (p a b st sp : Addr) : List Region :=
  [pairR p, rateR21 a, rateR21 b, callR (p + 1536), stR st, frame sp]

/-- What a main squeeze needs of its memory. -/
structure StepLay (S : Impl.MlKem.AArch64.Hybrid.HSrc) (p a b e st : Addr) (s : State) : Prop where
  cov : Covers [pairR p, stR st, callR (p + 1536)] s.wr
  ek : Covers [⟨e, S.len⟩] (s.rd ++ s.wr)
  hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (wordAddr p i) 16
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
  dSE : (stR st).Disjoint ⟨e, S.len⟩
  fP : (frame s.sp).Disjoint (pairR p)
  fS : (frame s.sp).Disjoint (stR st)
  fC : (frame s.sp).Disjoint (callR (p + 1536))

/-- **A main squeeze** absorbing block `blk`. -/
theorem step3_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {p a b e st : Addr}
    {A B : Spec.Sha3.State} {E : List Byte} {blk : Nat} (hS : SrcOk S)
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = a) (h21 : s.gpr .x21 = b)
    (h25 : s.gpr S.r + BitVec.ofNat 64 S.base = e) (h28 : s.gpr .x28 = st)
    (hb : 136 * blk < S.len)
    (hE : bytesAt s.mem e S.len = E) (hst : stateAt s.mem st = hstate E blk (dB S))
    (pair : PairAt s.mem p A B) (hl : StepLay S p a b e st s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.step3 S blk) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p a b st s.sp) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem a (keccakF A) ∧ Rate21 t.mem b (keccakF B) ∧
      stateAt t.mem st = hstate E (blk + 1) (dB S) ∧
      t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 := by
  refine WP.seq (WP.mono (absorbBlock_ok S hS h25 h28 hb hE hst hl.ek
    (covers_mono hl.cov (by simp))
    hl.dSE) fun u ⟨ku, fu, su⟩ => ?_)
  have pu : PairAt u.mem p A B :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dPS)
  refine WP.seq (WP.mono (x3call_ok (q := p + 1536) (S := stateAt u.mem st)
    (by rw [ku.get .x19, h19]) rfl (by rw [ku.get .x28, h28]) pu rfl hl.dPS hl.dPC hl.dSC
    (by rw [ku.sp]; exact hl.sp) (by rw [ku.sp]; exact hl.fP) (by rw [ku.sp]; exact hl.fS)
    (by rw [ku.sp]; exact hl.fC) (by rw [ku.wr]; exact hl.cov)) fun v ⟨kv, fv, pv, sv⟩ => ?_)
  rw [ku.sp] at fv
  have kuv := ku.trans kv
  refine WP.mono (tail_ok (by rw [kuv.get .x19, h19]) (by rw [kuv.get .x20, h20])
    (by rw [kuv.get .x21, h21]) pv
    (fun i hi => by rw [kuv.rd, kuv.wr]; exact hl.hin i hi)
    (fun i hi => by rw [kuv.wr]; exact hl.hwa i hi) (fun i hi => by rw [kuv.wr]; exact hl.hwb i hi)
    hl.dAB hl.dPA hl.dPB) fun t ⟨kt, ft, at', bt, t20, t21⟩ => ?_
  have fvt : ∀ r ∈ [rateR21 a, rateR21 b], (pairR p).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dPA; exact hl.dPB
  have svt : ∀ r ∈ [rateR21 a, rateR21 b], (stR st).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dSA; exact hl.dSB
  refine ⟨(kuv.trans kt).mono (by simp [stepRegs, clobbered]), ?_, ?_, at', bt, ?_, t20, t21⟩
  · refine ((fu.mono (by simp [step3Writes])).trans (fv.mono (by simp [step3Writes]))).trans
      (ft.mono (by simp [step3Writes]))
  · exact VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pv ft fvt
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame ft svt, sv, su]

end VG.Proof.MlKem.AArch64.Hybrid
