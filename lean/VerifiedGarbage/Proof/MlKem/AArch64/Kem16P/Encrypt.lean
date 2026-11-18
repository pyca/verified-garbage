module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps

/-! ### `MlKem.AArch64.Kem16P.Noise`, which this module and modules that import it used -/

section

/-!
# The noise from the matrix's PRF outputs

`outBuf_ok`: `SamplePolyCBD₂` of buffer `N` into its polynomial (`target`:
`ŷ[N]`, `e₁[N - k]` or `e₂`), transformed for `ŷ`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {L : Layout}

/-- Where the polynomial of PRF output `N ≤ 2k` goes. -/
theorem target_ok (hw : P.Wf) (hr : Noise.Room P) {N : Nat} (hN : N ≤ 2 * P.k) :
    NS + 1024 ≤ Impl.MlKem.AArch64.Kem16P.target P N ∧
    Impl.MlKem.AArch64.Kem16P.target P N + 1024 ≤ P.scl ∧
    Impl.MlKem.AArch64.Kem16P.target P N < 65536 ∧
    (Impl.MlKem.AArch64.Kem16P.target P N + 1024 ≤ TP P ∨ SV P + 48 ≤ Impl.MlKem.AArch64.Kem16P.target P N) ∧
    YH P ≤ Impl.MlKem.AArch64.Kem16P.target P N := by
  have := hw.facts
  unfold Impl.MlKem.AArch64.Kem16P.target
  split
  · rename_i h; refine ⟨by lom, by lom, by lom, .inl (by lom), by lom⟩
  · split
    · rename_i h h'
      have hf := Noise.noise_fits hr (i := N - P.k) (by omega_arith)
      have hs := Noise.noise_past_kem hr (N - P.k)
      refine ⟨by lom, hf, by omega_arith, .inr hs, by lom⟩
    · refine ⟨by lom, by lom, by lom, .inl (by lom), by lom⟩

/-- Two PRF outputs' polynomials are apart. -/
theorem target_apart (hw : P.Wf) (hr : Noise.Room P) {N N' : Nat} (hN : N ≤ 2 * P.k) (hN' : N' ≤ 2 * P.k)
    (hne : N ≠ N') :
    Impl.MlKem.AArch64.Kem16P.target P N + 1024 ≤ Impl.MlKem.AArch64.Kem16P.target P N' ∨
    Impl.MlKem.AArch64.Kem16P.target P N' + 1024 ≤ Impl.MlKem.AArch64.Kem16P.target P N := by
  have := hw.facts
  have hs := hr.kem
  have hz := hr.size
  unfold Impl.MlKem.AArch64.Kem16P.target Impl.MlKem.AArch64.Noise.noiseOff
  split <;> split <;> (try split) <;> (try split) <;> lom

/-- `outBuf`: `SamplePolyCBD₂` of buffer `N` into its polynomial, transformed for `ŷ`. -/
theorem outBuf_ok {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s)
    (htr : Optimized.TransformTables s) {N : Nat} (hN : N ≤ 2 * P.k) :
    WP isa (Impl.MlKem.AArch64.Kem16P.outBuf P N) s fun t => KB P L s₀ t ∧
      Frame [R (kA s₀) L.sc (Impl.MlKem.AArch64.Kem16P.target P N) 1024, R (kA s₀) L.sc NS 1024]
        s.mem t.mem ∧ t.gpr .x24 = s.gpr .x24 ∧ t.syms = s.syms ∧
      PolyIsW 16 t.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.target P N))
        (if N < P.k then ntt (samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N)) 128))
          else samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N)) 128)) := by
  have hw := hp.wf
  obtain ⟨tN, tS, t64, tB, tY⟩ := target_ok hw hr hN
  generalize ht : Impl.MlKem.AArch64.Kem16P.target P N = T at tN tS t64 tB tY
  have hN9 : N ≤ 8 := by have := hw.facts; omega_arith
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have hfs : T + 1024 ≤ L.len L.sc := by rw [hp.scl]; exact tS
  -- The buffer, its polynomial and the working space.
  have bR : ∀ {l : Nat}, l ≤ 504 → Region.mk (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N)) l =
      R (kA s₀) L.sc (TP P + 168 * N) l := fun _ => rfl
  have dBT : (Region.mk (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N)) 128).Disjoint
      (Region.mk (sA L s₀ T) 1024) := by
    rw [bR (by decide)]
    exact hp.args.rdisj hp.scb hp.scb (hp.fs (by lom)) hfs (.inl rfl) (.inr (by
      rcases tB with h | h
      · exact .inr (by omega_arith)
      · exact .inl (by lom)))
  have dTN : (polyRegion (sA L s₀ T)).Disjoint (polyRegion (sA L s₀ NS)) :=
    hp.args.rdisj hp.scb hp.scb hfs (hp.fs (by lom)) (.inl rfl) (.inr (.inr tN))
  have cT : Covers [R (kA s₀) L.sc T 1024] s.wr := cov_w hp h ⟨hp.scw, hp.scb⟩ hfs
  have cN : Covers [R (kA s₀) L.sc NS 1024] s.wr := cov_s hp h (by lom)
  have cB : Covers [R (kA s₀) L.sc (TP P + 168 * N) 128] (s.rd ++ s.wr) := cov_sr hp h (by lom)
  have sT : Safe P L s₀ (R (kA s₀) L.sc T 1024) := safe_R hp ⟨hp.scw, hp.scb⟩ hfs (.inr (by
    rcases tB with h | h
    · exact .inr (by lom)
    · exact .inl h))
  have sN : Safe P L s₀ (R (kA s₀) L.sc NS 1024) := safe_scr hp (by lom)
  unfold Impl.MlKem.AArch64.Kem16P.outBuf
  rw [ht]
  simp only [seqs]
  -- The pointers and `SamplePolyCBD₂`.
  have sample : WP isa (.seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N) ++
      Impl.MlKem.AArch64.ptrTo .x1 .x28 T)) Impl.MlKem.AArch64.Noise.cbdCall) s fun v =>
      Kept [R (kA s₀) L.sc T 1024] s v ∧
      PolyIsW (cw true) v.mem (sA L s₀ T)
        (samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N)) 128)) := by
    refine WP.seq (wp_ptrTo (by decide) hbo fun a ha ea => wp_ptrTo' (by decide) t64 fun u hu eu => ?_)
    have ou : Only [.x0, .x1] s u := (ha.trans hu).mono (by simp)
    have ku : Kept [R (kA s₀) L.sc T 1024] s u := Kept.of_keep ou.keep ou.mem (by decide)
    exact cbdW_call (by rw [hu.get .x0 (by decide), ea, e28 h])
      (by rw [eu, ha.get .x28 (by decide), e28 h]) dBT
      (by rw [ou.rd, ou.wr, bR (by decide)]; exact Covers.cons (Covers.head cB) (Covers.right cT))
      (by rw [ou.wr]; exact cT)
      (fun v kv pv => ⟨ku.trans kv, by simpa only [ou.mem] using pv⟩)
  apply WP.assoc
  refine WP.seq (WP.mono_syms sample fun v ⟨kv, pv⟩ sv => ?_)
  have kbv := h.call kv (fun r hr => by rw [List.mem_singleton.mp hr]; exact sT)
  by_cases hk : N < P.k
  · rw [ite_eq_left hk, ite_eq_left hk]
    have tv := htr.frame sv kv.rd kv.wr kv.sp kv.frame cT
    have cv : Covers [polyRegion (sA L s₀ T), polyRegion (sA L s₀ NS)] v.wr := by
      rw [kv.wr]; exact Covers.cons (Covers.head cT) (Covers.cons (Covers.head cN) Covers.nil)
    refine WP.mono_syms (Ntt16.W.nttAtWithW_ok t64 (by decide) (e28 kbv T) (e28 kbv NS)
      (dTN.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right
        (Region.sub_prefix (by decide : 512 ≤ 1024))) pv
      (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head cv))
        (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail cv))) Covers.nil))
      (tv.fast.ready cv)) fun t ⟨kt, pt⟩ st => ?_
    have kt' : Kept [R (kA s₀) L.sc T 1024, R (kA s₀) L.sc NS 1024] v t := kt.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
    refine ⟨kbv.call kt' fun r hr => ?_, (kv.frame.mono (by simp)).trans kt'.frame,
      (kt'.cs .x24 (by decide) (by decide)).trans (kv.cs .x24 (by decide) (by decide)), st.trans sv, pt⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sT
      · exact sN
  · rw [ite_eq_right hk, ite_eq_right hk]
    refine wp_nil ⟨kbv, kv.frame.mono (by simp), kv.cs .x24 (by decide) (by decide), sv, pv⟩

/-! ## The noise -/

/-- What the noise writes: `ŷ` and `e₂`, the NTT's working space, and `e₁`. -/
abbrev noiseW (P : KemLay) (L : Layout) (s₀ : State) : List Region :=
  [R (kA s₀) L.sc (YH P) (1024 * P.k + 1024), R (kA s₀) L.sc NS 1024,
    R (kA s₀) L.sc (Impl.MlKem.AArch64.Noise.noiseOff P 0) (1024 * P.k)]

/-- The polynomial of PRF output `N`: `ŷ[N]`, `e₁[N - k]` or `e₂`. -/
def tPoly (P : KemLay) (rv : List Byte) (N : Nat) : Poly := if N < P.k then encY rv N else cbd rv N

/-- After the polynomials of the first `j` PRF outputs. -/
structure NInv (P : KemLay) (L : Layout) (s₀ s : State) (rv : List Byte) (j : Nat) (t : State) : Prop where
  kb : KB P L s₀ t
  x24 : t.gpr .x24 = s.gpr .x24
  syms : t.syms = s.syms
  fr : Frame (noiseW P L s₀) s.mem t.mem
  done : ∀ N < j, PolyIsW 16 t.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.target P N)) (tPoly P rv N)

theorem target_sub (hw : P.Wf) (hr : Noise.Room P) {s₀ : State} {N : Nat} (hN : N ≤ 2 * P.k) :
    ∃ r' ∈ noiseW P L s₀, Region.Sub (R (kA s₀) L.sc (Impl.MlKem.AArch64.Kem16P.target P N) 1024) r' := by
  have := hw.facts
  unfold Impl.MlKem.AArch64.Kem16P.target
  split
  · exact ⟨_, List.mem_cons_self .., R.sub2 (by lom) (by lom)⟩
  · split
    · rename_i h h'
      have := hr.size
      refine ⟨R (kA s₀) L.sc (Impl.MlKem.AArch64.Noise.noiseOff P 0) (1024 * P.k), by simp, R.sub2 ?_ ?_⟩ <;>
        simp only [Impl.MlKem.AArch64.Noise.noiseOff] <;> omega_arith
    · exact ⟨_, List.mem_cons_self .., R.sub2 (by lom) (by lom)⟩

/-- What the noise writes misses a region below `YH` or between `TP` and `SV`. -/
theorem noiseW_far {s₀ : State} (hp : Pre P L s₀) (hr : Noise.Room P) {o l : Nat} (hf : o + l ≤ SV P + 48)
    (ho : o + l ≤ NS ∨ (NS + 1024 ≤ o ∧ o + l ≤ YH P) ∨ TP P ≤ o) :
    ∀ r ∈ noiseW P L s₀, (R (kA s₀) L.sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact sdisj hp hf (by lom) (by rcases ho with h | h | h <;> lom)
  · exact sdisj hp hf (by lom) (by rcases ho with h | h | h <;> lom)
  · have hs := Noise.noise_past_kem hr 0
    have hz := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega_arith)
    refine hp.args.rdisj hp.scb hp.scb (hp.fs hf) ?_ (.inl rfl) (.inr (.inl (by omega_arith)))
    rw [hp.scl]; simp only [Impl.MlKem.AArch64.Noise.noiseOff] at hz ⊢; have := hw.facts; omega_arith

/-- **The noise** from the buffers of the first `n ≥ 2k` PRF outputs. -/
theorem noiseP_ok {prf : Nat → Nat → Prog isa} {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (h : KB P L s₀ s) (htr : Optimized.TransformTables s) {n : Nat} (hn : 2 * P.k ≤ n) {rv : List Byte}
    (hrv : bytesAt s.mem (sA L s₀ RB) 32 = rv)
    (hprf : ∀ N < min n (Impl.MlKem.AArch64.Kem16P.prfs P), PrfAt P L s₀ s.mem s.mem N) :
    WP isa (Impl.MlKem.AArch64.Kem16P.noiseP prf P n) s
      (NInv P L s₀ s rv (min n (Impl.MlKem.AArch64.Kem16P.prfs P))) := by
  have hw := hp.wf
  have hc : min n (Impl.MlKem.AArch64.Kem16P.prfs P) ≤ 2 * P.k + 1 := by
    simp only [Impl.MlKem.AArch64.Kem16P.prfs]; omega_arith
  have hnil : (List.range (2 * P.k)).filter (n ≤ ·) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simp only [List.mem_range] at hx; simp; omega_arith
  unfold Impl.MlKem.AArch64.Kem16P.noiseP
  rw [hnil, List.map_nil, List.append_nil]
  have hne : 0 < min n (Impl.MlKem.AArch64.Kem16P.prfs P) := by
    simp only [Impl.MlKem.AArch64.Kem16P.prfs]; have := hw.facts; omega_arith
  apply WPs.seqs (map_range_ne_nil hne _)
  refine WPs.range (fun j hj t ht => ?_) ⟨h, rfl, rfl, Frame.refl _ _, fun N hN => absurd hN (Nat.not_lt_zero _)⟩
  have hjk : j ≤ 2 * P.k := by omega_arith
  have cW : Covers (noiseW P L s₀) s.wr := by
    refine Covers.cons (cov_s hp h (by lom)) (Covers.cons (cov_s hp h (by lom)) (Covers.cons ?_ Covers.nil))
    refine cov_w hp h ⟨hp.scw, hp.scb⟩ ?_
    rw [hp.scl]; have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega_arith)
    simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega_arith
  have tt := htr.frame ht.syms (ht.kb.rd.trans h.rd.symm) (ht.kb.wr.trans h.wr.symm) (ht.kb.sp.trans h.sp.symm)
    ht.fr cW
  refine WP.mono (outBuf_ok hp hr ht.kb tt hjk) fun u ⟨ku, fu, xu, su, pu⟩ => ?_
  obtain ⟨tN, tS, t64, tB, tY⟩ := target_ok hw hr hjk
  have dS : ∀ r ∈ [R (kA s₀) L.sc (Impl.MlKem.AArch64.Kem16P.target P j) 1024, R (kA s₀) L.sc NS 1024],
      ∃ r' ∈ noiseW P L s₀, Region.Sub r r' := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact target_sub hw hr hjk
    · exact ⟨_, by simp, fun _ h => h⟩
  -- The buffer is as the matrix left it.
  have hb : bytesAt t.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) j)) 128 = VG.Spec.MlKem.prf 2 rv (BitVec.ofNat 8 j) := by
    rw [show sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) j) = sA L s₀ (TP P + 168 * j) from rfl,
      bytesAt_frame ht.fr (noiseW_far hp hr (o := TP P + 168 * j) (l := 128) (by lom) (.inr (.inr (by lom))))
        (by decide), ← hrv]
    exact Noise.output_prf (by have := hw.facts; omega_arith) (hprf j hj)
  refine ⟨ku, xu.trans ht.x24, su.trans ht.syms, ht.fr.trans (fu.sub dS), fun N hN => ?_⟩
  rcases (by omega_arith : N < j ∨ N = j) with hN | rfl
  · refine polyIsW_frame_poly (w16 := true) fu (fun r hr' => ?_) (ht.done N hN)
    obtain ⟨tN', tS', t64', tB', tY'⟩ := target_ok hw hr (N := N) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    have hfs : ∀ {M : Nat}, M ≤ 2 * P.k →
        Impl.MlKem.AArch64.Kem16P.target P M + 1024 ≤ L.len L.sc := fun hM => by
      rw [hp.scl]; exact (target_ok hw hr hM).2.1
    rcases hr' with rfl | rfl
    · exact hp.args.rdisj hp.scb hp.scb (hfs (by omega_arith)) (hfs hjk) (.inl rfl)
        (.inr (target_apart hw hr (by omega_arith) hjk (by omega_arith)))
    · exact hp.args.rdisj hp.scb hp.scb (hfs (by omega_arith)) (hp.fs (by lom)) (.inl rfl) (.inr (.inr tN'))
  · rw [hb] at pu
    exact pu

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-! ### `MlKem.AArch64.Kem16P.VRest`, which only this module used -/

section

/-! # `v` with `e₂` from the matrix

`v_restP`: `Kem16P.vRestP`, which computes `e₂` with `prf` as `Kem16.vRest`
does (`v_restW`), or, when the matrix computed it (`e2`), finds it at `EP`
(`v_restE`, as `v_restW` with `e₂` kept through the decoding, the dot product
and the inverse transform). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem v_tailE {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (e₀ : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Optimized.TransformTables s)
    (t₀ : PolyIsW 16 s.mem (sA L s₀ (TP P)) (KPke.dotK T (encY rv) P.k))
    (e2 : PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,.block [],Kem16.addWAt (TP P) (EP P),
      Kem16.widenAt (TP P) (PP P),ddAt .x28 MB 1 (EP P),addAt (PP P) (EP P),
      P.ceLAt (PP P) P.dv (slotReg kC) (co+32*P.du*P.k)] s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) e₀.kb t₀.1 ht) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  obtain e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  obtain p₂ : PolyIsW 16 s₁.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact papart hp (po_EP hw) (po_TP hw) (by lom)
      · exact sdisj hp (po_EP hw).le (by lom) (by lom)) e2
  refine WPs.cons (wp_nil ?_)
  have kb₂ := kb₁
  have e₂ := e₁
  have t₂ := t₁
  refine WPs.cons (WP.mono (addW_read_ok hp (po_TP hw) (by lom) (.inr (by lom)) kb₂ t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  obtain e₃ := e₂.frame_far hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  obtain e₄ := e₃.frame_far hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₄.kb)
    fun s₅ ⟨kb₅, f₅, p₅, x₅⟩ => ?_)
  obtain e₅ := e₄.frame_far hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  obtain t₅ := polyIs_frame f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₄
  have hm : bytesAt s₄.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₄.m
  rw [hm] at p₅
  refine WPs.cons (WP.mono (add_ok hp (po_PP hw) (po_EP hw) (.inr (by lom)) e₅.kb t₅.1 p₅.1)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  obtain e₆ := e₅.frame_far hp kb₆ x₆ f₆ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₅.2, p₅.2] at t₆
  have fC := A.fC
  obtain hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (ceL_ok hp hc (off := PP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (po_PP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₆.kb t₆.1) fun s₇ ⟨kb₇, f₇, b₇, x₇⟩ => ?_)
  refine ⟨e₆.frame_far hp kb₇ x₇ f₇ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₇, t₆.2]

theorem v_restE {prf : Nat→Nat→Prog isa} {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (e2 : PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (Impl.MlKem.AArch64.Kem16P.vRestP prf P true (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  apply WPs.seqs (by simp)
  apply WPs.append
  refine WPs.mono_syms (v_decodeW hp A hT h) fun t ⟨vt,dt⟩ hs => ?_
  obtain ga : ∀r∈[R (kA s₀) L.sc AH (1024*P.k)],
      (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r := by
    intro r hh
    rw [List.mem_singleton.mp hh]
    obtain ⟨r',hm,hh'⟩ := (firstRow_vfar hp A).2.2.2.2
    exact (ha r' hm).sub_right hh'
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht dt.frame ga
  obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,dt.kb.rd,dt.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  obtain da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hs]
    exact ((ha (R (kA s₀) L.sc PB (SV P-PB)) (by simp [encW])).sub_right
      (R.sub2 (by lom) (by lom))).symm
  obtain trt := htr.frame hs (dt.kb.rd.trans h.kb.rd.symm) (dt.kb.wr.trans h.kb.wr.symm)
    (dt.kb.sp.trans h.kb.sp.symm) dt.frame (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) dt.kb (decodedTerms P)
    (decoded_readyW hp dt gt ct da).data) fun u ⟨ku,fu,pu,xu⟩ hsu => ?_)
  rw [decoded_sum] at pu
  obtain vu := vt.frame_far hp ku xu fu (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  obtain tru := trt.frame hsu (ku.rd.trans dt.kb.rd.symm) (ku.wr.trans dt.kb.wr.symm)
    (ku.sp.trans dt.kb.sp.symm) fu (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  obtain e2t : PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) dt.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (po_EP hw).le (by lom) (by lom)) e2
  obtain e2u : PolyIsW 16 u.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) e2t
  exact v_tailE hp hc A vu tru pu e2u

theorem v_restP {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) (e2 : Bool)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (he : e2 = true → PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (Impl.MlKem.AArch64.Kem16P.vRestP prf P e2 (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  cases e2
  · exact v_restW valid hp hc A hT htr h ht hcT ha
  · exact v_restE hp hc A hT htr h ht hcT ha (he rfl)

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Kem16P.URow`, which only this module used -/

section

/-! # The rows of `u`, keeping `e₂`

`u_rowsE`: `Kem16.u_rowsW`, with a polynomial at `EP` (`e₂`, which the
matrix computed) kept through the rows. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem fused_u_rowE {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (uTerms P i) F G = KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k)
    (ht : Optimized.TransformTables s)
    (he : PolyIsW 16 s.mem (sA L s₀ (noiseOff P i)) (cbd rv (P.k+i)))
    {E : Poly} (hE : PolyIsW 16 s.mem (sA L s₀ (EP P)) E) :
    WP isa (Kem16.uRow P (slotReg kC) co i) s
      (fun t => EInvW true P L s₀ kC co mE mB v rv mv P.k (i+1) t ∧ PolyIsW 16 t.mem (sA L s₀ (EP P)) E) := by
  have hw := hp.wf
  obtain hn : i≤P.k := Nat.le_of_lt hi
  obtain ef : noiseOff P i+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hi
  obtain ep := Noise.noise_past_kem hr i
  obtain far : ∀r∈[R (kA s₀) L.sc (TP P) 1024,R (kA s₀) L.sc NS 1024],
      (polyRegion (sA L s₀ (noiseOff P i))).Disjoint r := by
    intro r hh
    rcases mem2' hh with rfl | rfl <;>
      exact hp.args.rdisj hp.scb hp.scb ef (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  simp only [Kem16.uRow, seqs]
  refine WP.seq (WP.mono_syms (WP.mono (fusedW_ok hp (po_TP hw) h.kb (uTerms P i) hd)
    fun t ⟨kt,ft,pt,xt⟩ => (⟨h.frame hp kt xt ft (far_one hp A (Nat.le_refl _) hn (by lom) (by lom)),ft,pt⟩ :
      EInvW true P L s₀ kC co mE mB v rv mv P.k i t ∧ _ ∧ _)) fun s₁ ⟨e₁,f₁,t₁⟩ sy₁ => ?_)
  obtain p₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁
    (fun r hh => far r (by rw [List.mem_singleton.mp hh]; exact List.mem_cons_self ..)) he
  rw [hsum] at t₁
  obtain q₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) hE
  obtain ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (invW_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  obtain e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  obtain p₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ far p₁
  rw [t₁.2] at t₂
  obtain q₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ (fun r hh => by
    rcases mem2' hh with rfl | rfl
    · exact papart hp (po_EP hw) (po_TP hw) (by lom)
    · exact sdisj hp (po_EP hw).le (by lom) (by lom)) q₁
  refine WP.seq (WP.mono (addW_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₃ ⟨kb₃,f₃,t₃,x₃⟩ => ?_)
  obtain e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₃
  obtain q₃ : PolyIsW 16 s₃.mem _ _ := polyIsW_frame_poly (w16 := true) f₃ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) q₂
  refine WP.seq (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  obtain e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  obtain q₄ : PolyIsW 16 s₄.mem _ _ := polyIsW_frame_poly (w16 := true) f₄ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_PP hw) (by lom)) q₃
  have fC := A.fC
  obtain hu := du_le hi
  refine WP.mono (ceL_ok hp hc (off := PP P) (d := P.du) (k := kC) (o := co+32*P.du*i)
    (po_PP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom,.inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅,f₅,b₅,x₅⟩ => ?_
  obtain e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hh => by
    rw [List.mem_singleton.mp hh]; exact far_ct hp A (Nat.le_refl _) (by lom)
  obtain q₅ : PolyIsW 16 s₅.mem _ _ := polyIsW_frame_poly (w16 := true) f₅ (fun r hh => by
    rw [List.mem_singleton.mp hh]
    refine hp.args.rdisj hp.scb (hp.lt A.hkC) (hp.fs (po_EP hw).le) (by lom) (.inr (.inr A.wC)) ?_
    rcases A.sC with hC | hC
    · exact .inl (Ne.symm hC)
    · subst hC; exact .inr (.inl (by lom))) q₄
  refine ⟨⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩, q₅⟩
  rcases (by omega_using [hj] : j<i ∨ j=i) with hj | rfl
  · exact e₅.u j hj
  · rw [b₅,t₄.2]; rfl

theorem u_rowsE {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    {E : Poly} (hE : PolyIsW 16 s.mem (sA L s₀ (EP P)) E) :
    WPs ((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) s
      (fun t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧ t.syms=s.syms ∧
        PolyIsW 16 t.mem (sA L s₀ (EP P)) E) := by
  apply WPs.range (I := fun i t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k i t ∧ t.syms=s.syms ∧
    PolyIsW 16 t.mem (sA L s₀ (EP P)) E)
  · intro i hi t ⟨ei,hs,qi⟩
    obtain et := he.frame_enc hp hr A ei.fr
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht ei.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,ei.kb.rd,ei.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    obtain da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
      rw [hs]
      have hw := hp.wf
      obtain hsub : Region.Sub (R (kA s₀) L.sc (TP P) 1024) (R (kA s₀) L.sc PB (SV P-PB)) :=
        R.sub2 (by lom) (by lom)
      exact ((ha _ (by simp [encW])).sub_right hsub).symm
    exact WP.mono_syms (fused_u_rowE hp hr hc A hi ei (u_readyW hp hi ei gt ct da).data
      (u_sumW hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi) qi)
      fun u ⟨hu,qu⟩ hsu => ⟨hu,hsu.trans hs,qu⟩
  · exact ⟨h,rfl,hE⟩

end VG.Proof.MlKem.AArch64.Kem

end

end


/-! # The 16-bit encryption after the matrix computed PRF outputs

`encrypt_restP`: `Kem16P.encryptRestP`, the noise from the buffers
(`noiseP_ok`), then the rows of `u` and `v` (`after_noiseP`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem16P
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}
variable {prf : Nat→Nat→Prog isa}

/-- The rows of `u` and `v`, `e₂` at `EP` already if `e2`. -/
theorem after_noiseP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) (e2 : Bool)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hE : e2 = true → PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (seqs (((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) ++
      [Impl.MlKem.AArch64.Kem16P.vRestP prf P e2 (slotReg kE) eo .x28 MB (slotReg kC) co])) s
      (fun t => VInvW P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  apply WPs.seqs (by simp)
  apply WPs.append
  cases e2
  · refine WPs.mono (u_rowsW hp hr hc A htr h he ht hcT ha) fun t ⟨et,hs⟩ => ?_
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A false hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun h => absurd h (by decide)))
  · refine WPs.mono (u_rowsE hp hr hc A htr h he ht hcT ha (hE rfl)) fun t ⟨et,hs,qt⟩ => ?_
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A true hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun _ => qt))

/-- What the noise writes, `scratch` may be written. -/
theorem noiseW_cov {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s) :
    Covers (noiseW P L s₀) s.wr := by
  have hw := hp.wf
  refine Covers.cons (cov_s hp h (by lom)) (Covers.cons (cov_s hp h (by lom)) (Covers.cons ?_ Covers.nil))
  refine cov_w hp h ⟨hp.scw, hp.scb⟩ ?_
  rw [hp.scl]; have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega_using [this])
  simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega_arith

/-- **The noise, `u` and `v`**, the first `n ≥ 2k` PRF outputs in their buffers. -/
theorem encrypt_restP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {n : Nat} (hn : 2 * P.k ≤ n)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co mE mB v rv mv 0 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn' : ∀r∈noiseW P L s₀, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hprf : ∀ N < min n (Impl.MlKem.AArch64.Kem16P.prfs P), PrfAt P L s₀ s.mem s.mem N) :
    WP isa (Impl.MlKem.AArch64.Kem16P.encryptRestP prf P n (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => ∃mN, Frame (noiseW P L s₀) s.mem mN ∧
        VInvW P L s₀ kC co mN mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  have hk := hw.facts
  refine WP.seq (WP.mono (noiseP_ok (prf := prf) hp hr h.kb htr hn h.r hprf) fun t nt => ?_)
  obtain hcnt : 2 * P.k ≤ min n (Impl.MlKem.AArch64.Kem16P.prfs P) := by
    simp only [Impl.MlKem.AArch64.Kem16P.prfs]; omega_using [hn]
  obtain far : ∀ {o l : Nat}, o + l ≤ SV P + 48 →
      (o + l ≤ NS ∨ (NS + 1024 ≤ o ∧ o + l ≤ YH P) ∨ TP P ≤ o) →
      ∀ r ∈ noiseW P L s₀, (R (kA s₀) L.sc o l).Disjoint r := fun hf ho => noiseW_far hp hr hf ho
  obtain e0 : EInvW true P L s₀ kC co t.mem mB v rv mv P.k 0 t := by
    refine ⟨nt.kb, nt.x24.trans h.x24, ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_,
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
    · rw [bytesAt_frame nt.fr (far (o := RB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.r
    · rw [bytesAt_frame nt.fr (far (o := MB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.m
    · have := ij_lt hi hj
      obtain fa := far (o := aOff P i j) (l := 1024) (by lom) (.inr (.inl ⟨by lom, by lom⟩))
      exact ⟨reducedW_frame nt.fr fa (h.a i hi j hj).1, (polyAtW_frame nt.fr fa).trans (h.a i hi j hj).2⟩
    · have d := nt.done j (by omega_using [hcnt, hj])
      simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_left hj] at d
      exact d
  obtain er : ErrorsW P L s₀ rv t := by
    intro j hj
    obtain d := nt.done (P.k + j) (by omega_using [hcnt, hj])
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ P.k + j < P.k by omega_using []),
      ite_eq_left (show P.k + j < 2 * P.k by omega_using [hj]), Nat.add_sub_cancel_left] at d
    exact d
  obtain hE : decide (Impl.MlKem.AArch64.Kem16P.prfs P ≤ n) = true →
      PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) := by
    intro he
    obtain he' : Impl.MlKem.AArch64.Kem16P.prfs P ≤ n := of_decide_eq_true he
    obtain d := nt.done (2 * P.k) (by simp only [Impl.MlKem.AArch64.Kem16P.prfs] at he' ⊢; omega_using [he'])
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ 2 * P.k < P.k by omega_using []),
      Nat.lt_irrefl, ite_false] at d
    exact d
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [nt.syms]; exact gamma_frame ht nt.fr hn'
  obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [nt.syms, nt.kb.rd, nt.kb.wr, ← h.kb.rd, ← h.kb.wr] using hcT
  obtain tt := htr.frame nt.syms (nt.kb.rd.trans h.kb.rd.symm) (nt.kb.wr.trans h.kb.wr.symm)
    (nt.kb.sp.trans h.kb.sp.symm) nt.fr (noiseW_cov hp hr h.kb)
  exact WP.mono (after_noiseP valid hp hr hc A _ hT tt e0 er gt ct (by simpa only [nt.syms] using ha) hE)
    fun u ⟨eu, vu⟩ => ⟨t.mem, nt.fr, eu, vu⟩

end VG.Proof.MlKem.AArch64.Kem16P
