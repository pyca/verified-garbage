module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
      have hf := Noise.noise_fits hr (i := N - P.k) (by omega)
      have hs := Noise.noise_past_kem hr (N - P.k)
      refine ⟨by lom, hf, by omega, .inr hs, by lom⟩
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
        (if N < P.k then ntt (samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) 128))
          else samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) 128)) := by
  have hw := hp.wf
  obtain ⟨tN, tS, t64, tB, tY⟩ := target_ok hw hr hN
  generalize ht : Impl.MlKem.AArch64.Kem16P.target P N = T at tN tS t64 tB tY
  have hN9 : N ≤ 8 := by have := hw.facts; omega
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff P N < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have hfs : T + 1024 ≤ L.len L.sc := by rw [hp.scl]; exact tS
  -- The buffer, its polynomial and the working space.
  have bR : ∀ {l : Nat}, l ≤ 504 → Region.mk (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) l =
      R (kA s₀) L.sc (TP P + 168 * N) l := fun _ => rfl
  have dBT : (Region.mk (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) 128).Disjoint
      (Region.mk (sA L s₀ T) 1024) := by
    rw [bR (by decide)]
    exact hp.args.rdisj hp.scb hp.scb (hp.fs (by lom)) hfs (.inl rfl) (.inr (by
      rcases tB with h | h
      · exact .inr (by omega)
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
  have sample : WP isa (.seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 (Impl.MlKem.AArch64.Kem16P.bufOff P N) ++
      Impl.MlKem.AArch64.ptrTo .x1 .x28 T)) Impl.MlKem.AArch64.Noise.cbdCall) s fun v =>
      Kept [R (kA s₀) L.sc T 1024] s v ∧
      PolyIsW (cw true) v.mem (sA L s₀ T)
        (samplePolyCBD 2 (bytesAt s.mem (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff P N)) 128)) := by
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
      (tv.forward.ready cv)) fun t ⟨kt, pt⟩ st => ?_
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

end VG.Proof.MlKem.AArch64.Kem16P
