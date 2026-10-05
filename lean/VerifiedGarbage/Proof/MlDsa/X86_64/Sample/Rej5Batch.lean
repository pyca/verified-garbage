import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Parse

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq G PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (segment batch)

/-- Parsing a segment of the second buffer, retaining the squeeze state. -/
structure Batch (σ : State) (n off count K : Nat) (s : State) : Prop where
  sq : SqT σ 3 n s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 =
    BitVec.ofNat 64 (Lt σ k (if k < K then 168 + off + count else 168 + off)).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k)
    (Lt σ k (if k < K then 168 + off + count else 168 + off))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hpre {n off count K : Nat} (hK : K < 4) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count K s) : HPre σ K 1 off count s :=
  ⟨h.sq.env, fun p hp' => by simpa using h.sq.buf K hK p (by omega),
    by simpa only [Nat.mul_one, ite_eq_right (Nat.lt_irrefl K)] using h.j K hK,
    by simpa only [Nat.mul_one, ite_eq_right (Nat.lt_irrefl K)] using h.st K hK⟩

/-- Save the count after one segment, preserving the other polynomials and squeeze state. -/
theorem segmentEnd_ok {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4) {s s₁ : State} (h : Batch σ n off count K s) (hA : HAt σ s K 1 off count count s₁) :
    WP isa (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) s₁ (Batch σ n off count (K + 1)) := by
  have hin : InRegions s₁.wr (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 := in_scr hp hA.env.wr (by simp only [oJ]; omega)
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s₁.mem.writeW (at' σ (oJ + 8 * K)) (s₁.gpr .rdi))
    (by xrun [hA.env.rbx, hin]) rfl) fun s₂ ⟨hm, k⟩ => ?_
  have hf₂ : Frame [jR σ] s₁.mem s₂.mem := by
    rw [hm]; exact jR_write hK (Frame.refl _ _) _
  have k₁ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₁.gpr r = s.gpr r := fun r hr =>
    hA.kp.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨sqT_frame hn (sqT_frame hn h.sq hA.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_poly hp hK) (sub_polyR hK) hA.kp.2.1 hA.kp.2.2 k₁)
    hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2 fun r hr => k.gpr (by simp),
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [Mem.readW_writeW_self64, hA.rdi, ite_eq_left (by omega), Nat.mul_one]
    · rw [rd64_off (by simp only [oJ]; omega) (by simp only [oJ]; omega) (by omega), j_poly hp hK hA.fr hk, h.j k hk]
      congr 3
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · have hL := Lt_length_le σ k (if k < K + 1 then 168 + off + count else 168 + off)
    refine stored_frame hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact poly_jR hp k hk) ?_ hL
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega)]
      simpa only [Nat.mul_one] using hA.stored
    · have := st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

theorem segment_ok {n off count K : Nat} (hn : n ≤ 3) (hK : K < 4)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count K s) :
    WP isa (segment K off count) s (Batch σ n off count (K + 1)) :=
  WP.seq (WP.mono (parse_ok hp hK (by decide) hspan hpos (hpre hK hbuf h))
    fun _ hA => segmentEnd_ok hp hn hK h hA)

theorem batch_ok {n off count : Nat} (hn : n ≤ 3)
    (hspan : off + count ≤ 168) (hpos : 0 < count) (hbuf : 3 * (off + count) ≤ 168 * n)
    {s : State} (h : Batch σ n off count 0 s) :
    WP isa (batch off count) s (Batch σ n off count 4) :=
  WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos hbuf h) fun _ h₁ =>
    WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos hbuf h₁) fun _ h₂ =>
      WP.seq (WP.mono (segment_ok hp hn (by decide) hspan hpos hbuf h₂) fun _ h₃ =>
        segment_ok hp hn (by decide) hspan hpos hbuf h₃)))

omit hp in
theorem batch_of_m2 {s : State} (h : M2 σ 2 s) : Batch σ 2 0 112 0 s :=
  ⟨h.sq, by simpa using h.j, by simpa using h.st⟩

/-- Start the sixth-block parse with the coefficients retained after five. -/
theorem squeeze_last_ok {s : State} (h : Batch σ 2 0 112 4 s) :
    WP isa (squeeze4 2) s (Batch σ 3 112 56 0) := by
  refine WP.mono (sqT_ok hp (by decide) h.sq) fun s' ⟨q, hf⟩ => ⟨q, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oJ + 8 * k) (n := 8)
        (by simp only [oSave, oJ]; omega) (by simp only [oJ]; omega)).symm) (by decide), h.j k hk]
    simp only [ite_eq_left hk, Nat.add_zero, ite_eq_right (Nat.not_lt_zero k)]
  · have st := stored_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp hk).symm)
      (h.st k hk) (Lt_length_le σ k _)
    simpa only [ite_eq_left hk, Nat.add_zero, ite_eq_right (Nat.not_lt_zero k)] using st

end
end VG.Proof.MlDsa.X86_64.Rej4.Segment
