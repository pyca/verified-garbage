import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, correctness

The pieces, in order: the prologue, the round constants and the padded seeds,
and three squeezes (as in `vg_mlkem_sample_ntt4_avx2`); the counts zeroed; the
first half of each seed (`P1`); three more squeezes; the second half of each
seed, which leaves the coefficients of its 1008 bytes of output and the AND of
whether each has 256 in `r14` (`P2`); and the epilogue, which returns it
(`r4K`, as `vg_mldsa_rej_ntt_poly`'s contract `rnK` for each seed).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq G PolyIs)
open VG.Proof.MlKem (xofByte)

/-- `vg_mldsa_rej_ntt_poly4(seeds = rdi, a = rsi, scratch = rdx) -> eax`
(either implementation), with 24 bytes of stack below `rsp`: for each seed,
what `vg_mldsa_rej_ntt_poly`'s contract `rnK` says. -/
def r4K : Contract isa where
  pre := sample4K.pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 4).all (fun k => (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256)
          then 1 else 0) ∧
      ∀ k < 4, (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 →
        PolyIs s'.mem (poly4 (s.gpr .rsi) k) (toPoly (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)))
  pub := sample4K.pub

/-- The coefficients of seed `k`'s whole output. -/
theorem Lt_336 (σ : State) (k : Nat) : Lt σ k 336 = rnFold [] (G (VG.Proof.MlKem.X86_64.S4.B σ k) 1008) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [Xb, VG.Proof.MlDsa.Sample.G_length])]

theorem Lt_zero (σ : State) (k : Nat) : Lt σ k 0 = [] := by
  simp only [Lt, Nat.mul_zero, List.take_zero]; rfl

/-- 1 if each of the first `K` seeds has 256 coefficients, 0 otherwise. -/
def okN (σ : State) (K : Nat) : Nat := if (List.range K).all (fun k => (Lt σ k 336).length == 256) then 1 else 0

/-- Where the counts are kept. -/
abbrev jR (σ : State) : Region := ⟨at' σ oJ, 32⟩

/-- The saved registers. -/
abbrev svR (σ : State) : Region := ⟨at' σ oSave, 40⟩

section
variable {σ : State} (hp : Pre σ)
include hp

/-! ## The regions -/

omit hp in
theorem low_jR : (lowR σ).Disjoint (VG.Proof.MlDsa.X86_64.Rej4.jR σ) :=
  Offset.base_disjoint (scr σ) (k := oSave) (e := oJ) (n := 32) (by simp only [oSave, oJ]; omega)
    (by simp only [oJ]; omega)

omit hp in
theorem sv_jR : (VG.Proof.MlDsa.X86_64.Rej4.svR σ).Disjoint (VG.Proof.MlDsa.X86_64.Rej4.jR σ) :=
  Offset.disjoint (scr σ) (d := oSave) (n := 40) (e := oJ) (k := 32) (.inl (by simp only [oSave, oJ]; omega))
    (by simp only [oSave]; omega) (by simp only [oJ]; omega)

theorem low_poly {K : Nat} (hK : K < 4) : (lowR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (Region.sub_prefix (by simp only [oSave]; omega)))
    (sub_poly hK)

theorem sv_poly {K : Nat} (hK : K < 4) : (VG.Proof.MlDsa.X86_64.Rej4.svR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oSave) (n := 40) (by simp only [oSave]; omega) _ (List.mem_singleton_self _)

theorem jR_poly {K : Nat} (hK : K < 4) : (VG.Proof.MlDsa.X86_64.Rej4.jR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oJ) (n := 32) (by simp only [oJ]; omega) _ (List.mem_singleton_self _)

theorem poly_jR (k : Nat) (hk : k < 4) : (VG.Proof.MlDsa.Sample.polyR (poly4 (aP σ) k)).Disjoint (VG.Proof.MlDsa.X86_64.Rej4.jR σ) :=
  (VG.Proof.MlDsa.X86_64.Rej4.jR_poly hp hk).symm

/-! ## Frames -/

omit hp in
/-- `Env` after writes apart from the saved registers, in the regions of the precondition. -/
theorem env_frame {s s' : State} (he : EnvK σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsv : ∀ r ∈ rs, (VG.Proof.MlDsa.X86_64.Rej4.svR σ).Disjoint r) (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) :
    EnvK σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub hsub)⟩
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (hsv r hr).sub_left
    (Offset.sub (scr σ) (d := oSave + 8 * i) (n := 8) (e := oSave) (k := 40) (by omega) (by omega))) (by decide)]
  exact he.saved i hi

omit hp in
/-- `SqT` after writes apart from the low scratch space and the saved registers. -/
theorem sqT_frame {t n : Nat} (hn : n ≤ 3) {s s' : State} (h : SqT σ t n s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hlow : ∀ r ∈ rs, (lowR σ).Disjoint r) (hsv : ∀ r ∈ rs, (VG.Proof.MlDsa.X86_64.Rej4.svR σ).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r) : SqT σ t n s' := by
  refine ⟨VG.Proof.MlDsa.X86_64.Rej4.env_frame h.env hf hsv hsub hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hg .r14 (by simp), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * (50 + r) + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.rc r hr k hk
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * i + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.lanes i hi k hk
  · rw [frame_byte hf (R := ⟨at' σ (oBuf + 504 * k + p), 1⟩) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := oBuf + 504 * k + p) (by simp only [oBuf, oSave]; omega)))
      (Region.contains_self _ _)]
    exact h.buf k hk p (by omega)

/-- A count, apart from writes to a polynomial. -/
theorem j_poly {K : Nat} (hK : K < 4) {m m' : Mem} (hf : Frame [pR (poly4 (aP σ) K)] m m') {k : Nat} (hk : k < 4) :
    m'.readW (at' σ (oJ + 8 * k)) 64 = m.readW (at' σ (oJ + 8 * k)) 64 :=
  hf.readW (Region.contains_self _ _) (scr_poly hp hK (a := oJ + 8 * k) (n := 8) (by simp only [oJ]; omega))
    (by decide)

omit hp in
/-- A stored polynomial, apart from writes to another one. -/
theorem st_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) {m m' : Mem}
    (hf : Frame [pR (poly4 (aP σ) K)] m m') {L : List Zq} (h : Stored m (poly4 (aP σ) k) L) (hL : L.length ≤ 256) :
    Stored m' (poly4 (aP σ) k) L :=
  stored_frame hf (poly_poly hK hk hne) h hL

omit hp in
theorem sub_polyR {K : Nat} (hK : K < 4) : ∀ r ∈ [pR (poly4 (aP σ) K)], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨aR σ, by simp, sub_poly hK⟩

omit hp in
theorem sub_jR : ∀ r ∈ [VG.Proof.MlDsa.X86_64.Rej4.jR σ], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oJ]; omega)⟩

omit hp in
theorem jR_contains {k : Nat} (hk : k < 4) : (VG.Proof.MlDsa.X86_64.Rej4.jR σ).Contains (at' σ (oJ + 8 * k)) 8 :=
  Offset.contains (scr σ) (d := oJ + 8 * k) (n := 8) (e := oJ) (k := 32) (by omega) (by omega) (by simp only [oJ]; omega)

omit hp in
theorem jR_write {k : Nat} (hk : k < 4) {m m' : Mem} (hf : Frame [VG.Proof.MlDsa.X86_64.Rej4.jR σ] m m') (v : BitVec 64) :
    Frame [VG.Proof.MlDsa.X86_64.Rej4.jR σ] m (m'.writeW (at' σ (oJ + 8 * k)) v) :=
  hf.writeW (List.mem_singleton_self _) v (VG.Proof.MlDsa.X86_64.Rej4.jR_contains hk)

end

/-! ## The first halves -/

/-- After the first half of the seeds before `K`. -/
structure P1 (σ : State) (K : Nat) (s : State) : Prop where
  sq : SqT σ 0 3 s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k (if k < K then 168 else 0)).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k (if k < K then 168 else 0))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem zeroJ_eq : zeroJ = [.mov32 .rax (.imm 0), .store (at_ .rbx (oJ + 8 * 0)) .rax, .store (at_ .rbx (oJ + 8 * 1)) .rax,
    .store (at_ .rbx (oJ + 8 * 2)) .rax, .store (at_ .rbx (oJ + 8 * 3)) .rax] := rfl

/-- The counts zeroed. -/
theorem zeroJ_ok {s : State} (h : SqT σ 0 3 s) : WP isa (.block zeroJ) s (VG.Proof.MlDsa.X86_64.Rej4.P1 σ 0) := by
  have hin : ∀ k < 4, InRegions s.wr (at' σ (oJ + 8 * k)) 8 := fun k hk =>
    in_scr hp h.env.wr (by simp only [oJ]; omega)
  rw [VG.Proof.MlDsa.X86_64.Rej4.zeroJ_eq]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = (((s.mem.writeW (at' σ (oJ + 8 * 0)) (0 : BitVec 64)).writeW
      (at' σ (oJ + 8 * 1)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 2)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 3))
      (0 : BitVec 64))
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide)
      xrun [h.env.rbx, h0, h1, h2, h3]
      rfl)
    (by decide)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [VG.Proof.MlDsa.X86_64.Rej4.jR σ] s.mem s'.mem := by
    rw [hm]
    exact VG.Proof.MlDsa.X86_64.Rej4.jR_write (by decide) (VG.Proof.MlDsa.X86_64.Rej4.jR_write (by decide) (VG.Proof.MlDsa.X86_64.Rej4.jR_write (by decide) (VG.Proof.MlDsa.X86_64.Rej4.jR_write (by decide) (Frame.refl _ _) _) _) _) _
  refine ⟨VG.Proof.MlDsa.X86_64.Rej4.sqT_frame (by decide) h hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.sv_jR) VG.Proof.MlDsa.X86_64.Rej4.sub_jR k.2.1 k.2.2
    fun r hr => k.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm, ite_eq_right (by omega), VG.Proof.MlDsa.X86_64.Rej4.Lt_zero, List.length_nil]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oJ, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [ite_eq_right (by omega), VG.Proof.MlDsa.X86_64.Rej4.Lt_zero]
    exact stored_nil _ _

omit hp in
theorem hpre1 {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P1 σ K s) : HPre σ K 0 s :=
  ⟨h.sq.env, fun p hp' => by rw [h.sq.buf K hK p (by omega)],
    by rw [h.j K hK, ite_eq_right (by omega), Nat.mul_zero],
    by have := h.st K hK; rw [ite_eq_right (by omega)] at this; rwa [Nat.mul_zero]⟩

/-- `j` kept, after the first half of seed `K`. -/
theorem firstEnd_ok {K : Nat} (hK : K < 4) {s s₁ : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P1 σ K s) (hA : HAt σ s K 0 168 s₁) :
    WP isa (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) s₁ (VG.Proof.MlDsa.X86_64.Rej4.P1 σ (K + 1)) := by
  have hin : InRegions s₁.wr (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 := in_scr hp hA.env.wr (by simp only [oJ]; omega)
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s₁.mem.writeW (at' σ (oJ + 8 * K)) (s₁.gpr .rdi))
    (by xrun [hA.env.rbx, hin]) rfl) fun s₂ ⟨hm, k⟩ => ?_
  have hf₂ : Frame [VG.Proof.MlDsa.X86_64.Rej4.jR σ] s₁.mem s₂.mem := by
    rw [hm]; exact VG.Proof.MlDsa.X86_64.Rej4.jR_write hK (Frame.refl _ _) _
  have k₁ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₁.gpr r = s.gpr r := fun r hr =>
    hA.kp.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨VG.Proof.MlDsa.X86_64.Rej4.sqT_frame (by decide) (VG.Proof.MlDsa.X86_64.Rej4.sqT_frame (by decide) h.sq hA.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.low_poly hp hK)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.sv_poly hp hK) (VG.Proof.MlDsa.X86_64.Rej4.sub_polyR hK) hA.kp.2.1 hA.kp.2.2 k₁)
    hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.sv_jR) VG.Proof.MlDsa.X86_64.Rej4.sub_jR k.2.1 k.2.2 fun r hr => k.gpr (by simp),
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [Mem.readW_writeW_self64, hA.rdi, ite_eq_left (by omega)]
    · rw [rd64_off (by simp only [oJ]; omega) (by simp only [oJ]; omega) (by omega), VG.Proof.MlDsa.X86_64.Rej4.j_poly hp hK hA.fr hk, h.j k hk]
      congr 3
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · have hL := Lt_length_le σ k (if k < K + 1 then 168 else 0)
    refine stored_frame hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.X86_64.Rej4.poly_jR hp k hk) ?_ hL
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega)]
      exact hA.stored
    · have := VG.Proof.MlDsa.X86_64.Rej4.st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- The first half of seed `K`. -/
theorem first_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P1 σ K s) : WP isa (first K) s (VG.Proof.MlDsa.X86_64.Rej4.P1 σ (K + 1)) :=
  WP.seq (WP.mono (half_ok hp hK (by decide) (VG.Proof.MlDsa.X86_64.Rej4.hpre1 hK h)) fun _ hA => VG.Proof.MlDsa.X86_64.Rej4.firstEnd_ok hp hK h hA)

end


/-! ## The second halves -/

/-- After the second half of the seeds before `K`. -/
structure P2 (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ K)
  buf : ∀ k < 4, ∀ p < 504, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) (504 + p)
  j : ∀ k < 4, K ≤ k → s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k (if k < K then 336 else 168))

theorem tail_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]) s fun s' =>
      (s'.gpr .r14 = BitVec.setWidth 64 ((s.gpr .r14).setWidth 32 &&& ((s.gpr .rdi) >>> 8).setWidth 32) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- Whether a count is 256, from its bit 8. -/
theorem full_bit {n : Nat} (hn : n ≤ 256) :
    (BitVec.ofNat 64 n >>> 8).setWidth 32 = if n == 256 then 1 else 0 := by
  by_cases e : n = 256
  · subst e; decide
  · rw [ite_eq_right (by simpa using e)]
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [h0]
    omega

theorem okN_succ (σ : State) (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ K)).setWidth 32 &&&
    (BitVec.ofNat 64 (Lt σ K 336).length >>> 8).setWidth 32) = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ (K + 1)) := by
  rw [VG.Proof.MlDsa.X86_64.Rej4.full_bit (Lt_length_le σ K 336)]
  simp only [VG.Proof.MlDsa.X86_64.Rej4.okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;>
    cases (Lt σ K 336).length == 256 <;> rfl

section
variable {σ : State} (hp : Pre σ)
include hp

/-- During the second squeezes: the counts and coefficients of the first halves. -/
structure M2 (σ : State) (n : Nat) (s : State) : Prop where
  sq : SqT σ 3 n s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k 168)

omit hp in
theorem m2_of {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P1 σ 4 s) : VG.Proof.MlDsa.X86_64.Rej4.M2 σ 0 s :=
  ⟨⟨h.sq.env, h.sq.r14, h.sq.rc, h.sq.lanes, fun _ _ p hp' => absurd hp' (by omega)⟩,
    fun k hk => by rw [h.j k hk, ite_eq_left hk], fun k hk => by have := h.st k hk; rwa [ite_eq_left hk] at this⟩

/-- A second squeeze. -/
theorem sqM_ok {n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.M2 σ n s) : WP isa (squeeze4 n) s (VG.Proof.MlDsa.X86_64.Rej4.M2 σ (n + 1)) := by
  refine WP.mono (sqT_ok hp hn h.sq) fun s' ⟨q, hf⟩ => ⟨q, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oJ + 8 * k) (n := 8) (by simp only [oSave, oJ]; omega)
        (by simp only [oJ]; omega)).symm) (by decide), h.j k hk]
  · exact stored_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (VG.Proof.MlDsa.X86_64.Rej4.low_poly hp hk).symm) (h.st k hk)
      (Lt_length_le σ k _)

omit hp in
/-- `vzeroupper`, after the second squeezes. -/
theorem vz_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.M2 σ 3 s) : WP isa (.block [.vop .vzeroupper]) s (VG.Proof.MlDsa.X86_64.Rej4.P2 σ 0) := by
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem) (by xrun; rfl) rfl) fun s' ⟨hm, k⟩ => ?_
  refine ⟨h.sq.env.keep hm k (by simp), by rw [k.gpr (by simp), h.sq.r14]; rfl, fun k hk p hp' => ?_,
    fun k hk _ => by rw [hm]; exact h.j k hk, fun k hk => ?_⟩
  · rw [hm, h.sq.buf k hk p (by omega)]
  · rw [ite_eq_right (by omega), hm]; exact h.st k hk

omit hp in
theorem hpre2 {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P2 σ K s) : HPre σ K 1 s :=
  ⟨h.env, fun p hp' => by rw [h.buf K hK p hp'], by rw [h.j K hK (Nat.le_refl _), Nat.mul_one],
    by have := h.st K hK; rw [ite_eq_right (by omega)] at this; rwa [Nat.mul_one]⟩

/-- The AND of whether seed `K` has 256 coefficients, after its second half. -/
theorem secondEnd_ok {K : Nat} (hK : K < 4) {s s₁ : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P2 σ K s) (hA : HAt σ s K 1 168 s₁) :
    WP isa (.block [.mov .rax (.reg .rdi), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]) s₁ (VG.Proof.MlDsa.X86_64.Rej4.P2 σ (K + 1)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Rej4.tail_ok s₁) fun s₂ ⟨⟨h14, hm⟩, k⟩ => ?_
  have hf : Frame [pR (poly4 (aP σ) K)] s.mem s₂.mem := by rw [hm]; exact hA.fr
  have hrdi : s₁.gpr .rdi = BitVec.ofNat 64 (Lt σ K 336).length := hA.rdi
  refine ⟨hA.env.keep hm k (by simp), ?_, fun k hk p hp' => ?_, fun k hk hKk => ?_, fun k hk => ?_⟩
  · rw [h14, hA.kp.gpr (by decide), h.r14, hrdi, VG.Proof.MlDsa.X86_64.Rej4.okN_succ]
  · rw [frame_byte hf (R := ⟨at' σ (oBuf + 504 * k + p), 1⟩) (scr_poly hp hK (by simp only [oBuf]; omega))
      (Region.contains_self _ _)]
    exact h.buf k hk p hp'
  · rw [hm, VG.Proof.MlDsa.X86_64.Rej4.j_poly hp hK hA.fr hk, h.j k hk (by omega)]
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega)]
      exact hA.stored
    · have := VG.Proof.MlDsa.X86_64.Rej4.st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- The second half of seed `K`. -/
theorem second_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P2 σ K s) : WP isa (second K) s (VG.Proof.MlDsa.X86_64.Rej4.P2 σ (K + 1)) :=
  WP.seq (WP.mono (half_ok hp hK (by decide) (VG.Proof.MlDsa.X86_64.Rej4.hpre2 hK h)) fun _ hA => VG.Proof.MlDsa.X86_64.Rej4.secondEnd_ok hp hK h hA)

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.P2 σ 4 s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, VG.Proof.MlDsa.X86_64.Rej4.okN]
    simp only [VG.Proof.MlDsa.X86_64.Rej4.Lt_336]
    split <;> rfl
  · rw [hm]
    have := h.st k hk
    rw [ite_eq_left hk, VG.Proof.MlDsa.X86_64.Rej4.Lt_336] at this
    exact stored_polyIs this e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {s : State} (h : SqInv σ 0 s) :
    WP isa (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block zeroJ)
      (.seq (first 0) (.seq (first 1) (.seq (first 2) (.seq (first 3)
        (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block [.vop .vzeroupper])
          (.seq (second 0) (.seq (second 1) (.seq (second 2) (.seq (second 3) (.block epi))))))))))))))))) s
      fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqT_ok hp (by decide) (sqT_of h)) fun s₁ ⟨q₁, _⟩ => WP.seq (WP.mono
    (sqT_ok hp (by decide) q₁) fun s₂ ⟨q₂, _⟩ => WP.seq (WP.mono (sqT_ok hp (by decide) q₂) fun s₃ ⟨q₃, _⟩ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.zeroJ_ok hp q₃) fun s₄ p₀ => ?_))))
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.first_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.first_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.first_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.first_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.sqM_ok hp (by decide) (VG.Proof.MlDsa.X86_64.Rej4.m2_of p₄)) fun _ m₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.sqM_ok hp (by decide) m₁)
    fun _ m₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.sqM_ok hp (by decide) m₂) fun _ m₃ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.vz_ok m₃) fun _ r₀ => ?_))))
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.second_ok hp (by decide) r₀) fun _ r₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.second_ok hp (by decide) r₁)
    fun _ r₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.second_ok hp (by decide) r₂) fun _ r₃ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.second_ok hp (by decide) r₃) fun _ r₄ => VG.Proof.MlDsa.X86_64.Rej4.end_ok hp r₄))))

end

theorem correct (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa rejNTT4Avx2 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [VG.Proof.MlDsa.X86_64.Rej4.r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => VG.Proof.MlDsa.X86_64.Rej4.body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of the halves is proven by the taint analysis, from the
pointers (the prologue, the absorption and the first squeeze as in
`vg_mlkem_sample_ntt4_avx2`, `S4.start_ct`). Both runs read the same XOF
output, so in each half's loop they are at the same iteration with the same
coefficients sampled, and each iteration runs as in `vg_mldsa_rej_ntt_poly`
(`RejNttCT.body_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)
open VG.Spec.MlKem (poly4)

theorem pub_Lt4 {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    Lt σ₁ K t = Lt σ₂ K t := by simp only [Lt, Xb, pub_B hq hK]

/-! ## The squeezes -/

theorem sqTaint0 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 0) hc).isSome = true := ⟨_, by taint_decide⟩
theorem sqTaint1 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 1) hc).isSome = true := ⟨_, by taint_decide⟩
theorem sqTaint2 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 2) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A squeeze, from the absorption, given its taint analysis. -/
theorem sqT_ct {t n : Nat} (hn : n < 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R4 fun σ s => SqT σ t n s) (squeeze4 n) (R4 fun σ s => SqT σ t (n + 1) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => WP.mono (sqT_ok (pre_of hp) hn h) fun _ h' => h'.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- A second squeeze, given its taint analysis. -/
theorem sqM_ct {n : Nat} (hn : n < 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.M2 σ n s) (squeeze4 n) (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.M2 σ (n + 1) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => VG.Proof.MlDsa.X86_64.Rej4.sqM_ok (pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

/-! ## The halves -/

/-- Two runs at iteration `t` of a half of seed `K`, from states with `X`,
`n = 168 - t` iterations from its end. -/
def HI (X : State → State → Prop) (K h n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = 168 - t ∧ t < 168 ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ HAt σ₁ s₀₁ K h t s₁ ∧ HAt σ₂ s₀₂ K h t s₂

theorem hbpre {σ : State} (hp : Pre σ) {s₀ : State} {K h t : Nat} (hK : K < 4) (ht : t < 168) {s : State}
    (hI : HAt σ s₀ K h t s) : VG.Proof.MlDsa.X86_64.Sample.RejNttCT.BPre s (poly4 (aP σ) K) (Lt σ K (168 * h + t)) :=
  ⟨hI.rbp, hI.rdi, Lt_length_le σ K _, coeffsWr hp hK hI.env, hI.stored,
    by simpa using hat_regions hp hK hI (j := 0) (by omega), hat_regions hp hK hI (by omega),
    hat_regions hp hK hI (by omega)⟩

theorem hi_brel {X : State → State → Prop} {K h n : Nat} (hK : K < 4) (hh : h < 2) {s₁ s₂ : State}
    (H : VG.Proof.MlDsa.X86_64.Rej4.HI X K h n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, _, ht, _, _, l₁, l₂⟩ := H
  refine ⟨poly4 (aP σ₁) K, Lt σ₁ K (168 * h + t), VG.Proof.MlDsa.X86_64.Rej4.hbpre (pre_of p₁) hK ht l₁,
    by rw [pub_aP hq, VG.Proof.MlDsa.X86_64.Rej4.pub_Lt4 hq hK]; exact VG.Proof.MlDsa.X86_64.Rej4.hbpre (pre_of p₂) hK ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [hat_byte hh l₁ (by omega), hat_byte hh l₂ (by omega)]
  simp only [Xb, pub_B hq hK]

/-- The loop of a half. -/
theorem hloop_ct {X : State → State → Prop} {K h : Nat} (hK : K < 4) (hh : h < 2) (n : Nat) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Rej4.HI X K h n) (.loop rnBody .ne) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 168 s) := by
  refine RelCT.loop (M := isa) (VG.Proof.MlDsa.X86_64.Rej4.HI X K h) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × State × Nat, sample4K.pre p.1 ∧ p.2.2 < 168 ∧
      HAt p.1 p.2.1 K h p.2.2 x →
        HAt p.1 p.2.1 K h (p.2.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (168 - p.2.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y H => VG.Proof.MlDsa.X86_64.Rej4.hi_brel hK hh H) fun _ _ _ => trivial) (fun x y H => ?_) ?_
  · obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, _, _, ht, _, _, l₁, l₂⟩ := H
    exact ⟨WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hp'.2.1 hp'.2.2) ⟨(σ₁, s₀₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hp'.2.1 hp'.2.2) ⟨(σ₂, s₀₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, hn, ht, x₁, x₂, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, s₀₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, s₀₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (168 - t) - 1 == 0) = decide (t + 1 = 168) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 168 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁'⟩, ⟨s₀₂, x₂, l₂'⟩⟩
    · have : t + 1 ≠ 168 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨168 - (t + 1), by omega, σ₁, σ₂, s₀₁, s₀₂, t + 1, p₁, p₂, hq, rfl, by omega, x₁, x₂, l₁', l₂'⟩

/-- The setup of a half. -/
abbrev hsetup (K : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
    .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
    .mov .rdi (.mem (at_ .rbx (oJ + 8 * K))), .mov32 .rcx (.imm 168)]

/-- A half of seed `K` from states with `X`, given the taint analysis of its setup. -/
theorem half_ct {X : State → State → Prop} {K h : Nat} (hK : K < 4) (hh : h < 2)
    (hX : ∀ σ s, sample4K.pre σ → X σ s → HPre σ K h s) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Proof.MlDsa.X86_64.Rej4.hsetup K)) hc).isSome = true) :
    RelCT isa (R4 X) (half K) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 168 s) := by
  unfold half
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 0 s)
      (fun σ s hp hx => WP.mono (hsetup_ok (pre_of hp) hK (hX σ s hp hx)) fun _ h' => ⟨s, hx, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hX σ₁ x p₁ h₁).env
        have e₂ := (hX σ₂ y p₂ h₂).env
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c)) (fun _ _ h => h)
      (Q' := VG.Proof.MlDsa.X86_64.Rej4.HI X K h 168) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩ =>
        ⟨σ₁, σ₂, s₀₁, s₀₂, 0, p₁, p₂, hq, rfl, by decide, x₁, x₂, l₁, l₂⟩) (VG.Proof.MlDsa.X86_64.Rej4.hloop_ct hK hh 168)

/-- The first half of seed `K`, given the taint analysis of its blocks. -/
theorem first_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Proof.MlDsa.X86_64.Rej4.hsetup K)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome =
      true) :
    RelCT isa (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.P1 σ K s) (first K) (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.P1 σ (K + 1) s) :=
  RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.half_ct hK (by decide) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Rej4.hpre1 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => VG.Proof.MlDsa.X86_64.Rej4.firstEnd_ok (pre_of hp) hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

/-- The second half of seed `K`, given the taint analysis of its setup. -/
theorem second_ct {K : Nat} (hK : K < 4) {h₁ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (VG.Proof.MlDsa.X86_64.Rej4.hsetup K)) h₁).isSome = true) :
    RelCT isa (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.P2 σ K s) (second K) (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.P2 σ (K + 1) s) :=
  RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.half_ct hK (by decide) (fun _ _ _ h => VG.Proof.MlDsa.X86_64.Rej4.hpre2 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => VG.Proof.MlDsa.X86_64.Rej4.secondEnd_ok (pre_of hp) hK h₀ hA) (taintRel [] nil_regs (by taint_decide)))

/-! ## The whole function -/

theorem ct : ConstantTime isa r4K.pre r4K.pub rejNTT4Avx2 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq (RelCT.mono (VG.Proof.MlDsa.X86_64.Rej4.sqT_ct (t := 0) (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.sqT_ct (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint1) (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.sqT_ct (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint2) ?_))))
  refine RelCT.seq (relInv (fun σ s hp h => VG.Proof.MlDsa.X86_64.Rej4.zeroJ_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.first_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.first_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.first_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.first_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.mono (VG.Proof.MlDsa.X86_64.Rej4.sqM_ct (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, VG.Proof.MlDsa.X86_64.Rej4.m2_of h₁, VG.Proof.MlDsa.X86_64.Rej4.m2_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.sqM_ct (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint1) (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.sqM_ct (by decide) VG.Proof.MlDsa.X86_64.Rej4.sqTaint2) ?_))
  refine RelCT.seq (relInv (fun σ s _ h => VG.Proof.MlDsa.X86_64.Rej4.vz_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.second_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.second_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.second_ct (K := 2) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.second_ct (K := 3) (by decide) (by taint_decide)) ?_
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4`

The baseline implementation calls `vg_mldsa_rej_ntt_poly` on each seed,
between the prologue and the epilogue of the one for AVX2 (`Rej4Top.lean`):
after the call on seed `K`, polynomial `K` is the seed's `RejNTTPoly` if it
has 256 coefficients, and `r14` records whether the first `K + 1` do (`PC`),
as in `vg_mlkem_sample_ntt4` (`MlKem/X86_64/S4Scalar.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (rejNTT4)
open VG.Proof.MlKem.X86_64 (Keep sample4K relInv taintRel relStart Rel2 pR ret_disj24 stk_disj24'
  ce_bytesAt24 ce_gpr' WP.keep nosp_of)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' sd scr aR scrR stkR sdR pre_of pub_scr pub_aP pub_B pub_sd pub_sp
  env_rbx pro_ok I0 sub_scr sub_poly seed_bytes cov scr6144_lt sx34 sx1024 sx6144 c_sub c_disj and14_ok epi_eq
  cRd cWr in_scr')
open VG.Proof.MlDsa.X86_64.Sample (rnK nil_regs rejNTT_correct rejNTT_ct)
open VG.Proof.MlDsa.Sample (rnFold toPoly)
open VG.Proof.MlDsa.Arith (polyIs_frame)
open VG.Spec.MlKem (poly4)
open VG.Spec.MlDsa (G PolyIs)

theorem rn_nosp : NoSp Impl.MlDsa.X86_64.Sample.rejNTT := nosp_of (by decide +kernel)

theorem rn_depth : Impl.MlDsa.X86_64.Sample.rejNTT.depth = 2 := by decide +kernel

/-- Before the call on seed `K`. -/
structure PC (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ K)
  polys : ∀ k < K, (Lt σ k 336).length = 256 → PolyIs s.mem (poly4 (aP σ) k) (toPoly (Lt σ k 336))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- `PC` after code that writes no memory and keeps its registers. -/
theorem PC.keep {K : Nat} {s s' : State} (h : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hk.gpr (hrs .r14 (by simp)), h.r14], by rw [hm]; exact h.polys⟩

/-- `PC` after the call. -/
theorem PC.call {K : Nat} (hK : K < 4) {s s' : State} (h : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩,
    by rw [hg .r14 (by simp), h.r14], fun k hk e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
        (by omega)
      simpa [poly4] using hd
    · exact (hp.a_scr.sub_left (sub_poly (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (sub_poly (by omega))).symm

/-- The arguments of the call on seed `K`. -/
structure ArgI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K)
  rsi : s.gpr .rsi = poly4 (aP σ) K
  rdx : s.gpr .rdx = at' σ oScalar

omit hp in
theorem argsK_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) s (VG.Proof.MlDsa.X86_64.Rej4.ArgI σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = poly4 (aP σ) K ∧ s'.gpr .rdx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, sx34 hK, sx1024 hK, sx6144]; exact ⟨rfl, rfl⟩) rfl)
    fun _ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ⟨h.keep hm₂ k₂ (by decide), hdi, hsi, hdx⟩

theorem argK_kS {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.ArgI σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 34 * K) (n := 34) (by omega))

theorem argK_pre {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.ArgI σ K s) :
    rnK.pre (s.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := VG.Proof.MlDsa.X86_64.Rej4.argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [rnK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp⟩

/-- After the call on seed `K`. -/
structure CallI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s
  rax : (s.gpr .rax).setWidth 32 = if (Lt σ K 336).length = 256 then 1 else 0
  poly : (Lt σ K 336).length = 256 → PolyIs s.mem (poly4 (aP σ) K) (toPoly (Lt σ K 336))

theorem callK_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.ArgI σ K s) :
    WP isa (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTT) s (VG.Proof.MlDsa.X86_64.Rej4.CallI σ K) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call rejNTT_correct VG.Proof.MlDsa.X86_64.Rej4.rn_nosp (by rw [VG.Proof.MlDsa.X86_64.Rej4.rn_depth]; decide) (VG.Proof.MlDsa.X86_64.Rej4.argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_
  rw [VG.Proof.MlDsa.X86_64.Rej4.rn_depth, h.pinv.env.rsp] at hf
  have h₃ : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [rnK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rsi, hm₃, ce_bytesAt24 s (n := 34) (by decide) (VG.Proof.MlDsa.X86_64.Rej4.argK_kS hp hK h),
    seed_bytes hp hK h.pinv.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  simp only [← VG.Proof.MlDsa.X86_64.Rej4.Lt_336] at hpost
  exact ⟨h₃, hpost.1, hpost.2⟩

omit hp in
theorem okN_succ' (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ K)).setWidth 32 &&&
    (if (Lt σ K 336).length = 256 then 1 else 0)) = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Rej4.okN σ (K + 1)) := by
  simp only [VG.Proof.MlDsa.X86_64.Rej4.okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  by_cases e : (Lt σ K 336).length = 256
  · rw [ite_eq_left e, show ((Lt σ K 336).length == 256) = true by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl
  · rw [ite_eq_right e, show ((Lt σ K 336).length == 256) = false by simpa using e]
    cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;> rfl

omit hp in
theorem andK_ok {K : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.CallI σ K s) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s (VG.Proof.MlDsa.X86_64.Rej4.PC σ (K + 1)) := by
  refine WP.mono (and14_ok s) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  refine ⟨h.pinv.env.keep hm₄ k₄ (by decide), by rw [h14, h.pinv.r14, h.rax, VG.Proof.MlDsa.X86_64.Rej4.okN_succ'], fun k hk e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact h.poly e
  · exact h.pinv.polys k (by omega) e

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.PC σ K s) : WP isa (Impl.MlDsa.X86_64.Sample.Rej4.callK K) s (VG.Proof.MlDsa.X86_64.Rej4.PC σ (K + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.callK_ok hp hK h₂) fun _ h₃ => VG.Proof.MlDsa.X86_64.Rej4.andK_ok h₃))

/-- The return value, and the callee-saved registers restored. -/
theorem endS_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Rej4.PC σ 4 s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, VG.Proof.MlDsa.X86_64.Rej4.okN]
    simp only [VG.Proof.MlDsa.X86_64.Rej4.Lt_336]
    split <;> rfl
  · rw [hm, ← VG.Proof.MlDsa.X86_64.Rej4.Lt_336]
    rw [← VG.Proof.MlDsa.X86_64.Rej4.Lt_336] at e
    exact h.polys k hk e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

theorem scalar_body_ok {s : State} (h : I0 σ s) :
    WP isa (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 0) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 1)
      (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 2) (.seq (Impl.MlDsa.X86_64.Sample.Rej4.callK 3) (.block epi)))))
      s fun s' =>
      r4K.post σ s' ∧ gprPreserved σ s' := by
  have p₀ : VG.Proof.MlDsa.X86_64.Rej4.PC σ 0 s := ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega)⟩
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Rej4.callK_ok' hp (by decide) p₃) fun _ p₄ => VG.Proof.MlDsa.X86_64.Rej4.endS_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa rejNTT4 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [VG.Proof.MlDsa.X86_64.Rej4.r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.pro_ok hp) fun _ h => VG.Proof.MlDsa.X86_64.Rej4.scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

/-! ## Constant time -/

/-- The call on seed `K`. -/
theorem call_ct {K : Nat} (hK : K < 4) :
    RelCT isa (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.ArgI σ K s) (.call "vg_mldsa_rej_ntt_poly" Impl.MlDsa.X86_64.Sample.rejNTT)
      (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.CallI σ K s) :=
  relInv (fun σ s hp h => VG.Proof.MlDsa.X86_64.Rej4.callK_ok (pre_of hp) hK h) (RelCT.callEx rejNTT_correct rejNTT_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, pub_sp hq]
      refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Rej4.argK_pre (pre_of p₁) hK h₁, VG.Proof.MlDsa.X86_64.Rej4.argK_pre (pre_of p₂) hK h₂, ?_,
        (cov (pre_of p₁) h₁.pinv.env hK).1, (cov (pre_of p₁) h₁.pinv.env hK).2,
        (cov (pre_of p₂) h₂.pinv.env hK).1, (cov (pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [rnK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (VG.Proof.MlDsa.X86_64.Rej4.argK_kS (pre_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (VG.Proof.MlDsa.X86_64.Rej4.argK_kS (pre_of p₂) hK h₂),
        seed_bytes (pre_of p₁) hK h₁.pinv.env.frame, seed_bytes (pre_of p₂) hK h₂.pinv.env.frame, pub_B hq hK]
      simp only [pub_sd hq, pub_aP hq, at', pub_scr hq, hsp, and_self])

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.PC σ K s) (Impl.MlDsa.X86_64.Sample.Rej4.callK K) (R4 fun σ s => VG.Proof.MlDsa.X86_64.Rej4.PC σ (K + 1) s) :=
  RelCT.seq (relInv (fun σ s _ h => VG.Proof.MlDsa.X86_64.Rej4.argsK_ok hK h) (taintRel [.r12, .r13, .rbx]
      (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.env.r12, h₂.env.r12, pub_sd hq]
        · rw [h₁.env.r13, h₂.env.r13, pub_aP hq]
        · exact env_rbx hq h₁.env h₂.env) c))
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.call_ct hK) (relInv (fun σ s _ h => VG.Proof.MlDsa.X86_64.Rej4.andK_ok h) (taintRel [] nil_regs (by taint_decide))))

theorem ct_scalar : ConstantTime isa r4K.pre r4K.pub rejNTT4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => VG.Proof.MlDsa.X86_64.Rej4.PC σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (VG.Proof.MlKem.X86_64.S4.pro_ok (pre_of hp)) fun _ h => ⟨h.env, by rw [h.r14]; rfl, fun _ h _ => absurd h (by omega)⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (VG.Proof.MlDsa.X86_64.Rej4.callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_rej_ntt_poly4_avx2`, verified

The contract of the proofs (`r4K`) implies the shared one of `Spec/`: a seed
with 256 coefficients in the 1008 bytes both implementations sample from has
them within those bounds (`rejNTT_some`), and one without has none within the
least bound (`rejNTT_none`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none)
open VG.Proof.MlDsa.X86_64.Sample (leakBytes_inj)
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq : Spec.MlDsa.seed4 = Spec.MlKem.seed4 := rfl
theorem poly4_eq : Spec.MlDsa.poly4 = Spec.MlKem.poly4 := rfl

theorem r4_post {s s' : State} (h : r4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Spec.MlDsa.Reduced s'.mem (Spec.MlDsa.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ b : Spec.MlDsa.Bounds, Spec.MlDsa.rejNTTPoly b.rejNTT
          (Spec.MlDsa.seed4 s.mem (s.gpr .rdi) k) = some (Spec.MlDsa.polyAt s'.mem (Spec.MlDsa.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Spec.MlDsa.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  simp only [VG.Proof.MlDsa.X86_64.Rej4.seed4_eq, VG.Proof.MlDsa.X86_64.Rej4.poly4_eq]
  by_cases hall : ((List.range 4).all fun k =>
      (rnFold [] (G (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, (rnFold [] (G (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1, .inl ⟨hr, fun k hk => ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    rw [rejNTT_some (hs k hk), (hp k hk (hs k hk)).2]
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall, beq_iff_eq] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

theorem r4_pre (s : State) (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) : r4K.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, MlKem.X86_64.sample4K, X86_64.abi,
    X86_64.argRegs]

export VG.Proof.MlDsa.Sample (rej4Res seed4_of136 rej4Res_congr rej4Res_max)

/-- The public data of two calls include their seeds. -/
theorem r4_pub {S : Nat} (s₁ s₂ : State) (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi S).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .rdi) 136 = bytesAt s₂.mem (s₂.gpr .rdi) 136 := by
  sig_pub [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact VG.Proof.MlDsa.X86_64.Sample.leakBytes_inj hb

/-- The result of code that meets `r4K`. -/
theorem rej4_ret {c : Prog isa}
    (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s') {s s' : State}
    {t : List Leak} (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) (e : Exec isa c s t s') :
    (s'.gpr .rax).setWidth 32 = VG.Proof.MlDsa.Sample.rej4Res s.mem (s.gpr .rdi) := by
  obtain ⟨_, _, e', _, hq⟩ := hc s (VG.Proof.MlDsa.X86_64.Rej4.r4_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem rej4_verified (c : Prog isa) (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s')
    (ht : ConstantTime isa r4K.pre r4K.pub c) : Verified X86_64.target c (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := VG.Proof.MlDsa.X86_64.Rej4.r4_pre
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, X86_64.abi, X86_64.argRegs]
        exact VG.Proof.MlDsa.X86_64.Rej4.r4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs]
        sig_simp [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact VG.Proof.MlDsa.X86_64.Sample.leakBytes_inj ‹_›
      sat := by
        sig_implies_sat [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, VG.Proof.MlDsa.X86_64.Rej4.r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [MlKem.X86_64.sample4Sat] using MlKem.X86_64.sample4Sat }

theorem rejNTT4Avx2_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4Avx2
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) := VG.Proof.MlDsa.X86_64.Rej4.rej4_verified _ VG.Proof.MlDsa.X86_64.Rej4.correct VG.Proof.MlDsa.X86_64.Rej4.ct

theorem rejNTT4_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) := VG.Proof.MlDsa.X86_64.Rej4.rej4_verified _ VG.Proof.MlDsa.X86_64.Rej4.correct_scalar VG.Proof.MlDsa.X86_64.Rej4.ct_scalar

theorem rejNTT4Avx2_ret {s s' : State} {t : List Leak} (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4Avx2 s t s') :
    (s'.gpr .rax).setWidth 32 = VG.Proof.MlDsa.Sample.rej4Res s.mem (s.gpr .rdi) := VG.Proof.MlDsa.X86_64.Rej4.rej4_ret VG.Proof.MlDsa.X86_64.Rej4.correct h e

theorem rejNTT4_ret {s s' : State} {t : List Leak} (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4 s t s') :
    (s'.gpr .rax).setWidth 32 = VG.Proof.MlDsa.Sample.rej4Res s.mem (s.gpr .rdi) := VG.Proof.MlDsa.X86_64.Rej4.rej4_ret VG.Proof.MlDsa.X86_64.Rej4.correct_scalar h e

end VG.Proof.MlDsa.X86_64.Rej4

end
