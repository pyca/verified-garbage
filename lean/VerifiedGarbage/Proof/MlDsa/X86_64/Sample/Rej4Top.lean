module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Parse
public import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, correctness

The pieces, in order: the prologue, the round constants and the padded seeds,
and three squeezes (as in `vg_mlkem_sample_ntt4_avx2`); the counts zeroed; the
first half of each seed (`P1`); three more squeezes; the second half of each
seed, which leaves the coefficients of its 1008 bytes of output and the AND of
whether each has 256 in `r14`; and the epilogue, which returns it
(`r4K`, as `vg_mldsa_rej_ntt_poly`'s contract `rnK` for each seed).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlDsa (Zq G)
open VG.Proof.MlDsa (PolyIs)
open VG.Proof.MlKem (xofByte)

/-- `vg_mldsa_rej_ntt_poly4(seeds = rdi, a = rsi, scratch = rdx) -> eax`
(either implementation), with 24 bytes of stack below `rsp`: for each seed,
what `vg_mldsa_rej_ntt_poly`'s contract `rnK` says. -/
def r4K : Contract isa where
  pre := sample4K.pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 4).all (fun k => (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256)
          then 1 else 0) ∧
      ∀ k < 4, (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 →
        PolyIs s'.mem (Proof.MlKem.poly4 (s.gpr .rsi) k) (toPoly (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)))
  pub := sample4K.pub

/-- The coefficients of seed `k`'s whole output. -/
theorem Lt_336 (σ : State) (k : Nat) : Lt σ k 336 = rnFold [] (G (B σ k) 1008) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [Xb, G_length])]

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
theorem low_jR : (lowR σ).Disjoint (jR σ) :=
  Offset.base_disjoint (scr σ) (k := oSave) (e := oJ) (n := 32) (by simp only [oSave, oJ]; omega_arith)
    (by simp only [oJ]; omega_arith)

omit hp in
theorem sv_jR : (svR σ).Disjoint (jR σ) :=
  Offset.disjoint (scr σ) (d := oSave) (n := 40) (e := oJ) (k := 32) (.inl (by simp only [oSave, oJ]; omega_arith))
    (by simp only [oSave]; omega_arith) (by simp only [oJ]; omega_arith)

theorem low_poly {K : Nat} (hK : K < 4) : (lowR σ).Disjoint (pR (Proof.MlKem.poly4 (aP σ) K)) :=
  Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (Region.sub_prefix (by simp only [oSave]; omega_arith)))
    (sub_poly hK)

theorem sv_poly {K : Nat} (hK : K < 4) : (svR σ).Disjoint (pR (Proof.MlKem.poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oSave) (n := 40) (by simp only [oSave]; omega_arith) _ (List.mem_singleton_self _)

theorem jR_poly {K : Nat} (hK : K < 4) : (jR σ).Disjoint (pR (Proof.MlKem.poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oJ) (n := 32) (by simp only [oJ]; omega_arith) _ (List.mem_singleton_self _)

theorem poly_jR (k : Nat) (hk : k < 4) : (VG.Proof.MlDsa.Sample.polyR (Proof.MlKem.poly4 (aP σ) k)).Disjoint (jR σ) :=
  (jR_poly hp hk).symm

/-! ## Frames -/

omit hp in
/-- `Env` after writes apart from the saved registers, in the regions of the precondition. -/
theorem env_frame {s s' : State} (he : EnvK σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsv : ∀ r ∈ rs, (svR σ).Disjoint r) (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) :
    EnvK σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub hsub)⟩
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (hsv r hr).sub_left
    (Offset.sub (scr σ) (d := oSave + 8 * i) (n := 8) (e := oSave) (k := 40) (by omega_arith) (by omega_arith))) (by decide)]
  exact he.saved i hi

omit hp in
/-- `SqT` after writes apart from the low scratch space and the saved registers. -/
theorem sqT_frame {t n : Nat} (hn : n ≤ 3) {s s' : State} (h : SqT σ t n s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hlow : ∀ r ∈ rs, (lowR σ).Disjoint r) (hsv : ∀ r ∈ rs, (svR σ).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r) : SqT σ t n s' := by
  refine ⟨env_frame h.env hf hsv hsub hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hg .r14 (by simp), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * (50 + r) + 8 * k) (by simp only [oSave]; omega_arith))) (by decide)]
    exact h.rc r hr k hk
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * i + 8 * k) (by simp only [oSave]; omega_arith))) (by decide)]
    exact h.lanes i hi k hk
  · rw [frame_byte hf (R := ⟨at' σ (oBuf + 504 * k + p), 1⟩) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := oBuf + 504 * k + p) (by simp only [oBuf, oSave]; omega_arith)))
      (Region.contains_self _ _)]
    exact h.buf k hk p (by omega_arith)

/-- A count, apart from writes to a polynomial. -/
theorem j_poly {K : Nat} (hK : K < 4) {m m' : Mem} (hf : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] m m') {k : Nat} (hk : k < 4) :
    m'.readW (at' σ (oJ + 8 * k)) 64 = m.readW (at' σ (oJ + 8 * k)) 64 :=
  hf.readW (Region.contains_self _ _) (scr_poly hp hK (a := oJ + 8 * k) (n := 8) (by simp only [oJ]; omega_arith))
    (by decide)

omit hp in
/-- A stored polynomial, apart from writes to another one. -/
theorem st_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) {m m' : Mem}
    (hf : Frame [pR (Proof.MlKem.poly4 (aP σ) K)] m m') {L : List Zq} (h : Stored m (Proof.MlKem.poly4 (aP σ) k) L) (hL : L.length ≤ 256) :
    Stored m' (Proof.MlKem.poly4 (aP σ) k) L :=
  stored_frame hf (poly_poly hK hk hne) h hL

omit hp in
theorem sub_polyR {K : Nat} (hK : K < 4) : ∀ r ∈ [pR (Proof.MlKem.poly4 (aP σ) K)], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨aR σ, by simp, sub_poly hK⟩

omit hp in
theorem sub_jR : ∀ r ∈ [jR σ], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oJ]; omega_arith)⟩

omit hp in
theorem jR_contains {k : Nat} (hk : k < 4) : (jR σ).Contains (at' σ (oJ + 8 * k)) 8 :=
  Offset.contains (scr σ) (d := oJ + 8 * k) (n := 8) (e := oJ) (k := 32) (by omega_arith) (by omega_arith) (by simp only [oJ]; omega_arith)

omit hp in
theorem jR_write {k : Nat} (hk : k < 4) {m m' : Mem} (hf : Frame [jR σ] m m') (v : BitVec 64) :
    Frame [jR σ] m (m'.writeW (at' σ (oJ + 8 * k)) v) :=
  hf.writeW (List.mem_singleton_self _) v (jR_contains hk)

end

/-! ## The first halves -/

/-- After the first half of the seeds before `K`. -/
structure P1 (σ : State) (K : Nat) (s : State) : Prop where
  sq : SqT σ 0 3 s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k (if k < K then 168 else 0)).length
  st : ∀ k < 4, Stored s.mem (Proof.MlKem.poly4 (aP σ) k) (Lt σ k (if k < K then 168 else 0))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem zeroJ_eq : zeroJ = [.mov32 .rax (.imm 0), .store (at_ .rbx (oJ + 8 * 0)) .rax, .store (at_ .rbx (oJ + 8 * 1)) .rax,
    .store (at_ .rbx (oJ + 8 * 2)) .rax, .store (at_ .rbx (oJ + 8 * 3)) .rax] := rfl

/-- The counts zeroed. -/
theorem zeroJ_ok {s : State} (h : SqT σ 0 3 s) : WP isa (.block zeroJ) s (P1 σ 0) := by
  have hin : ∀ k < 4, InRegions s.wr (at' σ (oJ + 8 * k)) 8 := fun k hk =>
    in_scr hp h.env.wr (by simp only [oJ]; omega_arith)
  rw [zeroJ_eq]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = (((s.mem.writeW (at' σ (oJ + 8 * 0)) (0 : BitVec 64)).writeW
      (at' σ (oJ + 8 * 1)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 2)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 3))
      (0 : BitVec 64))
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide)
      xrun [h.env.rbx, h0, h1, h2, h3]
      rfl)
    (by decide)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [jR σ] s.mem s'.mem := by
    rw [hm]
    exact jR_write (by decide) (jR_write (by decide) (jR_write (by decide) (jR_write (by decide) (Frame.refl _ _) _) _) _) _
  refine ⟨sqT_frame (by decide) h hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2
    fun r hr => k.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm, ite_eq_right (by omega_arith), Lt_zero, List.length_nil]
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := omega_arith) only [oJ, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [ite_eq_right (by omega_arith), Lt_zero]
    exact stored_nil _ _

end

/-! ## The second halves -/

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
    omega_arith

section
variable {σ : State} (hp : Pre σ)
include hp

/-- During the second squeezes: the counts and coefficients of the first halves. -/
structure M2 (σ : State) (n : Nat) (s : State) : Prop where
  sq : SqT σ 3 n s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored s.mem (Proof.MlKem.poly4 (aP σ) k) (Lt σ k 168)

omit hp in
theorem m2_of {s : State} (h : P1 σ 4 s) : M2 σ 0 s :=
  ⟨⟨h.sq.env, h.sq.r14, h.sq.rc, h.sq.lanes, fun _ _ p hp' => absurd hp' (by omega_arith)⟩,
    fun k hk => by rw [h.j k hk, ite_eq_left hk], fun k hk => by have := h.st k hk; rwa [ite_eq_left hk] at this⟩

/-- The second squeezes. -/
theorem sqM_ok {fast : Bool} {b n : Nat} (hn : 0 < n) (hbn : b + n ≤ 3) {s : State} (h : M2 σ b s) :
    WP isa (squeezes b n fast) s (M2 σ (b + n)) := by
  refine WP.mono (sqTs_ok (fast := fast) hp hn hbn h.sq) fun s' ⟨q, hf⟩ => ⟨q, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oJ + 8 * k) (n := 8) (by simp only [oSave, oJ]; omega_arith)
        (by simp only [oJ]; omega_arith)).symm) (by decide), h.j k hk]
  · exact stored_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp hk).symm) (h.st k hk)
      (Lt_length_le σ k _)

end

end VG.Proof.MlDsa.X86_64.Rej4
