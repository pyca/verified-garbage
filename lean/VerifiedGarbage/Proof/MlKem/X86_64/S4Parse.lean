module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`, sampling

What holds during the loop of `vg_mlkem_sample_ntt4_avx2` on the buffer of
seed `k` (`LAt`), and an iteration of `vg_mlkem_sample_ntt`'s loop on it
(`lat_step`, as `SampleNtt.lean`'s); the rest of that loop is in
`S4Loop.lean`. Then what holds between the calls of `vg_mlkem_sample_ntt`
of the baseline implementation (`PC`), and the calls.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)
open VG.Spec.Sha3 (bytesAt)

/-- Whether the first `K` seeds sample their polynomials. -/
def okN (σ : State) (K : Nat) : Nat :=
  if (List.range K).all fun k => (sampleNTT minIterations (B σ k)).isSome then 1 else 0

/-- The table of the sampling and the constants of the vector code, from
byte `oTab` of `scratch`. -/
def TabOK (σ : State) (m : Mem) : Prop := ∀ i < 280, m.readW (at' σ (oTab + 8 * i)) 64 = tabQ i

/-- Where the table is. -/
abbrev tabR (σ : State) : Region := ⟨at' σ oTab, 2240⟩

/-- The table is kept by writes elsewhere. -/
theorem tab_frame {σ : State} {m m' : Mem} {rs : List Region} (hd : ∀ r ∈ rs, Region.Disjoint (tabR σ) r)
    (hf : Frame rs m m') (h : TabOK σ m) : TabOK σ m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (Offset.contains _ (by simp only [oTab]; omega) (by simp only [oTab]; omega)
    (by simp only [oTab]; omega)) hd (by decide)

/-- Before the `K`-th polynomial, with `X` of the memory. -/
structure PCW (w16 : Bool) (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  buf : X s.mem
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ K)
  polys : ∀ k < K, ∀ f, sampleNTT minIterations (B σ k) = some f → PolyIsW (cw w16) s.mem (poly4W w16 (aP σ) k) f

/-- `PCW` with 32-bit coefficients. -/
abbrev PC := PCW false

/-- The coefficients of seed `K` after `t` iterations. -/
abbrev Lt (σ : State) (K t : Nat) : List Zq := sampleAfter [] (xofByte (B σ K)) t

/-- What the iterations of the loop on seed `K` keep, from `s₀`: its buffer
holds bytes `3 b` on of its XOF output, and only polynomial `K` is written. -/
structure LBW (w16 : Bool) (σ s₀ : State) (K b : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = s₀.gpr .r14
  tab : TabOK σ s.mem
  out : ∀ p < 504, 3 * b + p < 840 → s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (3 * b + p)
  fr : Frame [cRegion w16 (poly4W w16 (aP σ) K)] s₀.mem s.mem

/-- `LBW` with 32-bit coefficients. -/
abbrev LB := LBW false

/-- At iteration `b + t` of the loop on seed `K`, at byte `3 t` of its buffer. -/
structure LAtW (w16 : Bool) (σ s₀ : State) (K b t : Nat) (s : State) : Prop where
  lb : LBW w16 σ s₀ K b s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K (b + t)).length
  rbp : s.gpr .rbp = poly4W w16 (aP σ) K
  stored : Stored w16 s.mem (poly4W w16 (aP σ) K) (Lt σ K (b + t))

/-- `LAtW` with 32-bit coefficients. -/
abbrev LAt := LAtW false

/-- A byte apart from the regions of a frame. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    {x : Addr} (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

/-- Stored coefficients, apart from the regions of a frame. -/
theorem stored_apart {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (cRegion w16 p).Disjoint r) {L : List Zq} (hL : L.length ≤ 256) (h : Stored w16 m p L) :
    Stored w16 m' p L :=
  fun k hk => by
    rw [← h k hk, coeffAtW_eq, coeffAtW_eq, hf.readW (cAddr_contains w16 p (by omega)) hd
      (by have := cw_bytes_le w16; omega)]

section
variable {σ : State} (hp : PreW w16 σ)
include hp

omit hp in
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (cRegion w16 (poly4W w16 (aP σ) K)) (aRW w16 σ) :=
  Offset.sub_base _ (by wd_omega)

/-- Polynomial `K` is apart from the scratch space. -/
theorem scr_poly {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ 8192) :
    Region.Disjoint ⟨at' σ a, n⟩ (cRegion w16 (poly4W w16 (aP σ) K)) :=
  (hp.a_scr.symm.sub_left (sub_scr h)).sub_right (sub_poly hK)

/-- `Env` after writes to polynomial `K`. -/
theorem EnvW.poly {K : Nat} (hK : K < 4) {s s' : State} (he : EnvW w16 σ s)
    (hf : Frame [cRegion w16 (poly4W w16 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvW w16 σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub fun r hr => ?_)⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using scr_poly hp hK (a := oSave + 8 * i) (n := 8) (by simp only [oSave]; omega)) (by decide)]
    exact he.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨aRW w16 σ, by simp, sub_poly hK⟩

/-- Writes to polynomial `K` keep `LB`. -/
theorem LBW.poly {s₀ : State} {K b : Nat} (hK : K < 4) {s s' : State} (h : LBW w16 σ s₀ K b s)
    (hf : Frame [cRegion w16 (poly4W w16 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r) : LBW w16 σ s₀ K b s' :=
  ⟨EnvW.poly hp hK h.env hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hg .r14 (by simp), h.r14],
    tab_frame (by simpa using scr_poly hp hK (a := oTab) (n := 2240) (by simp only [oTab]; omega)) hf h.tab,
    fun p hp' hb => by
      rw [byte_frame hf (R := ⟨at' σ (oBuf + 504 * K + p), 1⟩)
        (by simpa using scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact h.out p hp' hb,
    h.fr.trans hf⟩

omit hp in
/-- `LB` after code that writes no memory and keeps its registers. -/
theorem LBW.keep {s₀ : State} {K b : Nat} {s s' : State} (h : LBW w16 σ s₀ K b s) (hm : s'.mem = s.mem) {rs : List Reg}
    (k : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs := by decide) :
    LBW w16 σ s₀ K b s' :=
  ⟨h.env.keep hm k fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [k.gpr (hrs .r14 (by simp)), h.r14], by rw [hm]; exact h.tab, by rw [hm]; exact h.out,
    by rw [hm]; exact h.fr⟩

omit hp in
theorem LAtW.same {s₀ : State} {K b t : Nat} {s s' : State} (h : LAtW w16 σ s₀ K b t s) (g : s'.gpr = s.gpr)
    (m : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : LAtW w16 σ s₀ K b t s' :=
  ⟨h.lb.keep m (rs := []) ⟨fun r _ => by rw [g], rd, wr⟩ (by simp), by rw [g]; exact h.rsi,
    by rw [g]; exact h.rdi, by rw [g]; exact h.rbp, by rw [m]; exact h.stored⟩

omit hp in
theorem LAtW.same' {s₀ : State} {K b t : Nat} {s s' : State} (h : LAtW w16 σ s₀ K b t s) (m : s'.mem = s.mem)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs := by decide)
    (hrs' : Reg.rsi ∉ rs ∧ Reg.rdi ∉ rs ∧ Reg.rbp ∉ rs := by decide) : LAtW w16 σ s₀ K b t s' :=
  ⟨h.lb.keep m k hrs, by rw [k.gpr hrs'.1]; exact h.rsi, by rw [k.gpr hrs'.2.1]; exact h.rdi,
    by rw [k.gpr hrs'.2.2]; exact h.rbp, by rw [m]; exact h.stored⟩

omit hp in
theorem out_byte {s₀ : State} {K b t : Nat} {s : State} (h : LAtW w16 σ s₀ K b t s) {j : Nat} (hj : 3 * t + j < 504)
    (hj' : 3 * (b + t) + j < 840) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = xofByte (B σ K) (3 * (b + t) + j) := by
  have e := h.lb.out (3 * t + j) hj (by omega)
  rw [at'] at e
  rw [h.rsi, at', Offset.add_add, Offset.add_add, e]
  exact congrArg _ (by omega)

theorem lat_regions {s₀ : State} {K b t : Nat} (hK : K < 4) {s : State} (h : LAtW w16 σ s₀ K b t s) {j : Nat}
    (hj : 3 * t + j < 504) : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [h.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp h.lb.env.rd h.lb.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem lat_step {s₀ : State} {K b t : Nat} (hK : K < 4) (ht : t < 168) (hbt : b + t < 280) {s : State}
    (h : LAtW w16 σ s₀ K b t s) :
    WP isa (snBody w16) s fun s' => LAtW w16 σ s₀ K b (t + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hL : (Lt σ K (b + t)).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ (b + t)
  have hw : WrA w16 s.wr (poly4W w16 (aP σ) K) := fun j hj => by
    rw [h.lb.env.wr, hp.wr]
    refine ⟨aRW w16 σ, by simp, ?_⟩
    rw [cAddr, poly4W, Offset.add_add]
    exact Offset.contains_base _ (by wd_omega) (by wd_omega)
  refine WP.mono (snBody_ok w16 s (aP := poly4W w16 (aP σ) K) h.rbp h.rdi hL hw h.stored
    (by simpa using lat_regions hp hK h (j := 0) (by omega)) (lat_regions hp hK h (by omega))
    (lat_regions hp hK h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := out_byte h (j := 0) (by omega) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  rw [e0, out_byte h (j := 1) (by omega) (by omega), out_byte h (j := 2) (by omega) (by omega),
    ← sampleAfter_succ] at hdi hst
  refine ⟨⟨h.lb.poly hp hK hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, h.rsi, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, Offset.add_add, Nat.mul_succ], hdi,
    by rw [hk.gpr (by decide), h.rbp], hst⟩, hcx, hz⟩

omit hp in
/-- `PC` after code that writes no memory and keeps its registers. -/
theorem PCW.keep {X : Mem → Prop} {K : Nat} {s s' : State} (h : PCW w16 X σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : PCW w16 X σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hm]; exact h.buf, by rw [hk.gpr (hrs .r14 (by simp)), h.r14],
    by rw [hm]; exact h.polys⟩

/-! ## The calls of `vg_mlkem_sample_ntt` -/

omit hp in
theorem okN_succ (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (okN σ K)).setWidth 32 &&&
    (if (sampleNTT minIterations (B σ K)).isSome then 1 else 0)) = BitVec.ofNat 64 (okN σ (K + 1)) := by
  simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range K).all fun k => (sampleNTT minIterations (B σ k)).isSome <;>
    cases (sampleNTT minIterations (B σ K)).isSome <;> rfl

/-- The seed at `seeds + 34 K`. -/
theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [aRW w16 σ, scrR σ, stkR σ] σ.mem m) :
    bytesAt m (sd σ + BitVec.ofNat 64 (34 * K)) 34 = B σ K := by
  rw [bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega)),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega)), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega)]
  simp only [oScalar]; omega

/-- The regions of `vg_mlkem_sample_ntt`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩]
abbrev cWrW (w16 : Bool) (σ : State) (K : Nat) : List Region := [cRegion w16 (poly4W w16 (aP σ) K), ⟨at' σ oScalar, 2048⟩]

/-- The same for 32-bit coefficients. -/
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (poly4 (aP σ) K), ⟨at' σ oScalar, 2048⟩]

omit hp in
theorem c_subW {K : Nat} (hK : K < 4) : ∀ r ∈ cWrW w16 σ K ++ [stkR σ],
    (∃ R ∈ [aRW w16 σ, scrR σ, stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨aRW w16 σ, by simp, sub_poly hK⟩
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disjW {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ cWrW w16 σ K ++ [stkR σ], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (sub_scr (by simp only [oScalar] at h; omega))).sub_right (sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega) (by simp only [oScalar]; omega)
  · exact (hp.stk_scr.sub_right (sub_scr (by simp only [oScalar] at h; omega))).symm

/-- `PC` after the call. -/
theorem PCW.call {X : Mem → Prop} {K : Nat} (hK : K < 4) {s s' : State} (h : PCW w16 X σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (cWrW w16 σ K ++ [stkR σ]) s.mem s'.mem)
    (hX : ∀ m m', Frame (cWrW w16 σ K ++ [stkR σ]) m m' → X m → X m') : PCW w16 X σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (c_subW (σ := σ) hK))⟩,
    ?_, by rw [hg .r14 (by simp), h.r14], fun k hk f e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disjW hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · exact hX _ _ hf h.buf
  · refine polyIsW_frame w16 hf (fun r hr => ?_) (h.polys k hk f e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact Offset.disjoint (aP σ) (d := pBytes w16 * k) (n := 256 * (cw w16 / 8)) (e := pBytes w16 * K)
        (k := 256 * (cw w16 / 8)) (by wd_omega) (by wd_omega) (by wd_omega)
    · exact (hp.a_scr.sub_left (sub_poly (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (sub_poly (by omega))).symm

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

theorem regs {s : State} (he : EnvW w16 σ s) : s.rd ++ s.wr = [sdR σ, aRW w16 σ, scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : EnvW w16 σ s) {K : Nat} (hK : K < 4) :
    Covers (cRd σ K ++ cWrW w16 σ K) (s.rd ++ s.wr) ∧ Covers (cWrW w16 σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sdR σ, by simp, 34 * K, rfl, by simp only; omega⟩
    · exact ⟨aRW w16 σ, by simp, pBytes w16 * K, rfl, by simp only; wd_omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨aRW w16 σ, by simp, pBytes w16 * K, rfl, by simp only; wd_omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩

omit hp in
theorem sx34 {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (34 * K)) = BitVec.ofNat 64 (34 * K) :=
  sx_ofNat (by omega)

omit hp in
theorem sx1024 {K : Nat} (hK : K < 4) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) = BitVec.ofNat 64 (1024 * K) := sx_ofNat (by omega)

omit hp in
theorem sxP {K : Nat} (hK : K < 4) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (pBytes w16 * K)) = BitVec.ofNat 64 (pBytes w16 * K) := sx_ofNat (by wd_omega)

omit hp in
theorem and14_ok (s : State) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s fun s' =>
      (s'.gpr .r14 = BitVec.setWidth 64 ((s.gpr .r14).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r14] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- The arguments of the call of `vg_mlkem_sample_ntt` on seed `K`. -/
structure ArgIW (w16 : Bool) (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PCW w16 X σ K s
  rdi : s.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K)
  rsi : s.gpr .rsi = poly4W w16 (aP σ) K
  rdx : s.gpr .rdx = at' σ oScalar

/-- `ArgIW` with 32-bit coefficients. -/
abbrev ArgI := ArgIW false

omit hp in
theorem argsK_ok {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : PCW w16 X σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (pBytes w16 * K))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) s (ArgIW w16 X σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = poly4W w16 (aP σ) K ∧ s'.gpr .rdx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, sx34 hK, sxP hK, sx6144]; rfl) rfl)
    fun _ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ⟨h.keep hm₂ k₂ (by decide), hdi, hsi, hdx⟩

theorem argK_kS {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : ArgIW w16 X σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 34 * K) (n := 34) (by omega))

theorem argK_pre {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : ArgIW w16 X σ K s) :
    (sampleKW w16).pre (s.callEntry.withRegions (cRd σ K) (cWrW w16 σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (cRegion w16 (poly4W w16 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [sampleKW, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    scr6144_lt hp⟩

/-- After the call of `vg_mlkem_sample_ntt` on seed `K`. -/
structure CallIW (w16 : Bool) (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  pinv : PCW w16 X σ K s
  rax : (s.gpr .rax).setWidth 32 = if (sampleNTT minIterations (B σ K)).isSome then 1 else 0
  poly : ∀ f, sampleNTT minIterations (B σ K) = some f → PolyIsW (cw w16) s.mem (poly4W w16 (aP σ) K) f

/-- `CallIW` with 32-bit coefficients. -/
abbrev CallI := CallIW false

theorem callK_ok {X : Mem → Prop} {K : Nat} (hK : K < 4)
    (hX : ∀ m m', Frame (cWrW w16 σ K ++ [stkR σ]) m m' → X m → X m') {s : State} (h : ArgIW w16 X σ K s) :
    WP isa (.call (if w16 then "vg_mlkem16_sample_ntt" else "vg_mlkem_sample_ntt") (sampleNTTW w16)) s
      (CallIW w16 X σ K) := by
  have hcv := cov hp h.pinv.env hK
  refine WP.call (sampleW_correct w16) (sampleW_nosp w16) (by rw [sampleW_depth]; decide) (argK_pre hp hK h)
    hcv.1 hcv.2 fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_
  rw [sampleW_depth, h.pinv.env.rsp] at hf
  have h₃ : PCW w16 X σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf hX
  simp only [sampleKW, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rsi, hm₃, ce_bytesAt24 s (n := 34) (by decide) (argK_kS hp hK h),
    seed_bytes hp hK h.pinv.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  exact ⟨h₃, hpost.1, hpost.2⟩

omit hp in
theorem andK_ok {X : Mem → Prop} {K : Nat} {s : State} (h : CallIW w16 X σ K s) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s (PCW w16 X σ (K + 1)) := by
  refine WP.mono (and14_ok s) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  have h₃ := h.pinv
  refine ⟨⟨k₄.2.1.trans h₃.env.rd, k₄.2.2.trans h₃.env.wr, by rw [k₄.gpr (by decide), h₃.env.rbx],
      by rw [k₄.gpr (by decide), h₃.env.r12], by rw [k₄.gpr (by decide), h₃.env.r13],
      by rw [k₄.gpr (by decide), h₃.env.rsp], by rw [k₄.gpr (by decide), h₃.env.r15],
      by rw [hm₄]; exact h₃.env.saved, by rw [hm₄]; exact h₃.env.frame⟩,
    by rw [hm₄]; exact h₃.buf, by rw [h14, h₃.r14, h.rax, okN_succ], fun k hk f e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact h.poly f e
  · exact h₃.polys k (by omega) f e

end

section
variable {σ : State}

/-- `c_subW` for 32-bit coefficients. -/
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ cWr σ K ++ [stkR σ],
    (∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨aR σ, by simp, sub_poly (w16 := false) hK⟩
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨stkR σ, by simp, fun _ h => h⟩

/-- `c_disjW` for 32-bit coefficients. -/
theorem c_disj (hp : Pre σ) {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ cWr σ K ++ [stkR σ], Region.Disjoint ⟨at' σ a, n⟩ r :=
  fun r hr => c_disjW (w16 := false) hp hK h r (by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (rfl | rfl) | rfl
    exacts [.inl (.inl rfl), .inl (.inr rfl), .inr rfl])

end

end VG.Proof.MlKem.X86_64.S4
