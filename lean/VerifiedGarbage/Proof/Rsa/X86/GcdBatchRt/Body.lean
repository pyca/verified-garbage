module

public import VerifiedGarbage.Proof.Divstep.Steps
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Encoding
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Tc32
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum.Abs
public import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Init
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.State
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Batch
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Shr

-- separate module: its proofs cost more than its imports; `BatchInstance` binds it, as it binds
-- `InvBatchRt.Body`
/-! # The batched GCD of prime recovery

`update_ok`: both rows of the matrix, `f` and `g` replaced; `batch_ok`: the window's thirty
divsteps, the update and the count down by one, which take the state `I` to `divsteps 30 I`;
`loop_ok`: the counted batches; `finish_ok`: `|f|` into narrow array 1 and array 5 zeroed;
`body_ok`: `gcd(m, x)` for `m` odd, from narrow arrays 8 and 0, `w = n - 1` words each.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.Divstep (oddInput)
open VG.Proof.Divstep (divsteps)
open VG.Proof.Weierstrass.X86.Inv (read32_unch)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem seq_assoc' {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  exact WP.seq_iff.mpr (WP.mono h fun _ hu => WP.seq_iff.mpr hu)

/-- The arrays the update writes. -/
def arrWrites (len : Nat) : List (Nat × Nat) :=
  [(rv (kw len) (a 0), 6 * (8 * nw len + 8)), (rv (kw len) (a 11), 2 * (8 * nw len + 8))]

/-- The update: `f = (u f + v g) / 2 ^ 30` and `g = (q f + r g) / 2 ^ 30`. -/
theorem update_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {T : Divstep.MSt} {f g : Int} {p : Nat} (hm : MatrixAt B T s)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * nw len + 1))
    (divF : 2 ^ 30 ∣ T.u * f + T.v * g) (divG : 2 ^ 30 ∣ T.q * f + T.r * g) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.update L) s fun z => Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.u * f + T.v * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      (val32 z.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((T.q * f + T.r * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s z ∧ Unch B (arrWrites len) s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11
  have r12 := rv_a len 12
  have e16 : win = 16 := rfl
  unfold VG.Impl.Rsa.X86.GcdBatchRt.update
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- The first row, into `[0]`.
  refine seq_assoc' (WP.seq (WP.mono (fgRowO_ok h hodd h3 (j := 0) (by decide) (by decide) (by decide)
    hm.u hm.v huv hf hg hfb hgb hp divF) fun s₁ ⟨H₁, F₁, K₁, U₁⟩ => ?_))
  have apart₁ : ∀ d, (d + 4 ≤ rv (kw len) (a 0) ∨ rv (kw len) (a 0) + 4 * (nw len + 1) ≤ d) →
      d + 4 ≤ rv (kw len) (a 11) → s₁.mem.readW (off B d) 32 = s.mem.readW (off B d) 32 :=
    fun d h₁ h₂ => read32_unch U₁ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  have val₁ : ∀ d k, rv (kw len) (a 0) + 4 * (nw len + 1) ≤ d → d + 4 * k ≤ rv (kw len) (a 11) →
      val32 s₁.mem B d k = val32 s.mem B d k :=
    fun d k h₁ h₂ => Outs.val32 U₁ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  -- The second, into `[5]`.
  refine seq_assoc' (WP.seq (WP.mono (fgRowO_ok H₁ hodd h3 (j := 5) (by decide) (by decide) (by decide)
    (by rw [apart₁ _ (by omega) (by omega)]; exact hm.q) (by rw [apart₁ _ (by omega) (by omega)]; exact hm.r)
    hqr (by rw [val₁ _ _ (by omega) (by omega)]; exact hf) (by rw [val₁ _ _ (by omega) (by omega)]; exact hg)
    hfb hgb hp divG) fun s₂ ⟨H₂, G₂, K₂, U₂⟩ => ?_))
  have A₂ : val32 s₂.mem B (rv (kw len) (a 0)) (nw len + 1) = val32 s₁.mem B (rv (kw len) (a 0)) (nw len + 1) :=
    Outs.val32 U₂ (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega) (by omega)
  -- `[4] = [0]`.
  refine WP.mono (copy_ok H₂ (o := a 4) (a := a 0) (e := 1) (by decide) (by omega) (by omega) (by omega))
    fun z ⟨Hz, Oz, Vz, Kz⟩ => ⟨Hz, by rw [Vz, A₂]; exact F₁, ?_, ?_, ?_⟩
  · rw [Oz.val32 (by omega) (by omega)]; exact G₂
  · exact ((K₁.trans K₂).trans (Kz.mono (by decide)))
  · intro y hy
    have h0 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [arrWrites])
    have h11 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [arrWrites])
    simp only at h0 h11
    rw [Oz y (by omega), U₂ y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega), U₁ y (by
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega)]

/-- The loop body. -/
abbrev batchCode (L : Lay) : Prog isa :=
  VG.Impl.Rsa.X86.Keys.seqs [.block (start L), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, VG.Impl.Rsa.X86.GcdBatchRt.update L,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]

/-- A counted batch. -/
theorem batch_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {p j : Nat} {I : Int × Int × Int} (hI : GState len B I s) (hdb : |I.1| + 64 < 2 ^ 30) (hfo : I.2.1 % 2 = 1)
    (hfb : |I.2.1| ≤ p) (hgb : |I.2.2| ≤ p) (hp : p < 2 ^ (32 * nw len + 1))
    (jp : 1 ≤ j) (jl : j < 2 ^ 32) (counter : w32 s.mem B 100 = j) :
    WP isa (batchCode L) s fun z => Bx L z B Z len N ∧ GState len B (Divstep.divsteps 30 I) z ∧
      w32 z.mem B 100 = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have e16 : win = 16 := rfl
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11
  generalize hT : Divstep.msteps 30 (Divstep.MSt.init I.1 I.2.1 I.2.2) = T
  have mat := Divstep.msteps_mat (d := I.1) (g := I.2.2) hfo 30
  have bound := Divstep.msteps_bnd I.1 I.2.1 I.2.2 30
  rw [hT] at mat bound
  change 2 ^ 30 * T.f = T.u * I.2.1 + T.v * I.2.2 ∧ 2 ^ 30 * T.g = T.q * I.2.1 + T.r * I.2.2 at mat
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at bound
  have df : (T.d, T.f, T.g) = Divstep.divsteps 30 I := by
    have D := Divstep.msteps_dfg 30 (Divstep.MSt.init I.1 I.2.1 I.2.2)
    rw [hT] at D
    simpa only [Divstep.MSt.init, Prod.eta] using D
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine seq_assoc' (WP.seq (WP.mono (words_ok h hI.d hI.f hI.g hdb hfo) fun u ⟨Hu, M, K, O⟩ => ?_))
  rw [hT] at M
  refine WP.seq (WP.mono (update_ok Hu hodd h3 M (by rw [O.val32 (by omega) (by omega)]; exact hI.f)
    (by rw [O.val32 (by omega) (by omega)]; exact hI.g) bound.1 bound.2 hfb hgb hp
    ⟨T.f, mat.1.symm⟩ ⟨T.g, mat.2.symm⟩) fun v ⟨Hv, Fv, Gv, Kv, Ov⟩ => ?_)
  have cv : w32 v.mem B 100 = j := by
    rw [VG.Proof.Weierstrass.X86.Inv.word_unch Ov (by
      intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega),
      O.w32 (by omega) (by omega), counter]
  refine WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok Hv.ws.ws.workspace (d := 100) (by omega) jp jl cv)
    fun z ⟨c, zf, Kz, Oz⟩ => ?_
  refine ⟨Hv.keepHigh Kz (by decide) (by decide) Oz (by decide) (by omega), ?_, c, zf,
    (K.trans Kv).trans (Kz.mono (by decide)), ?_⟩
  · rw [← df]
    refine ⟨?_, ?_, ?_⟩
    · rw [read32_unch Oz.unch (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp only; omega)
        (by omega), read32_unch Ov (by
        intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)]
      exact M.d
    · rw [Oz.val32 (by omega) (by omega), Fv, ← mat.1, Int.mul_ediv_cancel_left _ (by decide)]
    · rw [Oz.val32 (by omega) (by omega), Gv, ← mat.2, Int.mul_ediv_cancel_left _ (by decide)]
  · intro x hx
    have h1 := hx (win, 88) (by simp [gcdWrites])
    have h2 := hx (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    have h3 := hx (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz x (by omega), Ov x (by
      intro r hr; simp only [arrWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega), O x (by omega)]


/-- What a batch needs of the state it starts from. -/
structure Facts (I : Int × Int × Int) (p : Nat) : Prop where
  delta : |I.1| + 64 < 2 ^ 30
  odd : I.2.1 % 2 = 1
  f : |I.2.1| ≤ p
  g : |I.2.2| ≤ p

theorem runFacts {n m x p i : Nat} (hn : n ≤ 1024) (hi : i < 3 * (n + 1))
    (hm : m % 2 = 1) (mp : m ≤ p) (xp : x ≤ p) :
    Facts (divsteps (30 * i) (1, m, x)) p := by
  have d := Divstep.W32.divsteps_d (1, m, x) (30 * i)
  have ho := Divstep.divsteps_odd (d := 1) (f := m) (g := x) (by decide) (by exact_mod_cast hm) (30 * i)
  have fg := Divstep.W32.divsteps_le (M := p) (d := 1) (f := m) (g := x) (by decide) (by exact_mod_cast hm)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (m : Int) ≤ p by exact_mod_cast mp))
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (x : Int) ≤ p by exact_mod_cast xp)) (30 * i)
  refine ⟨?_, ho.2, fg.1, fg.2⟩
  norm_num only [abs_one, Nat.cast_mul, Nat.cast_ofNat] at d
  omega

/-- The counted batches, `K` of them. -/
theorem loop_ok {s : State} (h : Bx L s B Z len N) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len)
    {p K : Nat} {m x : Int} (hK : 0 < K) (hK32 : K < 2 ^ 32) (hp : p < 2 ^ (32 * nw len + 1))
    (hI : GState len B (1, m, x) s) (hc : w32 s.mem B 100 = K)
    (facts : ∀ i < K, Facts (divsteps (30 * i) (1, m, x)) p) :
    WP isa (.loop (batchCode L) .ne) s fun z => Bx L z B Z len N ∧
      GState len B (divsteps (30 * K) (1, m, x)) z ∧ Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  let J := fun j u => Bx L u B Z len N ∧ GState len B (divsteps (30 * (K - j)) (1, m, x)) u ∧
    w32 u.mem B 100 = j ∧ Keeps wordClob s u ∧ Unch B (gcdWrites len) s.mem u.mem
  refine VG.Proof.Weierstrass.X86.countLoop_ok (Inv := J) (n := K) ?_ ?_ hK ?_
  · intro j u hj hjK ⟨Hu, Iu, Cu, Ku, Ou⟩
    have F := facts (K - j) (by omega)
    refine WP.mono (batch_ok Hu hodd h3 Iu F.delta F.odd F.f F.g hp hj (by omega) Cu)
      fun z ⟨Hz, Iz, Cz, Zz, Kz, Oz⟩ => ⟨⟨Hz, ?_, Cz, Ku.trans Kz, fun y hy => (Oz y hy).trans (Ou y hy)⟩, Zz⟩
    rw [show 30 * (K - (j - 1)) = 30 * (K - j) + 30 by omega, Divstep.divsteps_add]
    exact Iz
  · intro u ⟨Hu, Iu, _, Ku, Ou⟩
    exact ⟨Hu, by simpa only [Nat.sub_zero] using Iu, Ku, Ou⟩
  · exact ⟨h, by simpa only [Nat.sub_self, Nat.mul_zero, divsteps] using hI, hc, Keeps.refl _ _,
      Unch.refl _ _ _⟩

/-- What `finish` writes. -/
def finishWrites (len : Nat) : List (Nat × Nat) :=
  [(rv (kw len) (a 12), 4 * nw len), (rv (kw len) res, 4 * nw len), (rv (kw len) (a 5), 4 * nw len)]

/-- `finish`: `|f|` into `res` and `[5] = 0`, `n` words each. -/
theorem finish_ok {s : State} (h : Bx L s B Z len N) {f : Int}
    (hb : |f| < 2 ^ (32 * nw len))
    (hc : (val32 s.mem B (rv (kw len) (a 4)) (nw len) : Int) % (2 ^ (32 * nw len) : Int) =
      f % (2 ^ (32 * nw len) : Int))
    (sign : (2 ^ 31 ≤ w32 s.mem B (rv (kw len) (a 4) + 4 * nw len)) ↔ f < 0) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.finish L) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) res) (nw len) = f.natAbs ∧
      val32 z.mem B (rv (kw len) (a 5)) (nw len) = 0 ∧ Keeps wordClob s z ∧
      Unch B (finishWrites len) s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  have rr := rv_res len
  have h41 := rv_half1' len 4
  unfold VG.Impl.Rsa.X86.GcdBatchRt.finish
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- `[12] = 0`, then `-[4]`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok h (o := a 12) (countN0 h) (by omega) (by omega))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (chainSub_ok H₁ (o := a 12) (a := a 12) (b := a 4) (e := 0) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega)) fun s₂ ⟨H₂, O₂, ⟨c, _, V₂⟩, K₂⟩ => ?_)
  simp only [Nat.add_zero] at O₂ V₂
  rw [V₁, Nat.zero_add, O₁.val32 (by omega) (by omega)] at V₂
  -- The selection of `[4]` where `f` is not negative.
  refine WP.seq (maskAt_ok H₂ (x := { arr := 4, half := 1 }) (by omega) fun s₃ K₃ m₃ c₃ => ?_)
  rw [h41, O₂.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega)] at c₃
  refine wp_logicS (.inr rfl) rfl fun s₄ U₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .ebx, .ecx, .edx] s₂ s₄ := K₃.trans (U₄.keeps.mono (by decide))
  have m₄ : s₄.mem = s₂.mem := by rw [U₄.mem, m₃]
  have H₄ : Bx L s₄ B Z len N := H₂.keep K₄ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₄]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have mask : s₄.gpr .ecx = cmask (!decide (f < 0)) := by
    rw [U₄.gpr, ite_eq_right (by decide), c₃]
    simp only [cmask]
    by_cases hf : f < 0
    · rw [ite_eq_left (sign.mpr hf)]; simp only [hf, decide_true, Bool.not_true]; decide
    · rw [ite_eq_right (fun e => hf (sign.mp e))]; simp only [hf, decide_false, Bool.not_false]; decide
  refine WP.seq (WP.mono (selIn_ok H₄ (o := a 12) (a := a 4) (e := 0) mask (by decide) (by omega) (by omega)
    (by omega)) fun s₅ ⟨H₅, O₅, V₅, K₅⟩ => ?_)
  simp only [Nat.add_zero] at O₅ V₅
  rw [m₄, O₂.val32 (d := rv (kw len) (a 4)) (by omega) (by omega),
    O₁.val32 (d := rv (kw len) (a 4)) (by omega) (by omega)] at V₅
  have abs5 : val32 s₅.mem B (rv (kw len) (a 12)) (nw len) = f.natAbs := by
    rw [V₅]
    have := VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _) (by exact_mod_cast hc) ⟨c, V₂⟩
    rw [← this]
    by_cases hf : f < 0 <;> simp [hf]
  -- `res = [12]`, then `[5] = 0`.
  refine WP.seq (WP.mono (copy_ok H₅ (o := res) (a := a 12) (e := 0) (by decide) (by omega) (by omega)
    (by omega)) fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  simp only [Nat.add_zero] at O₆ V₆
  refine WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₆ (o := a 5) (countN0 H₆) (by omega) (by omega))
    fun z ⟨Hz, O₇, V₇, K₇⟩ => ⟨Hz, ?_, V₇, ?_, ?_⟩
  · rw [O₇.val32 (by omega) (by omega), V₆, abs5]
  · exact ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans ((K₆.mono (by decide)).trans (K₇.mono (by decide)))
  · intro x hx
    have h1 := hx (rv (kw len) (a 12), 4 * nw len) (by simp [finishWrites])
    have h2 := hx (rv (kw len) res, 4 * nw len) (by simp [finishWrites])
    have h3 := hx (rv (kw len) (a 5), 4 * nw len) (by simp [finishWrites])
    simp only at h1 h2 h3
    rw [O₇ x h3, O₆ x h2, O₅ x h1, m₄, O₂ x h1, O₁ x h1]

/-- The batched GCD: `gcd(m, x)` into `res` and `[5] = 0`, `n - 1` words each. -/
theorem body_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hodd : nw len % 2 = 1)
    (h3 : 3 ≤ nw len) (hmax : nw len ≤ 1024) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 4)) (nw len - 1) = m)
    (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len - 1) = x) (odd : m % 2 = 1) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body L) s fun z => Bx L z B Z len N ∧
      val32 z.mem B (rv (kw len) res) (nw len - 1) = Nat.gcd m x ∧
      val32 z.mem B (rv (kw len) (a 5)) (nw len - 1) = 0 ∧
      Keeps wordClob s z ∧ Unch B (gcdWrites len) s.mem z.mem := by
  have hn := h.ws.workspace.nowrap
  have mlt : m < 2 ^ (32 * (nw len - 1)) := hm ▸ val32_lt _ _ _ _
  have xlt : x < 2 ^ (32 * (nw len - 1)) := hx ▸ val32_lt _ _ _ _
  have up : 2 ^ (32 * (nw len - 1)) ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (by decide) (by omega)
  have mp : m < 2 ^ (32 * nw len) := by omega
  have xp : x < 2 ^ (32 * nw len) := by omega
  let y := oddInput m x
  let K := 3 * (nw len + 1)
  have done := VG.Proof.Rsa.Divstep.oddInput_done odd mp xp
  have yl := VG.Proof.Rsa.Divstep.oddInput_lt mp xp
  have hp : max m y < 2 ^ (32 * nw len + 1) := by
    have := Nat.two_pow_pos (32 * nw len); rw [Nat.pow_succ]; omega
  unfold VG.Impl.Rsa.X86.GcdBatchRt.body
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (init_ok h room h3 hm hx) fun s₁ ⟨H₁, I₁, C₁, K₁, O₁⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok H₁ hodd h3 (K := K) (by omega) (by omega) hp I₁ C₁
    (fun i hi => runFacts hmax hi odd (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    fun s₂ ⟨H₂, I₂, K₂, O₂⟩ => ?_)
  let f := (divsteps (30 * K) (1, (m : Int), (y : Int))).2.1
  have gl : Nat.gcd m x < 2 ^ (32 * (nw len - 1)) := (Nat.gcd_le_left x (by omega)).trans_lt mlt
  have absBound : |f| < (2 : Int) ^ (32 * nw len) := by
    have hNat : f.natAbs < 2 ^ (32 * nw len) := by rw [done.2]; omega
    have hInt : (f.natAbs : Int) < (2 : Int) ^ (32 * nw len) := by exact_mod_cast hNat
    simpa only [Int.natCast_natAbs] using hInt
  refine WP.mono (finish_ok H₂ absBound (VG.Proof.Rsa.X86.GcdBatch.encoding_low I₂.f)
    (VG.Proof.Rsa.X86.GcdBatch.encoding_sign I₂.f absBound)) fun z ⟨Hz, Gz, Zz, Kz, Oz⟩ => ?_
  have hf16 := Hz.fits16
  have r0 := rv_a len 0; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  have rr := rv_res len
  refine ⟨Hz, ?_, ?_, (K₁.trans K₂).trans Kz, ?_⟩
  · rw [show nw len = nw len - 1 + 1 by omega, done.2] at Gz
    exact (low_eq Gz gl).1
  · rw [show nw len = nw len - 1 + 1 by omega] at Zz
    exact (low_eq Zz (Nat.two_pow_pos _)).1
  · intro y hy
    have h1 := hy (win, 88) (by simp [gcdWrites])
    have h2 := hy (rv (kw len) (a 0), 6 * (8 * nw len + 8)) (by simp [gcdWrites])
    have h3 := hy (rv (kw len) (a 11), 2 * (8 * nw len + 8)) (by simp [gcdWrites])
    simp only at h1 h2 h3
    rw [Oz y (by
      intro w hw; simp only [finishWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega), O₂ y hy, O₁ y hy]

end VG.Proof.Rsa.X86.GcdBatchRt
