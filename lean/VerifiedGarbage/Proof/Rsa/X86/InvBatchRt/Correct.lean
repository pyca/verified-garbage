module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Rows
public import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrectDef
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq

/-! # The inverse's corrections at a run-time width

`normalize_ok`: the coefficient negated modulo `p` where `f` is negative (`InvBatch.normalize_ok`);
`doubleLoop_ok`: doubled `K` times modulo `p` (`InvBatch.doubleLoop_ok`); `finish_ok`: `|f|` and the
coefficient into the outputs, zero-padded to `w` words (`InvBatch.finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-! ## The arithmetic -/

def normal (p a : Nat) (f : Int) : Nat := if f < 0 then (p - a) % p else a

def doubled (p a k : Nat) : Nat := (a * 2 ^ k) % p

theorem doubled_zero {p a : Nat} (ha : a < p) : doubled p a 0 = a := by
  simp only [doubled, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt ha]

theorem doubled_next (p a k : Nat) : (2 * doubled p a k) % p = doubled p a (k + 1) := by
  rw [doubled, doubled, Nat.mul_mod_mod, Nat.pow_succ, Nat.mul_comm 2 (a * 2 ^ k), Nat.mul_assoc]

theorem normal_range {p a : Nat} (f : Int) (hp : 0 < p) (ha : a < p) : normal p a f < p := by
  unfold normal
  split
  · exact Nat.mod_lt _ hp
  · exact ha

theorem normal_cast {p a : Nat} (f : Int) (ha : a < p) :
    (normal p a f : Int) = (if f < 0 then -(a : Int) else (a : Int)) % p := by
  unfold normal
  split
  · rw [Int.natCast_emod, Int.ofNat_sub (by omega)]
    exact Int.neg_emod_eq_sub_emod.symm
  · exact (Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha)).symm

theorem correction_eq {p a n : Nat} {st : Divstep.W32.IState} (ha : a < p) (sa : st.a = (a : Int)) :
    doubled p (normal p a st.f) (6 * (n + 1)) = (VG.Proof.Rsa.Divstep.corrected p st (3 * (n + 1))).toNat := by
  apply Int.ofNat_inj.mp
  rw [doubled, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, normal_cast _ ha]
  unfold VG.Proof.Rsa.Divstep.corrected
  rw [sa]
  have exp : 2 * (3 * (n + 1)) = 6 * (n + 1) := by omega
  rw [exp, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  exact ((Int.mod_modEq _ _).mul_right _).eq

/-! ## The code -/

theorem rv_half1' (len j : Nat) : rv (kw len) { arr := j, half := 1 } = rv (kw len) (a j) + 4 * nw len := by
  have := rv_half1 (kw len) (a j) rfl
  have ke := kw_eq len
  simp only [a] at this ⊢; omega

/-- `normalize`: `[6] = normal p a f` (`InvBatch.normalize_ok`). -/
theorem normalize_ok {s : State} (h : Bx L s B Z len N) {p a₀ : Nat} {f : Int}
    (hm : val32 s.mem B (rv (kw len) mo) (nw len) = p) (ha : val32 s.mem B (rv (kw len) (a 6)) (nw len) = a₀)
    (top : w32 s.mem B (rv (kw len) (a 6) + 4 * nw len) = 0) (small : a₀ < p)
    (sign : (2 ^ 31 ≤ w32 s.mem B (rv (kw len) (a 4) + 4 * nw len)) ↔ f < 0) :
    WP isa (normalize L) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) (a 6)) (nw len) = normal p a₀ f ∧
      w32 z.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 ∧ Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 6), 4 * nw len), (rv (kw len) (a 12), 4 * nw len)] s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r2 := rv_a len 2; have r4 := rv_a len 4; have r6 := rv_a len 6; have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rtmp : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have h41 := rv_half1' len 4
  have pn : p < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
  unfold normalize
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- `[12] = p - a`.
  refine WP.seq (WP.mono (copy_ok h (o := a 12) (a := a 2) (e := 0) (by decide) (by omega) (by omega)
    (by omega)) fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  simp only [Nat.add_zero] at O₁ V₁
  rw [← rmo, hm] at V₁
  refine WP.seq (WP.mono (chainSub_ok H₁ (o := a 12) (a := a 12) (b := a 6) (e := 0) (by decide) rfl
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₂ ⟨H₂, O₂, ⟨c, _, V₂⟩, K₂⟩ => ?_)
  simp only [Nat.add_zero] at O₂ V₂
  rw [V₁, O₁.val32 (by omega) (by omega), ha] at V₂
  have value2 : val32 s₂.mem B (rv (kw len) (a 12)) (nw len) = p - a₀ := by
    have bound := val32_lt s₂.mem B (rv (kw len) (a 12)) (nw len)
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at V₂ <;>
      omega
  -- The sign of `f`, then the selection.
  refine WP.seq (maskAt_ok H₂ (x := { arr := 4, half := 1 }) (by omega) fun s₃ K₃ m₃ c₃ => WP.block_nil ?_)
  rw [h41, O₂.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega)] at c₃
  have H₃ : Bx L s₃ B Z len N := H₂.keep K₃ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₃]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine WP.seq (WP.mono (selIn_ok H₃ (o := a 6) (a := a 12) (e := 0) (k := decide (f < 0))
    (by rw [c₃]; simp only [cmask, decide_eq_true_eq]; exact if_congr sign rfl rfl) (by decide) (by omega) (by omega) (by omega))
    fun s₄ ⟨H₄, O₄, V₄, K₄⟩ => ?_)
  simp only [Nat.add_zero] at O₄ V₄
  rw [m₃, value2, O₂.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega), ha] at V₄
  have top4 : w32 s₄.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 := by
    rw [O₄.w32 (by omega) (by omega), m₃, O₂.w32 (by omega) (by omega), O₁.w32 (by omega) (by omega), top]
  have full4 : val32 s₄.mem B (rv (kw len) (a 6)) (nw len + 1) = if f < 0 then p - a₀ else a₀ := by
    rw [val32_succ, V₄, top4, Nat.mul_zero, Nat.add_zero]
    by_cases hf : f < 0 <;> simp [hf]
  have mod4 : val32 s₄.mem B (rv (kw len) mo) (nw len) = p := by
    rw [O₄.val32 (by omega) (by omega), m₃, O₂.val32 (by omega) (by omega), O₁.val32 (by omega) (by omega), hm]
  refine WP.mono (csub_ok H₄ (src := a 6) (o := a 6) rfl rfl (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun hne => absurd rfl hne) (by omega) mod4 (by rw [full4]; split <;> omega))
    fun z ⟨Hz, U₅, V₅, K₅⟩ => ?_
  refine ⟨Hz, ?_, ?_, ?_, ?_⟩
  · rw [V₅, full4]
    unfold normal
    split
    · rfl
    · exact Nat.mod_eq_of_lt small
  · rw [VG.Proof.Weierstrass.X86.Inv.word_unch U₅ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega), top4]
  · exact ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))
  · intro x hx
    have hA := hx (rv (kw len) (a 6), 4 * nw len) (by simp)
    have hU := hx (rv (kw len) (a 12), 4 * nw len) (by simp)
    rw [U₅ x (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hU
      · exact hA), O₄ x hA, m₃, O₂ x hU, O₁ x hU]

/-- `twice`: `[6] = 2 a mod p` (`InvBatch.twice_ok`). -/
theorem twice_ok {s : State} (h : Bx L s B Z len N) {p a₀ : Nat}
    (hm : val32 s.mem B (rv (kw len) mo) (nw len) = p) (ha : val32 s.mem B (rv (kw len) (a 6)) (nw len) = a₀)
    (top : w32 s.mem B (rv (kw len) (a 6) + 4 * nw len) = 0) (small : a₀ < p) :
    WP isa (twice L) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) (a 6)) (nw len) = (2 * a₀) % p ∧
      w32 z.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s z ∧
      Unch B [(rv (kw len) (a 6), 4 * (nw len + 1)), (rv (kw len) (a 12), 4 * nw len)] s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r2 := rv_a len 2; have r6 := rv_a len 6; have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have h61 := rv_half1' len 6
  have rtmp : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have pn : p < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
  have full : val32 s.mem B (rv (kw len) (a 6)) (nw len + 1) = a₀ := by
    rw [val32_succ, ha, top, Nat.mul_zero, Nat.add_zero]
  unfold twice
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (chainAdd_ok h (o := a 6) (a := a 6) (b := a 6) (e := 1) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _)))
    fun s₁ ⟨H₁, O₁, ⟨c, _, V₁⟩, K₁⟩ => ?_)
  rw [full] at V₁
  have total : 2 * a₀ < 2 ^ (32 * (nw len + 1)) := by rw [pow32_succ]; omega
  have value1 : val32 s₁.mem B (rv (kw len) (a 6)) (nw len + 1) = 2 * a₀ := by
    cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at V₁ <;>
      omega
  have mod1 : val32 s₁.mem B (rv (kw len) mo) (nw len) = p := by rw [O₁.val32 (by omega) (by omega), hm]
  refine WP.seq (WP.mono (csub_ok H₁ (src := a 6) (o := a 6) rfl rfl (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun hne => absurd rfl hne) (by omega) mod1 (by rw [value1]; omega))
    fun s₂ ⟨H₂, U₂, V₂, K₂⟩ => ?_)
  refine zeroWord_ok H₂ (x := { arr := 6, half := 1 }) (by omega) fun z Hz K₃ O₃ z₃ => WP.block_nil ?_
  rw [h61] at O₃ z₃
  refine ⟨Hz, ?_, z₃, ((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide)), ?_⟩
  · rw [O₃.val32 (by omega) (by omega), V₂, value1]
  · intro x hx
    have hA := hx (rv (kw len) (a 6), 4 * (nw len + 1)) (by simp)
    have hU := hx (rv (kw len) (a 12), 4 * nw len) (by simp)
    rw [O₃ x (by omega), U₂ x (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hU
      · simp only; omega), O₁ x hA]

/-- After `k` doublings. -/
def DoubleAt (L : Lay) (B : Addr) (Z len N p a₀ K : Nat) (s₀ : State) (k : Nat) (s : State) : Prop :=
  Bx L s B Z len N ∧ val32 s.mem B (rv (kw len) (a 6)) (nw len) = doubled p a₀ k ∧
  w32 s.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 ∧ val32 s.mem B (rv (kw len) mo) (nw len) = p ∧
  s.gpr .esi = BitVec.ofNat 32 (K - k) ∧ Keeps wordClob s₀ s ∧
  Unch B [(rv (kw len) (a 6), 4 * (nw len + 1)), (rv (kw len) (a 12), 4 * nw len)] s₀.mem s.mem

/-- `K` doublings (`InvBatch.doubleLoop_ok`). -/
theorem doubleLoop_ok {s : State} (h : Bx L s B Z len N) {p a₀ K : Nat}
    (hm : val32 s.mem B (rv (kw len) mo) (nw len) = p) (ha : val32 s.mem B (rv (kw len) (a 6)) (nw len) = a₀)
    (top : w32 s.mem B (rv (kw len) (a 6) + 4 * nw len) = 0) (hp : 0 < p) (small : a₀ < p)
    (kp : 0 < K) (kl : K < 2 ^ 32) (counter : s.gpr .esi = BitVec.ofNat 32 K) :
    WP isa (.loop (.seq (twice L) (.block [decCounter, testCounter])) .ne) s (DoubleAt L B Z len N p a₀ K s K) := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have r2 := rv_a len 2; have r6 := rv_a len 6; have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have start : DoubleAt L B Z len N p a₀ K s 0 s :=
    ⟨h, by rw [doubled_zero small, ha], top, hm, by simpa only [Nat.sub_zero] using counter, Keeps.refl _ _,
      Unch.refl _ _ _⟩
  refine WP.loop (M := isa) (fun remaining u => ∃ k, k + remaining = K ∧ 0 < remaining ∧
    DoubleAt L B Z len N p a₀ K s k u) ?_ K s ⟨0, by omega, kp, start⟩
  intro remaining u ⟨k, total, pos, Hu, va, ta, ma, cu, ku, ou⟩
  refine WP.seq (WP.mono (twice_ok Hu ma va ta (Nat.mod_lt _ hp)) fun v ⟨Hv, vv, tv, kv, ov⟩ => ?_)
  have cv : v.gpr .esi = BitVec.ofNat 32 (K - k) := (kv.1 .esi (by decide)).trans cu
  refine VG.Proof.Weierstrass.X86.wp_decCounter (by omega) cv fun v₁ cv₁ kv₁ mv₁ => ?_
  refine VG.Proof.Weierstrass.X86.wp_testCounter (by omega) cv₁ fun z F zf => WP.block_nil ?_
  have kz : Keeps wordClob u z := ((kv.mono (by decide)).trans (kv₁.mono (by decide))).trans (F.keeps _)
  have mz : z.mem = v.mem := F.mem.trans mv₁
  have Kvz : Keeps [.esi] v z := (kv₁.mono (by decide)).trans (F.keeps _)
  have Hz : Bx L z B Z len N := Hv.keep Kvz (by decide) (by decide) (o := 160) (c := 0)
    (by rw [mz]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have vz : val32 z.mem B (rv (kw len) (a 6)) (nw len) = doubled p a₀ (k + 1) := by rw [mz, vv, doubled_next]
  have tz : w32 z.mem B (rv (kw len) (a 6) + 4 * nw len) = 0 := by rw [mz, tv]
  have modz : val32 z.mem B (rv (kw len) mo) (nw len) = p := by
    rw [mz, Outs.val32 ov (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega), ma]
  have cz : z.gpr .esi = BitVec.ofNat 32 (K - (k + 1)) := by rw [F.gpr, cv₁]; congr 1
  have oz : Unch B [(rv (kw len) (a 6), 4 * (nw len + 1)), (rv (kw len) (a 12), 4 * nw len)] s.mem z.mem := by
    rw [mz]
    exact fun y hy => (ov y hy).trans (ou y hy)
  have next : DoubleAt L B Z len N p a₀ K s (k + 1) z := ⟨Hz, vz, tz, modz, cz, ku.trans kz, oz⟩
  by_cases last : k + 1 = K
  · left
    refine ⟨?_, by simpa only [last] using next⟩
    change z.zf.map (!·) = some false
    rw [zf]
    have zero : K - k - 1 = 0 := by omega
    simp only [zero, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, remaining - 1, by omega, k + 1, by omega, by omega, next⟩
    change z.zf.map (!·) = some true
    rw [zf]
    have nz : K - k - 1 ≠ 0 := by omega
    simp only [nz, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Rsa.X86.InvBatchRt
