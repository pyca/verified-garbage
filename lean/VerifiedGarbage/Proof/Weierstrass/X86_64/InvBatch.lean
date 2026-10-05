import VerifiedGarbage.Proof.Weierstrass.X86_64.InvRed
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Inversion by divsteps on x86-64: a batch

The signed linear combinations of a batch as integers modulo the words'
range (`linM_ok`), the shift by 59 of a multiple of `2^59` (`shrM_ok`), and a
batch: `59` divsteps on the low words, then `f`, `g`, `a`, `b` updated by
their matrix, as `Divstep.batch` (`batch_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `[T] = u [x] + v [y]` modulo `2^(64 K)`, for words `u`, `v` (signed) in `w`, `w'`. -/
theorem linM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {T x y U k K : Nat} (hkK : k ≤ K) (hK : 2 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * k ≤ U)
    (hUy : U + 8 * (K - 1) ≤ y ∨ y + 8 * k ≤ U) :
    WP isa (.block (lin w w' T x y U k K)) s fun t =>
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  refine WP.mono (lin_ok hs hw hw' hkK hK hk' hx hy hT hU hTx hTy hUT hUx hUy) fun t ⟨e, kt, O⟩ => ⟨?_, kt, O⟩
  rw [masked_smask, masked_smask] at e
  have e' := congrArg (Nat.cast : Nat → Int) e
  push_cast at e'
  rw [← Divstep.toInt_sgn, ← Divstep.toInt_sgn]
  refine Divstep.lin_words (X' := wordsVal s.mem base x (K - 1)) (Y' := wordsVal s.mem base y (K - 1)) ?_ ?_ ?_
  · have := shifted_cong s.mem base x (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · have := shifted_cong s.mem base y (k := k) (K := K) (by omega) (by omega); push_cast at this; exact this
  · push_cast; convert e' using 3

/-- `[dst] = y / 2^59` modulo `2^(64 L)`, for `[src] ≡ y` with `|y| < 2^(64 L - 1)`
a multiple of `2^59`. -/
theorem shrM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) {y z : Int}
    (hy : (wordsVal s.mem base src L : Int) % ((2 ^ (64 * L) : Nat) : Int) = y % ((2 ^ (64 * L) : Nat) : Int))
    (hy1 : -((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int) ≤ y) (hy2 : y < ((2 ^ (64 * (L - 1)) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) = z % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  refine WP.mono (shr59_ok hs hL hsrc hdst hsep) fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy1 hy2 ⊢
  have hQ : 2 ^ (64 * (j + 1)) = 2 * (2 ^ (64 * j) * 2 ^ 63) := by
    rw [pow64_succ, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ring
  rw [sext, Nat.add_sub_cancel, sgnW_top, hQ] at e
  rw [hQ] at hy ⊢
  exact Divstep.shr_nat (c := 2 ^ 59) (B := 2 ^ 64) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := wordsVal_lt s.mem base src (j + 1); rw [hQ] at this; exact this) hy hy1 hy2 hz e

theorem modOk_out {M : Mod} {size p : Nat} {mem mem' : Mem} {base : Addr} (hM : ModOk M size p mem base)
    {W : List (Nat × Nat)} (hU : Unch base W mem mem') (hsep : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo)
    (hn : base.toNat + size ≤ 2 ^ 64) : ModOk M size p mem' base :=
  ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by rw [hU.wordsVal hsep (by have := hM.mo; omega)]; exact hM.val,
    hM.inv, hM.red⟩

/-- Apart from each range of a list written out. -/
local macro "apart" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq] <;> omega))

/-- Half a batch's update of `f`, `g`: `[dst] = (u f + v g) / 2^59` (`L` words, signed). -/
theorem fHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst L : Nat} (hL : 2 ≤ L) (hx : x + 8 * L ≤ size) (hy : y + 8 * L ≤ size) (hT : T + 8 * L ≤ size)
    (hU : U + 8 * (L - 1) ≤ size) (hd : dst + 8 * L ≤ size)
    (hTx : T + 8 * L ≤ x ∨ x + 8 * L ≤ T) (hTy : T + 8 * L ≤ y ∨ y + 8 * L ≤ T)
    (hUT : U + 8 * (L - 1) ≤ T ∨ T + 8 * L ≤ U) (hUx : U + 8 * (L - 1) ≤ x ∨ x + 8 * L ≤ U)
    (hUy : U + 8 * (L - 1) ≤ y ∨ y + 8 * L ≤ U) (hdT : dst + 8 * L ≤ T ∨ T + 8 * L ≤ dst) {p : Nat} {f g : Int}
    (hf : (wordsVal s.mem base x L : Int) % ((2 ^ (64 * L) : Nat) : Int) = f % ((2 ^ (64 * L) : Nat) : Int))
    (hg : (wordsVal s.mem base y L : Int) % ((2 ^ (64 * L) : Nat) : Int) = g % ((2 ^ (64 * L) : Nat) : Int))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (64 * (L - 1))) (hdiv : 2 ^ 59 ∣ u * f + v * g) :
    WP isa (.block (lin w w' T x y U L L ++ shr59 dst T L)) s fun t =>
      (wordsVal t.mem base dst L : Int) % ((2 ^ (64 * L) : Nat) : Int) =
        ((u * f + v * g) / 2 ^ 59) % ((2 ^ (64 * L) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * L), (U, 8 * (L - 1)), (dst, 8 * L)] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs hw hw' (k := L) (K := L) (Nat.le_refl _) hL (by omega) hx hy hT hU hTx hTy hUT hUx hUy)
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), Divstep.cong_comb hf hg] at e₁
  obtain ⟨b1, b2⟩ := Divstep.comb_range (A := 2 ^ (64 * (L - 1))) huv hfb hgb hp
  refine WP.mono (shrM_ok hs₁ (dst := dst) (src := T) (by omega) hT hd hdT e₁ b1 b2 (Int.mul_ediv_cancel' hdiv).symm)
    fun t ⟨e, k, O⟩ => ⟨e, k₁.trans (k.mono (by decide)), (O₁.trans O.unch).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]⟩

/-- Half a batch's update of `a`, `b`: `[dst] = mred (u a + v b)` (`n` words). -/
theorem abHalf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOk M size p s.mem base) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {u v : Int} (hu : s.gpr w = BitVec.ofInt 64 u) (hv : s.gpr w' = BitVec.ofInt 64 v) (huv : |u| + |v| ≤ 2 ^ 59)
    {T x y U dst : Nat} (hx : x + 8 * M.n ≤ size) (hy : y + 8 * M.n ≤ size) (hT : T + 8 * (M.n + 2) ≤ size)
    (hU : U + 8 * (M.n + 1) ≤ size) (hd : dst + 8 * M.n ≤ size)
    (hTx : T + 8 * (M.n + 2) ≤ x ∨ x + 8 * M.n ≤ T) (hTy : T + 8 * (M.n + 2) ≤ y ∨ y + 8 * M.n ≤ T)
    (hUT : U + 8 * (M.n + 1) ≤ T ∨ T + 8 * (M.n + 2) ≤ U) (hUx : U + 8 * (M.n + 1) ≤ x ∨ x + 8 * M.n ≤ U)
    (hUy : U + 8 * (M.n + 1) ≤ y ∨ y + 8 * M.n ≤ U) (hdT : dst + 8 * M.n ≤ T ∨ T + 8 * (M.n + 2) ≤ dst)
    (hTm : T + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ T) (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {a b : Int} (ha : (wordsVal s.mem base x M.n : Int) = a) (hb : (wordsVal s.mem base y M.n : Int) = b)
    (ha0 : |a| ≤ p) (hb0 : |b| ≤ p) :
    WP isa (.block (lin w w' T x y U M.n (M.n + 1) ++ mredC M dst T U)) s fun t =>
      (wordsVal t.mem base dst M.n : Int) = Divstep.mred p M.minv.toNat (u * a + v * b) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧
      Unch base [(T, 8 * (M.n + 2)), (U, 8 * (M.n + 1)), (dst, 8 * M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hn0 := hM.n0
  rw [WP.block_append_iff]
  refine WP.mono (linM_ok hs hw hw' (k := M.n) (K := M.n + 1) (by omega) (by omega) (by omega) hx hy (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hu, hv, Divstep.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), ha, hb] at e₁
  have hM₁ := modOk_out hM O₁ (by have := hM.mo; apart) hn
  have hT' : |u * a + v * b| ≤ 2 ^ 63 * (p : Int) := by
    have := Divstep.comb_le huv ha0 hb0
    have hp : (0 : Int) ≤ p := Int.natCast_nonneg _
    nlinarith
  have O₁' : Unch base [(T, 8 * (M.n + 2)), (U, 8 * (M.n + 1))] s.mem s₁.mem := fun z hz => O₁ z (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz ⊢; omega)
  refine WP.mono (mredC_ok hs₁ hM₁ hT hd hU hTm hdT (by omega) hUm hT' e₁) fun t ⟨e, k, O⟩ =>
    ⟨e, k₁.trans k, (O₁'.trans O).mono fun w hw => ?_⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with h | h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.X86_64
