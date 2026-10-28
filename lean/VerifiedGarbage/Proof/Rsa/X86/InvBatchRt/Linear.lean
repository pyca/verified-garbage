module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
import VerifiedGarbage.Proof.Weierstrass.X86.InvLinearMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead

/-! # The signed linear combination at a run-time width

`correction_ok`: `[acc + 4] -= [src]`, `n` words, if the coefficient at a header
word is negative, as the difference into `[tmp]` selected into place, with
`InvMemory.correction`'s statement; `linear_ok`: `InvMemory.linear`'s signed
combination modulo `n + 1` words, with its statement.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem rv_byte (w : Nat) (x : Ref) (d : Nat) : rv w { x with byte := x.byte + d } = rv w x + d := by
  simp only [rv]; omega

/-- The correction: `[acc + 4] -= [src]` (`n` words) if the coefficient at `c` is negative. -/
theorem correction_ok {s : State} (h : Bx L s B Z len N) {c : Nat} (hc : c + 4 ≤ 160)
    {acc src tmp : Ref} (hth : tmp.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 1) ≤ Z) (hsz : rv (kw len) src + 4 * nw len ≤ Z)
    (htz : rv (kw len) tmp + 4 * nw len ≤ Z)
    (ta : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (ts : rv (kw len) tmp ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) tmp) :
    WP isa (correction L c acc src tmp) s fun u =>
      Bx L u B Z len N ∧ Unch B [(rv (kw len) acc, 4 * (nw len + 1)), (rv (kw len) tmp, 4 * nw len)] s.mem u.mem ∧
      Keeps wordClob s u ∧
      ∃ cb : Bool, val32 u.mem B (rv (kw len) acc) (nw len + 1) +
          2 ^ 32 * (if 2 ^ 31 ≤ w32 s.mem B c then val32 s.mem B (rv (kw len) src) (nw len) else 0) =
        val32 s.mem B (rv (kw len) acc) (nw len + 1) + 2 ^ (32 * (nw len + 1)) * cb.toNat := by
  have hn := h.nowrap
  have ra := rv_ge (kw len) acc
  have rt := rv_ge (kw len) tmp
  have e4 := rv_byte (kw len) acc 4
  unfold correction
  -- The difference.
  refine WP.seq (WP.mono (chainSub_ok h (o := tmp) (a := { acc with byte := acc.byte + 4 }) (b := src) (e := 0)
    (by decide) hth (by simpa using htz) (by rw [e4]; simpa using (by omega : rv (kw len) acc + 4 + 4 * nw len ≤ Z))
    (by simpa using hsz) (by rw [e4]; simp only [Nat.add_zero]; omega) (by simpa using ts))
    fun s₁ ⟨H₁, O₁, ⟨cb, _, V₁⟩, K₁⟩ => ?_)
  rw [e4] at V₁
  simp only [Nat.add_zero] at O₁ V₁
  have C₁ : w32 s₁.mem B c = w32 s.mem B c := O₁.w32 (.inl (by omega)) (by omega)
  -- The coefficient's sign, then the selection.
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.X86.Inv.maskOf_ok H₁.ws.ws.workspace (coefficient := c) (by omega))
    fun s₂ ⟨M₂, K₂, m₂⟩ => ?_)
  have H₂ : Bx L s₂ B Z len N := H₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  rw [C₁] at M₂
  refine WP.mono (selIn_ok H₂ (o := { acc with byte := acc.byte + 4 }) (a := tmp) (e := 0)
    (k := decide (2 ^ 31 ≤ w32 s.mem B c)) (by rw [M₂]; simp [cmask]) (by decide)
    (by rw [e4]; omega) (by simpa using htz) (by rw [e4]; omega)) fun u ⟨H, O, V, K⟩ => ?_
  rw [e4, m₂] at O V
  simp only [Nat.add_zero] at O V
  refine ⟨H, ?_, ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K.mono (by decide)), ?_⟩
  · intro x hx
    rw [O x (by have := hx _ (List.mem_cons_self ..); omega), O₁ x (hx (rv (kw len) tmp, 4 * nw len) (by simp))]
  · -- Word 0 is kept; words 1 to `n` are the selected ones.
    have w0 : w32 u.mem B (rv (kw len) acc) = w32 s.mem B (rv (kw len) acc) := by
      rw [O.w32 (.inl (by omega)) (by omega), O₁.w32 (by omega) (by omega)]
    have A₁ : val32 s₁.mem B (rv (kw len) acc + 4) (nw len) = val32 s.mem B (rv (kw len) acc + 4) (nw len) :=
      O₁.val32 (by omega) (by omega)
    refine ⟨if 2 ^ 31 ≤ w32 s.mem B c then cb else false, ?_⟩
    rw [val32, val32, w0]
    by_cases hk : 2 ^ 31 ≤ w32 s.mem B c
    · simp only [hk, decide_true, ite_true] at V ⊢
      rw [V, show 32 * (nw len + 1) = 32 + 32 * nw len by omega, Nat.pow_add, Nat.mul_assoc]
      have := congrArg (2 ^ 32 * ·) V₁
      simp only [Nat.mul_add] at this
      omega
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false] at V ⊢
      rw [V, A₁]
      simp

/-- `linear u v acc a b tmp e`: `InvMemory.linear`'s signed combination of the `n + e`-word inputs
`[a]` and `[b]` with the coefficients at the header words `u` and `v`, modulo `n + 1` words. -/
theorem linear_ok {s : State} (h : Bx L s B Z len N) {u v : Nat} (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    {acc a b tmp : Ref} {e : Nat} (he : e ≤ 1) (hah : a.half = 0) (hbh : b.half = 0) (hth : tmp.half = 0)
    (haccz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z)
    (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z) (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (htz : rv (kw len) tmp + 4 * nw len ≤ Z)
    (sa : rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) a)
    (sb : rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) b)
    (ta : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) tmp)
    (tsa : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) tmp)
    (tsb : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) tmp) :
    WP isa (linear L u v acc a b tmp e) s fun z =>
      Bx L z B Z len N ∧ Unch B [(rv (kw len) acc, 4 * (nw len + e + 2)), (rv (kw len) tmp, 4 * nw len)] s.mem z.mem ∧
      Keeps wordClob s z ∧
      (val32 z.mem B (rv (kw len) acc) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((s.mem.readW (off B u) 32).toInt * val32 s.mem B (rv (kw len) a) (nw len + e) +
         (s.mem.readW (off B v) 32).toInt * val32 s.mem B (rv (kw len) b) (nw len + e)) % 2 ^ (32 * (nw len + 1)) := by
  have hn := h.nowrap
  have ra := rv_ge (kw len) acc
  have rt := rv_ge (kw len) tmp
  unfold linear
  refine WP.seq (WP.mono (linearUnsigned_ok h hu hv (by omega) hah hbh haccz haz hbz sa sb)
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  have U₁ : w32 s₁.mem B u = w32 s.mem B u := O₁.w32 (.inl (by omega)) (by omega)
  have W₁ : w32 s₁.mem B v = w32 s.mem B v := O₁.w32 (.inl (by omega)) (by omega)
  have A₁ : val32 s₁.mem B (rv (kw len) a) (nw len) = val32 s.mem B (rv (kw len) a) (nw len) :=
    O₁.val32 (by omega) (by omega)
  have B₁ : val32 s₁.mem B (rv (kw len) b) (nw len) = val32 s.mem B (rv (kw len) b) (nw len) :=
    O₁.val32 (by omega) (by omega)
  have H₀ : val32 s₁.mem B (rv (kw len) acc) (nw len + 1) =
      (w32 s.mem B u * val32 s.mem B (rv (kw len) a) (nw len + e) +
        w32 s.mem B v * val32 s.mem B (rv (kw len) b) (nw len + e)) % 2 ^ (32 * (nw len + 1)) := by
    rw [VG.Proof.Weierstrass.X86.Inv.prefix_mod s₁.mem B _ (nw len + 1) (nw len + e + 2) (by omega), V₁]
  refine WP.seq (WP.mono (correction_ok H₁ (c := u) (src := a) (tmp := tmp) hu hth (by omega) (by omega) htz
    (by omega) (by omega)) fun s₂ ⟨H₂, O₂, K₂, c₁, V₂⟩ => ?_)
  rw [U₁, A₁] at V₂
  have W₂ : w32 s₂.mem B v = w32 s₁.mem B v := VG.Proof.Weierstrass.X86.Inv.word_unch O₂
    (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> omega)
    (by omega)
  have B₂ : val32 s₂.mem B (rv (kw len) b) (nw len) = val32 s₁.mem B (rv (kw len) b) (nw len) :=
    Outs.val32 O₂
      (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> omega)
      (by omega)
  refine WP.mono (correction_ok H₂ (c := v) (src := b) (tmp := tmp) hv hth (by omega) (by omega) htz
    (by omega) (by omega)) fun z ⟨H₃, O₃, K₃, c₂, V₃⟩ => ?_
  rw [W₂, W₁, B₂, B₁] at V₃
  have H := VG.Proof.Weierstrass.X86.Inv.corrections_mod H₀ V₂ V₃
  refine ⟨H₃, ?_, (K₁.trans K₂).trans K₃, ?_⟩
  · intro x hx
    have hacc := hx (rv (kw len) acc, 4 * (nw len + e + 2)) (by simp)
    have htmp := hx (rv (kw len) tmp, 4 * nw len) (by simp)
    have small : ∀ w ∈ [(rv (kw len) acc, 4 * (nw len + 1)), (rv (kw len) tmp, 4 * nw len)],
        ofs B x < w.1 ∨ w.1 + w.2 ≤ ofs B x := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only at hacc htmp ⊢ <;> omega
    rw [O₃ x small, O₂ x small, O₁ x hacc]
  · have HX := VG.Proof.Weierstrass.X86.Inv.shifted_prefix_mod s.mem B (rv (kw len) a) (nw len) (nw len + e) (by omega)
    have HY := VG.Proof.Weierstrass.X86.Inv.shifted_prefix_mod s.mem B (rv (kw len) b) (nw len) (nw len + e) (by omega)
    have E := VG.Proof.Divstep.W32.lin_words
      (M := (2 : Int) ^ (32 * (nw len + 1)))
      (V := val32 z.mem B (rv (kw len) acc) (nw len + 1))
      (X := val32 s.mem B (rv (kw len) a) (nw len + e)) (X' := val32 s.mem B (rv (kw len) a) (nw len))
      (Y := val32 s.mem B (rv (kw len) b) (nw len + e)) (Y' := val32 s.mem B (rv (kw len) b) (nw len))
      (W := w32 s.mem B u) (W' := w32 s.mem B v)
      (c := 2 ^ 31 ≤ w32 s.mem B u) (c' := 2 ^ 31 ≤ w32 s.mem B v)
      (by exact_mod_cast HX) (by exact_mod_cast HY) (by exact_mod_cast H)
    simpa only [w32, VG.Proof.Divstep.W32.toInt_sgn] using E

end VG.Proof.Rsa.X86.InvBatchRt
