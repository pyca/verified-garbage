module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordSub
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.WordStep

meta import VerifiedGarbage.Proof.Rsa.X86_64.WordSub
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.WordStep

/-! # A normalized remainder step with a full low input word

The quotient estimate, multiword multiply-subtract and two masked corrections
compute `(remainder * 2^64 + digit) mod modulus` at the factors' width, while
the surrounding workspace may have a different stride.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w
open VG.Proof.Bignum.WordStep

theorem step_ok {t : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr t B Z)
    (hbx : t.gpr .rbx = off B ex) (h10 : t.gpr .r10 = off B em) (h8 : t.gpr .r8 = off B et)
    (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hbp : t.gpr .rbp = off B ev)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hXz : ex + 8 * w ≤ Z) (hMz : em + 8 * w ≤ Z) (hTz : et + 8 * (w + 1) ≤ Z) (hE : ev + 16 ≤ Z)
    (sepX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et)
    (sepM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat)
    (hv : (word t.mem B ev).toNat =
      (2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem B ex w < wv t.mem B em w) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t fun t' =>
      wv t'.mem B ex w = (wv t.mem B ex w * 2 ^ 64 + (word t.mem B (ev + 8)).toNat) % wv t.mem B em w ∧
      Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hs.nowrap
  unfold Impl.Rsa.X86_64.WordReduce.step
  change WP isa (.seq (.block quot) (.seq Impl.Rsa.X86_64.WordReduce.mulSub
    (.seq addBack (.seq addBack copyBack)))) t _
  let t₁ := t
  have hm₁ : t₁.mem = t.mem := rfl
  have k₁ : Keep [] t t₁ := Keep.refl _ _
  have h1bx : t₁.gpr .rbx = off B ex := hbx
  have h110 : t₁.gpr .r10 = off B em := h10
  have h18 : t₁.gpr .r8 = off B et := h8
  have h112 : t₁.gpr .r12 = BitVec.ofNat 64 w := h12
  have h1bp : t₁.gpr .rbp = off B ev := hbp
  have hs₁ : Scr t₁ B Z := hs
  generalize hX : wv t.mem B ex w = X at hx
  generalize hM : wv t.mem B em w = M at hx
  have hu := top_le (by omega_arith) (hX ▸ hM ▸ hx)
  rw [← hm₁] at hu hd hv
  have e1 : ex + 8 * w ≤ Z := hXz
  have e2 : em + 8 * w ≤ Z := hMz
  have e3 : ev + 8 ≤ Z := by omega_arith
  have eT : et + 8 * (w + 1) ≤ Z := hTz
  have sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et := sepX
  have sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et := sepM
  have hw31 : w < 2 ^ 31 := by omega_arith
  have hq := quot_ok hs₁ h1bx h110 h112 h1bp hw e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  generalize hqh : min (((word t₁.mem B (ex + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t₁.mem B (ex + 8 * (w - 2))).toNat) / (word t₁.mem B (em + 8 * (w - 1))).toNat)
      (2 ^ 64 - 1) = qh at h2cx
  have hqh' : qh < 2 ^ 64 := by rw [← hqh]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₂ := hs₁.congr k₂.2.2
  have t₂bx : t₂.gpr .rbx = off B (ex) := (k₂.gpr (by decide)).trans h1bx
  have t₂10 : t₂.gpr .r10 = off B (em) := (k₂.gpr (by decide)).trans h110
  have t₂8 : t₂.gpr .r8 = off B (et) := (k₂.gpr (by decide)).trans h18
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  have t₂bp : t₂.gpr .rbp = off B ev := (k₂.gpr (by decide)).trans h1bp
  have hms := mulSub_ok hs₂ t₂bx t₂10 t₂8 t₂bp hE t₂12 hw hw31 e1 e2 eT sX sM
  refine WP.seq (WP.mono hms fun t₃ ⟨b, hv₃, ho₃, k₃⟩ => ?_)
  rw [h2cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqh'] at hv₃
  have hs₃ := hs₂.congr k₃.2.2
  have t₃10 : t₃.gpr .r10 = off B (em) := (k₃.gpr (by decide)).trans t₂10
  have t₃8 : t₃.gpr .r8 = off B (et) := (k₃.gpr (by decide)).trans t₂8
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂12
  have hab₃ := addBack_ok hs₃ t₃10 t₃8 t₃12 (by omega_arith) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₃ fun t₄ ⟨c1, hv₄, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have t₄10 : t₄.gpr .r10 = off B (em) := (k₄.gpr (by decide)).trans t₃10
  have t₄8 : t₄.gpr .r8 = off B (et) := (k₄.gpr (by decide)).trans t₃8
  have t₄12 : t₄.gpr .r12 = BitVec.ofNat 64 w := (k₄.gpr (by decide)).trans t₃12
  have hab₄ := addBack_ok hs₄ t₄10 t₄8 t₄12 (by omega_arith) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₄ fun t₅ ⟨c2, hv₅, ho₅, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have t₅bx : t₅.gpr .rbx = off B (ex) :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans t₂bx))
  have t₅8 : t₅.gpr .r8 = off B (et) := (k₅.gpr (by decide)).trans t₄8
  have t₅12 : t₅.gpr .r12 = BitVec.ofNat 64 w := (k₅.gpr (by decide)).trans t₄12
  unfold R2Words.copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t' => t'.gpr .rsi = off B (et) ∧ t'.mem = t₅.mem)
    (by xrun [t₅8]) rfl) fun t₆ ⟨⟨h6si, hm₆⟩, k₆⟩ => ?_)
  have hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) < ex ∨
      ex + 8 * w ≤ ofs B (off B (et + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_arith)]; omega_arith
  have hs₆ := hs₅.congr k₆.2.2
  have hrd : ∀ j < w, InRegions (t₆.rd ++ t₆.wr) (off B (et + 8 * j)) 8 := fun j hj => hs₆.ld (by omega_arith)
  have hwr : ∀ j < w, InRegions t₆.wr (off B (ex + 8 * j)) 8 := fun j hj => hs₆.st (by omega_arith)
  have hcw := copyWords_ok (S := B) (D := B) h6si ((k₆.gpr (by decide)).trans t₅bx)
    ((k₆.gpr (by decide)).trans t₅12) (by omega_arith) hw31 (by omega_arith) hrd hwr hsepw
  refine WP.mono hcw fun t' ⟨hc, _, ho', k'⟩ => ?_
  -- Memory: `m` and `x` as on entry until the copy; the accumulator's changes.
  have em3 : ∀ {d n}, d + 8 * n ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₃.wv (by omega_arith) (by omega_arith), hm₂, hm₁]
  have em5 : ∀ {d n}, d + 8 * n ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 * n ≤ Z →
      wv t₅.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₅.wv (by omega_arith) (by omega_arith), ho₄.wv (by omega_arith) (by omega_arith), em3 h h']
  have wo3 : ∀ {d}, d + 8 ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 ≤ Z →
      word t₃.mem B d = word t.mem B d := fun h h' => by
    rw [ho₃.word (by omega_arith) (by omega_arith), hm₂, hm₁]
  have wo4 : ∀ {d}, d + 8 ≤ et ∨ et + 8 * (w + 1) ≤ d → d + 8 ≤ Z →
      word t₄.mem B d = word t.mem B d := fun h h' => by
    rw [ho₄.word (by omega_arith) (by omega_arith), wo3 h h']
  rw [em3 (n := w) (d := em) (by omega_arith) (by omega_arith), hM] at hv₄
  rw [ho₄.wv (d := em) (k := w) (by omega_arith) (by omega_arith), em3 (n := w) (d := em) (by omega_arith) (by omega_arith),
    hM] at hv₅
  rw [hm₂, hm₁, hX, hM] at hv₃
  simp only [← top_half] at hv₄ hv₅
  -- The step's value.
  have hX' : X = (word t.mem B (ex + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (ex + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B (ex) (w - 2) := by
    rw [← hX, show w = (w - 2) + 1 + 1 by omega_arith, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega_arith,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega_arith]
    grind
  have hM' : M = (word t.mem B (em + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      wv t.mem B (em) (w - 1) := by
    rw [← hM, show w = (w - 1) + 1 by omega_arith, wv_succ, show w - 1 + 1 - 1 = w - 1 by omega_arith]; grind
  rw [hm₁] at hqh
  have hT3 := wordStepDigit_val hw (BitVec.isLt (word t.mem B (ev + 8))) hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (by rw [← hm₁]; exact hd)
    (BitVec.isLt _) hx (wv_lt _ _ _ _) (Bool.toNat_lt b) (by rw [hqh]; exact hv₃) (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₄ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₅
  have hlow : wv t₅.mem B (et) w = wv t₅.mem B (et) (w + 1) := by
    have hlt : wv t₅.mem B (et) (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) (hM ▸ wv_lt _ _ _ _)
    rw [wv_succ] at hlt ⊢
    have : (word t₅.mem B (et + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t₅.mem B (et + 8 * w)).toNat by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  have f₃ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₂.mem t₃.mem :=
    Frm.of_outside ho₃ (by simp)
  have f₄ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₃.mem t₄.mem :=
    Frm.of_outside ho₄ (by simp)
  have f₅ : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₄.mem t₅.mem :=
    Frm.of_outside ho₅ (by simp)
  have f' : Frm B [(et, 8 * (w + 1)), (ex, 8 * w)] t₆.mem t'.mem :=
    Frm.of_outside ho' (by simp)
  rw [hm₆] at f'
  have ff := ((f₃.trans f₄).trans f₅).trans f'
  rw [hm₂, hm₁] at ff
  refine ⟨?_, ff, (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans (k₆.trans k')).mono (by decide)⟩
  rw [hc, hm₆, hlow, hT3]

/-- The low input word and modulus are secret; only bases and width are public. -/
theorem step_ct {α : Type} {Φ : α → State → Prop}
    (hp : Pins Φ [.rbx, .r10, .r8, .r12, .rbp]) :
    RelCT isa (Two Φ) Impl.Rsa.X86_64.WordReduce.step fun _ _ => True :=
  two_taint [.rbx, .r10, .r8, .r12, .rbp] hp (by taint_decide)

end VG.Proof.Rsa.X86_64.WordReduce
