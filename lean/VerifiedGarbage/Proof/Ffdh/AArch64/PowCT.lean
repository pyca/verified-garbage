module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Pow
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT

/-!
# FFDH on AArch64: an exponentiation in constant time

`pow` leaks the same in runs on workspaces of the same layout, with the same
pointers and lengths of the base and the exponent, whatever the modulus, the
base and the exponent (`pow_ct`). Its steps' claims are those of RSA's
pieces (`loadArr_ct`, `Mont.ct`, `copyArr_ct`, `expLoop_ct`); between
them, each run satisfies a stage (`PS0` … `PS6`) with the same public data
(`PowPub`), by the steps' correctness.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of `pow`: the workspaces, and the base's and the
exponent's pointers and lengths. -/
structure PowPub where
  x : XPub
  pb : Addr
  lb : Nat
  pe : Addr
  le : Nat

/-- What every step keeps: the modulus' workspace and its values, and the
exponent. -/
def PB (ep el : Nat) (a : PowPub) (mi : BitVec 64) (X : Nat) (s : State) : Prop :=
  SubCtx s a.x.B a.x.Z a.x.o a.x.w a.x.w mi ∧ XVals s a.x.B a.x.o a.x.w mi X ∧ 1 < X ∧ X % 2 = 1 ∧
    a.x.wx = a.x.w ∧ a.x.o + slot a.x.w 8 + tabBytes32 a.x.w ≤ a.x.Z ∧ 2 ≤ a.x.w ∧ a.x.w < 2 ^ 28 ∧
    ∃ eb : List Byte, ep < 32 ∧ el < 32 ∧ word s.mem a.x.B (8 * ep) = a.pe ∧
      word s.mem a.x.B (8 * el) = BitVec.ofNat 64 eb.length ∧ eb.length = a.le ∧ 1 ≤ eb.length ∧
      eb.length ≤ 1024 ∧ Src s a.x.B a.x.Z a.pe eb

/-- The arrays a step may change: past the header's first 17 slots, within the
arrays, not the modulus or the number 1. -/
def StepR (w : Nat) (r : Nat × Nat) : Prop :=
  8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 ∧ (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
    (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1)

theorem stepR_arr (w : Nat) {j : Nat} (hj : j < 8) (h0 : j ≠ aN) (h7 : j ≠ aOne) :
    StepR w (slot w j, 8 * (w + 2)) :=
  ⟨by have := hdr_lt_slot w j (show 31 < 32 by decide); simp only; omega_arith, slot_le hj, slot_sep (w := w) h0,
    slot_sep (w := w) h7⟩

theorem PB.step {ep el : Nat} {a : PowPub} {mi : BitVec 64} {X : Nat} {s t : State} {rs : List (Nat × Nat)}
    (h : PB ep el a mi X s) (hf : Frm (off a.x.B a.x.o) rs s.mem t.mem) (hr : ∀ r ∈ rs, StepR a.x.w r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : PB ep el a mi X t := by
  obtain ⟨hc, hv, hX1, hodd, hwx, hwide, hw2, hw28, eb, hep, hel, hpe, hle, hl, hl1, hl2, hse⟩ := h
  have hGn := hc.good.scr.nowrap
  have hc' := hc.of_frm hf (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) hwr h0
  obtain ⟨hb, hi⟩ := child_frm hc hwide hf (fun r hr' => by have := (hr r hr').2.1; omega_arith)
  exact ⟨hc', hv.of_frmA hGn (by omega_arith) hf (fun r hr' => (hr r hr').2.2), hX1, hodd, hwx, hwide, hw2, hw28, eb,
    hep, hel, by rw [hb _ hep]; exact hpe, by rw [hb _ hel]; exact hle, hl, hl1, hl2, hse.congr hi hrd hwr⟩

/-! ## The stages -/

/-- `R² mod X` in `aR2`. -/
def R2At (a : PowPub) (X : Nat) (s : State) : Prop :=
  wv s.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w < X ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w % X = 2 ^ (64 * a.x.w) * 2 ^ (64 * a.x.w) % X

def PS1 (ep el : Nat) (a : PowPub) (s : State) : Prop :=
  ∃ mi X, PB ep el a mi X s ∧ R2At a X s

def PS0 (bp bl ep el : Nat) (a : PowPub) (s : State) : Prop :=
  PS1 ep el a s ∧ LPre aXm bp bl ⟨a.x, a.pb, a.lb⟩ s

def PS2 (ep el : Nat) (a : PowPub) (s : State) : Prop :=
  ∃ mi X, PB ep el a mi X s ∧ R2At a X s ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w < X ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w % X = 2 ^ (64 * a.x.w) % X

def PS3 (ep el : Nat) (a : PowPub) (s : State) : Prop :=
  ∃ mi X x, PB ep el a mi X s ∧ R2At a X s ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w < X ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w % X = 2 ^ (64 * a.x.w) % X ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aXm) a.x.w < X ∧
    wv s.mem (off a.x.B a.x.o) (slot a.x.w aXm) a.x.w % X = x * 2 ^ (64 * a.x.w) % X

/-- After the exponentiation: what the last multiplication needs. -/
def PS6 (a : PowPub) (s : State) : Prop :=
  ∃ mi X, SubCtx s a.x.B a.x.Z a.x.o a.x.w a.x.w mi ∧ XVals s a.x.B a.x.o a.x.w mi X ∧ 1 < X ∧
    2 ≤ a.x.w ∧ a.x.w < 2 ^ 28

/-- The inner workspace, as Montgomery multiplication sees it. -/
abbrev PowPub.ws (a : PowPub) : Ws := ⟨off a.x.B a.x.o, slot a.x.w 8, a.x.w⟩

theorem PS1.goodW {ep el : Nat} {a : PowPub} {s : State} (h : PS1 ep el a s) : GoodW a.ws s := by
  obtain ⟨mi, X, ⟨hc, -⟩, -⟩ := h
  exact ⟨mi, hc.good, Nat.le_refl _⟩

/-- Before the exponentiation: its hypotheses, with the number 1 and `1 < X`. -/
def PS5 (ep el : Nat) (a : PowPub) (s : State) : Prop :=
  EPreWide ep el ⟨a.x, a.pe, a.le⟩ s ∧ wv s.mem (off a.x.B a.x.o) (slot a.x.w aOne) a.x.w = 1 ∧
    1 < wv s.mem (off a.x.B a.x.o) (slot a.x.w aN) a.x.w ∧ a.x.wx = a.x.w ∧ a.x.w < 2 ^ 28

/-! ## The steps' correctness, stage to stage -/

theorem pb_consts {ep el : Nat} {a : PowPub} {mi : BitVec 64} {X : Nat} {s : State} (h : PB ep el a mi X s) :
    2 ≤ a.x.w ∧ a.x.w < 2 ^ 28 ∧ (off a.x.B a.x.o).toNat + slot a.x.w 8 ≤ 2 ^ 64 :=
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.1.good.scr.nowrap⟩

theorem ps0_ps1 {bp bl ep el : Nat} (a : PowPub) (s : State) (h : PS0 bp bl ep el a s) :
    WP isa (seqs (loadArr aXm bp bl)) s (PS1 ep el a) := by
  obtain ⟨⟨mi, X, hb, hR⟩, ⟨mi', bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, -, hsrc, hk1, hk', hkw⟩⟩ := h
  obtain ⟨hw2', hw28, hGn⟩ := pb_consts hb
  refine WP.mono (primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw) fun t ⟨_, _, ho, k⟩ => ?_
  have f : Frm (off a.x.B a.x.o) [(slot a.x.wx aXm, 8 * (a.x.wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  have e : a.x.wx = a.x.w := hb.2.2.2.2.1
  rw [e] at f
  have hr : ∀ r ∈ [(slot a.x.w aXm, 8 * (a.x.w + 2))], StepR a.x.w r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)
  refine ⟨mi, X, hb.step f hr k.rd k.wr (k.gpr .x0 (by decide)), ?_⟩
  have e2 := f.wv_eq (d := slot a.x.w aR2) (k := a.x.w)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := slot_sep (w := a.x.w) (show aR2 ≠ aXm by decide); simp only; omega_arith)
    (by have := slot_le (w := a.x.w) (show aR2 < 8 by decide); omega_arith)
  exact ⟨by rw [e2]; exact hR.1, by rw [e2]; exact hR.2⟩

theorem ps1_ps2 (M : Mont) {ep el : Nat} (a : PowPub) (s : State) (h : PS1 ep el a s) :
    WP isa (M.mm aY aR2 aOne) s (PS2 ep el a) := by
  obtain ⟨mi, X, hb, hR⟩ := h
  obtain ⟨hw2, hw28, hGn⟩ := pb_consts hb
  have hv := hb.2.1
  refine WP.mono (M.mm_ok hb.1.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv.inv
    (by rw [hv.one, hv.n]; exact hb.2.2.1)) fun t ⟨_, hYl, hYv, ha, k⟩ => ?_
  simp only [hv.n, hv.one, Nat.mul_one] at hYl hYv
  have f : Frm (off a.x.B a.x.o) [(slot a.x.w aAcc, 8 * (a.x.w + 2)), (slot a.x.w aTmp, 8 * (a.x.w + 2)),
      (slot a.x.w aY, 8 * (a.x.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  have hb' := hb.step f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact stepR_arr _ (by decide) (by decide) (by decide)) k.rd k.wr (k.gpr .x0 (by decide))
  have hR' : wv t.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w = wv s.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w :=
    ha.wv_of_not_mem (by decide) (by decide) hGn
  have hRc : Nat.Coprime (2 ^ (64 * a.x.w)) X := VG.Proof.Bignum.coprime_pow2 hb.2.2.2.1 _
  refine ⟨mi, X, hb', ⟨by rw [hR']; exact hR.1, by rw [hR']; exact hR.2⟩, hYl, mont_cancel hRc ?_⟩
  rw [hYv, hR.2]

theorem ps2_ps3 (M : Mont) {ep el : Nat} (a : PowPub) (s : State) (h : PS2 ep el a s) :
    WP isa (M.mm aXm aXm aR2) s (PS3 ep el a) := by
  obtain ⟨mi, X, hb, hR, hYl, hYv⟩ := h
  obtain ⟨hw2, hw28, hGn⟩ := pb_consts hb
  have hv := hb.2.1
  refine WP.mono (M.mm_ok hb.1.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aXm) (a := aXm) (b := aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv.inv
    (by rw [hv.n]; exact hR.1)) fun t ⟨_, hXl, hXv, ha, k⟩ => ?_
  simp only [hv.n] at hXl hXv
  have f : Frm (off a.x.B a.x.o) [(slot a.x.w aAcc, 8 * (a.x.w + 2)), (slot a.x.w aTmp, 8 * (a.x.w + 2)),
      (slot a.x.w aXm, 8 * (a.x.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  have hb' := hb.step f (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact stepR_arr _ (by decide) (by decide) (by decide)) k.rd k.wr (k.gpr .x0 (by decide))
  have hR' : wv t.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w = wv s.mem (off a.x.B a.x.o) (slot a.x.w aR2) a.x.w :=
    ha.wv_of_not_mem (by decide) (by decide) hGn
  have hY' : wv t.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w = wv s.mem (off a.x.B a.x.o) (slot a.x.w aY) a.x.w :=
    ha.wv_of_not_mem (by decide) (by decide) hGn
  have hRc : Nat.Coprime (2 ^ (64 * a.x.w)) X := VG.Proof.Bignum.coprime_pow2 hb.2.2.2.1 _
  refine ⟨mi, X, wv s.mem (off a.x.B a.x.o) (slot a.x.w aXm) a.x.w, hb', ⟨by rw [hR']; exact hR.1,
    by rw [hR']; exact hR.2⟩, by rw [hY']; exact hYl, by rw [hY']; exact hYv, hXl, mont_cancel hRc ?_⟩
  rw [hXv, Nat.mul_mod, hR.2, ← Nat.mul_mod, Nat.mul_assoc]

theorem ps3_copy {ep el : Nat} (a : PowPub) (s : State) (h : PS3 ep el a s) :
    WP isa (seqs (copyArr aX aR2)) s (PS3 ep el a) := by
  obtain ⟨mi, X, x, hb, hR, hYl, hYv, hXl, hXv⟩ := h
  obtain ⟨hw2, hw28, hGn⟩ := pb_consts hb
  refine WP.mono (copyArr_ok hb.1.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aX < 8 by decide)
    (show aR2 < 8 by decide) (by decide)) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off a.x.B a.x.o) [(slot a.x.w aX, 8 * (a.x.w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot a.x.w aX) (n' := 8 * (a.x.w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hr : ∀ r ∈ [(slot a.x.w aX, 8 * (a.x.w + 2))], StepR a.x.w r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)
  have e : ∀ {j}, j < 8 → j ≠ aX → wv t.mem (off a.x.B a.x.o) (slot a.x.w j) a.x.w =
      wv s.mem (off a.x.B a.x.o) (slot a.x.w j) a.x.w := fun hj hne =>
    f.wv_eq (fun r hr' => by rw [List.mem_singleton.mp hr']; have := slot_sep (w := a.x.w) hne; simp only; omega_arith)
      (by have := slot_le (w := a.x.w) hj; omega_arith)
  exact ⟨mi, X, x, hb.step f hr k.rd k.wr (k.gpr .x0 (by decide)),
    ⟨by rw [e (by decide) (by decide)]; exact hR.1, by rw [e (by decide) (by decide)]; exact hR.2⟩,
    by rw [e (by decide) (by decide)]; exact hYl, by rw [e (by decide) (by decide)]; exact hYv,
    by rw [e (by decide) (by decide)]; exact hXl, by rw [e (by decide) (by decide)]; exact hXv⟩

theorem ps3_ps5 {ep el : Nat} (a : PowPub) (s : State) (h : PS3 ep el a s) :
    WP isa (seqs (copyArr Crt.aXc aXm)) s (PS5 ep el a) := by
  obtain ⟨mi, X, x, hb, hR, hYl, hYv, hXl, hXv⟩ := h
  obtain ⟨hw2, hw28, hGn⟩ := pb_consts hb
  obtain ⟨hc, hv, hX1, hodd, hwx, hwide, -, -, eb, hep, hel, hpe, hle, hl, hl1, hl2, hse⟩ := hb
  refine WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show Crt.aXc < 8 by decide)
    (show aXm < 8 by decide) (by decide)) fun t ⟨hC, ho, k⟩ => ?_
  have eXc : Crt.aXc = aR2 := rfl
  rw [eXc] at hC ho
  have f : Frm (off a.x.B a.x.o) [(slot a.x.w aR2, 8 * (a.x.w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot a.x.w aR2) (n' := 8 * (a.x.w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hr : ∀ r ∈ [(slot a.x.w aR2, 8 * (a.x.w + 2))], StepR a.x.w r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact stepR_arr _ (by decide) (by decide) (by decide)
  have hb' := PB.step (ep := ep) (el := el) (a := a) (mi := mi) (X := X)
    ⟨hc, hv, hX1, hodd, hwx, hwide, hw2, hw28, eb, hep, hel, hpe, hle, hl, hl1, hl2, hse⟩ f hr k.rd k.wr
    (k.gpr .x0 (by decide))
  obtain ⟨hc', hv', -, -, -, -, -, -, eb', hep', hel', hpe', hle', hl', hl1', hl2', hse'⟩ := hb'
  have e : ∀ {j}, j < 8 → j ≠ aR2 → wv t.mem (off a.x.B a.x.o) (slot a.x.w j) a.x.w =
      wv s.mem (off a.x.B a.x.o) (slot a.x.w j) a.x.w := fun hj hne =>
    f.wv_eq (fun r hr' => by rw [List.mem_singleton.mp hr']; have := slot_sep (w := a.x.w) hne; simp only; omega_arith)
      (by have := slot_le (w := a.x.w) hj; omega_arith)
  refine ⟨⟨⟨mi, X, x, 1, eb', by rw [hwx]; exact hc', by dsimp only; omega_arith, by dsimp only; omega_arith,
    by dsimp only; omega_arith, by rw [hwx]; exact hv'.n,
    by rw [hwx]; exact hv'.inv, hodd, by rw [hwx, eXc, hC]; exact hXl, by rw [hwx, eXc, hC]; exact hXv,
    by rw [hwx, e (by decide) (by decide)]; exact hYl, by rw [hwx, e (by decide) (by decide), Nat.one_mul]; exact hYv,
    hep', hel', hpe', hle', hl', hl1', hl2', hse'⟩, by rw [hwx]; exact hwide⟩, hv'.one,
    by rw [hv'.n]; exact hX1, hwx, hw28⟩

theorem ps5_ps6 (W : Window) (M : Mont) (S : Selector) {ep el : Nat} (a : PowPub) (s : State) (h : PS5 ep el a s) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code ep el) s (PS6 a) := by
  obtain ⟨⟨⟨mi, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hlen, hL1,
    hL2, he⟩, hwide⟩, hone, hX1, hwxe, hw28⟩ := h
  dsimp only at *
  rw [hwxe] at hc hn hinv hxl hxc hyl hyc hwide hw2
  rw [hn] at hX1
  refine WP.mono (expLoop_ok W M S (Q := False) (x := 0) hc hwide hw2 (Nat.le_refl _) (by omega_arith) hn hinv hodd hxl
    False.elim hyl False.elim hsp hsl hep hel hL1 hL2 he) fun t ⟨hc', _, _, f, _⟩ => ?_
  have hGn := hc.good.scr.nowrap
  have hv : XVals s a.x.B a.x.o a.x.w mi X := ⟨hn, hinv, hone⟩
  refine ⟨mi, X, hc', hv.of_frmA hGn (by omega_arith) f (fun r hr => ?_), hX1, hw2, hw28⟩
  simp only [CrtWindowFive.crtExpRanges, crtWinRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (unfold slot hdrBytes; simp only [aN, aOne, aAcc, aTmp, aY, Crt.aT, Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sTab,
    Crt.sV, Crt.sBit, Crt.sNib, Crt.sEnt, Crt.sJ, sFn, tabBytes32]; omega_arith)

theorem ps6_ps6 (M : Mont) (a : PowPub) (s : State) (h : PS6 a s) : WP isa (M.mm aY aY aOne) s (PS6 a) := by
  obtain ⟨mi, X, hc, hv, hX1, hw2, hw28⟩ := h
  have hGn := hc.good.scr.nowrap
  refine WP.mono (M.mm_ok hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aY) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv.inv
    (by rw [hv.one, hv.n]; exact hX1)) fun t ⟨_, _, _, ha, k⟩ => ?_
  have f : Frm (off a.x.B a.x.o) [(slot a.x.w aAcc, 8 * (a.x.w + 2)), (slot a.x.w aTmp, 8 * (a.x.w + 2)),
      (slot a.x.w aY, 8 * (a.x.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  have hr : ∀ r ∈ [(slot a.x.w aAcc, 8 * (a.x.w + 2)), (slot a.x.w aTmp, 8 * (a.x.w + 2)),
      (slot a.x.w aY, 8 * (a.x.w + 2))], StepR a.x.w r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact stepR_arr _ (by decide) (by decide) (by decide)
  exact ⟨mi, X, hc.of_frm f (fun r hr' => ⟨(hr r hr').1, (hr r hr').2.1⟩) k.wr (k.gpr .x0 (by decide)),
    hv.of_frmA hGn (by omega_arith) f (fun r hr' => (hr r hr').2.2), hX1, hw2, hw28⟩

/-! ## Constant time -/

theorem PS2.goodW {ep el : Nat} {a : PowPub} {s : State} (h : PS2 ep el a s) : GoodW a.ws s := by
  obtain ⟨mi, X, ⟨hc, -⟩, -⟩ := h
  exact ⟨mi, hc.good, Nat.le_refl _⟩

theorem PS3.goodW {ep el : Nat} {a : PowPub} {s : State} (h : PS3 ep el a s) : GoodW a.ws s := by
  obtain ⟨mi, X, x, ⟨hc, -⟩, -⟩ := h
  exact ⟨mi, hc.good, Nat.le_refl _⟩

theorem PS6.goodW {a : PowPub} {s : State} (h : PS6 a s) : GoodW a.ws s := by
  obtain ⟨mi, X, hc, -⟩ := h
  exact ⟨mi, hc.good, Nat.le_refl _⟩

/-- `pow_ok`'s hypotheses give `PS0`. -/
theorem ps0_of {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat} (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    PS0 bp bl ep el ⟨⟨B, Z, o, w, w⟩, pb, bb.length, pe, eb.length⟩ s := by
  have hw2 := hc.w2
  have hw28 := hc.w28
  exact ⟨⟨mi, X, ⟨hc.sub, hc.xv, hc.x1, hc.odd, rfl, hc.wide, hw2, hw28, eb, hep, hel, hpe, hle, rfl, he1, he2, hse⟩,
    hc.r2l, hc.r2⟩, ⟨mi, bb, hc.sub, hw2, Nat.le_refl _, show w < 2 ^ 30 by omega_arith, by decide, hbp, hbl, hpb, hlb, rfl, hsb, hb1,
    by omega_arith, hb2⟩⟩

/-- `pow` leaks the same in runs that agree on the public data, given that the
taint analysis checks the copies' header loads. -/
theorem pow_ct (W : Window) (M : Mont) (S : Selector) {bp bl ep el : Nat} (hL : LoadCT aXm bp bl)
    (hE : RelCT isa (Two (EPreWide ep el)) (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code ep el)
      fun _ _ => True)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr aR2), ldh .x17 (sArr aX)])
      hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr aXm), ldh .x17 (sArr Crt.aXc)])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aR2)])
      hc₃).isSome = true) :
    RelCT isa (Two (PS0 bp bl ep el)) (seqs (pow W.code S.code M.mm bp bl ep el)) fun _ _ => True := by
  unfold pow
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (R := Two (PS1 ep el))
    (two_post (two_map (fun a : PowPub => (⟨a.x, a.pb, a.lb⟩ : BPub)) (fun _ _ h => h.2) hL) ps0_ps1) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (PS2 ep el))
    (two_post (two_map PowPub.ws (fun _ _ h => PS1.goodW h) (M.ct (by unfold MmUse; decide))) (ps1_ps2 M)) ?_)
  refine seqs_cons_ct (by simp [copyArr]) (RelCT.seq (R := Two (PS3 ep el))
    (two_post (two_map PowPub.ws (fun _ _ h => PS2.goodW h) (M.ct (by unfold MmUse; decide))) (ps2_ps3 M)) ?_)
  refine RelCT.seqs_append (by simp [copyArr]) (by simp [copyArr]) (RelCT.seq (R := Two (PS3 ep el))
    (two_post (two_map PowPub.ws (fun _ _ h => PS3.goodW h) (copyArr_ct (by decide) (by decide) hT₁)) ps3_copy) ?_)
  refine RelCT.seqs_append (by simp [copyArr]) (by simp [copyArr]) (RelCT.seq (R := Two (PS5 ep el))
    (two_post (two_map PowPub.ws (fun _ _ h => PS3.goodW h) (copyArr_ct (by decide) (by decide) hT₂)) ps3_ps5) ?_)
  refine seqs_cons_ct (by simp [copyArr]) (RelCT.seq (R := Two PS6)
    (two_post (two_map (fun a : PowPub => (⟨a.x, a.pe, a.le⟩ : BPub)) (fun _ _ h => h.1) hE) (ps5_ps6 W M S)) ?_)
  refine seqs_cons_ct (by simp [copyArr]) (RelCT.seq (R := Two PS6)
    (two_post (two_map PowPub.ws (fun _ _ h => PS6.goodW h) (M.ct (by unfold MmUse; decide))) (ps6_ps6 M)) ?_)
  exact two_map PowPub.ws (fun _ _ h => PS6.goodW h) (copyArr_ct (by decide) (by decide) hT₃)

end VG.Proof.Ffdh.AArch64
