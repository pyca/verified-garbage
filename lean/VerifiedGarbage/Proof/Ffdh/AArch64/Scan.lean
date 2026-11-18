module

public import VerifiedGarbage.Proof.Ffdh.Lead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.Lead
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Ffdh.AArch64.Front
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Front
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.AArch64.Pow
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT

/-! ### `Ffdh.AArch64.PowCT`, which the modules that import this one used -/

section

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

end

end

/-! ### `Ffdh.AArch64.ChecksCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.AArch64.SetupCT`, which the modules that import this one used -/

section

/-!
# FFDH on AArch64: the front in constant time

The check of p (`domHead_ct`) and the workspaces with p, `-p⁻¹` and the
number 1 (`setup_ct`) leak the same in runs with the same working space,
domain pointer and p's length (`DPub`), whatever p: between the pieces,
each run satisfies a stage (`SP1` … `SP3`, `SWPre`) by their correctness,
and the registers a piece's addresses and loop counts come from are fixed
by the stage.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (wsEnd wsNew loadArr leave ldw)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The public data of the front: the working space, p's length and the
domain's pointer. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  dp : Addr

/-- The words of p. -/
abbrev DPub.w (a : DPub) : Nat := (a.k + 7) / 8

/-! ## The check of p -/

/-- `domHead_ok`'s hypotheses. -/
def DHP (a : DPub) (s : State) : Prop :=
  Scr s a.B a.Z ∧ s.gpr .x0 = a.B ∧ 256 ≤ a.Z ∧ word s.mem a.B (8 * sDom) = a.dp ∧
    word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k

theorem domHead_ct : RelCT isa (Two DHP) (.block domHead) fun _ _ => True := by
  unfold domHead
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : DPub) t => t.gpr .x2 = a.dp ∧
      t.gpr .x3 = BitVec.ofNat 64 a.k) [.x0] (pins_x0B DPub.B fun _ _ h => h.2.1) (by taint_decide)
      fun a s h => ?_)
    (two_taint [.x2, .x3] (pins_of (fun (a : DPub) r => if r = .x2 then a.dp else BitVec.ofNat 64 a.k)
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide)))
  obtain ⟨hs, h0, hZ, hD, hK⟩ := h
  exact WP.mono (domHead1_ok hs h0 hZ hD hK) fun t ⟨⟨h2, h3, _⟩, _⟩ => ⟨h2, h3⟩

/-! ## The workspaces -/

/-- `setup_ok`'s hypotheses. -/
def SetupP (a : DPub) (s : State) : Prop :=
  ∃ pb : List Byte, Scr s a.B a.Z ∧ s.gpr .x0 = a.B ∧ 64 ≤ a.k ∧ a.k ≤ 1024 ∧ 128 * a.k + 256 ≤ a.Z ∧
    word s.mem a.B (8 * sDom) = a.dp ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k ∧ Src s a.B a.Z a.dp pb ∧
    pb.length = a.k ∧ Spec.Rsa.os2ip pb % 2 = 1

/-- After `head`: the outer workspace. -/
def SP1 (a : DPub) (s : State) : Prop :=
  ∃ pb : List Byte, Outer s a.B a.Z a.w ∧ 64 ≤ a.k ∧ a.k ≤ 1024 ∧ 128 * a.k + 256 ≤ a.Z ∧
    word s.mem a.B (8 * sDom) = a.dp ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.k ∧ Src s a.B a.Z a.dp pb ∧
    pb.length = a.k ∧ Spec.Rsa.os2ip pb % 2 = 1

/-- The public data of a modulus' workspace: the outer workspace of `w`
words, and the modulus' length and pointer. -/
structure MPub where
  B : Addr
  Z : Nat
  w : Nat
  len : Nat
  ptr : Addr

abbrev MPub.wx (a : MPub) : Nat := wsWords a.len

/-- The inner workspace, as the arithmetic sees it. -/
abbrev MPub.ws (a : MPub) : Ws := ⟨off a.B (inner a.w), slot a.wx 8, a.wx⟩

/-- The modulus' load. -/
abbrev MPub.bp (a : MPub) : BPub := ⟨⟨a.B, a.Z, inner a.w, a.w, a.wx⟩, a.ptr, a.len⟩

/-- `wsMod_ok`'s hypotheses: the outer workspace, and the modulus' length and
pointer in its slots `sl` and `sp`. -/
def M1 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  ∃ bs : List Byte, Outer s a.B a.Z a.w ∧ word s.mem a.B (8 * sl) = BitVec.ofNat 64 a.len ∧
    word s.mem a.B (8 * sp) = a.ptr ∧ Src s a.B a.Z a.ptr bs ∧ bs.length = a.len ∧ 1 ≤ a.len ∧
    a.len ≤ 8 * a.w ∧ Spec.Rsa.os2ip bs % 2 = 1

/-- In the inner workspace. -/
def M2 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (bs : List Byte), SubCtx s a.B a.Z (inner a.w) a.w a.wx mi ∧
    word s.mem a.B (8 * sl) = BitVec.ofNat 64 a.len ∧ word s.mem a.B (8 * sp) = a.ptr ∧ Src s a.B a.Z a.ptr bs ∧
    bs.length = a.len ∧ 1 ≤ a.len ∧ a.len ≤ 8 * a.w ∧ Spec.Rsa.os2ip bs % 2 = 1 ∧ 2 ≤ a.w ∧ a.w < 2 ^ 28

/-- With the modulus, odd, in `aN`. -/
def M3 (a : MPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, SubCtx s a.B a.Z (inner a.w) a.w a.wx mi ∧
    (word s.mem (off a.B (inner a.w)) (slot a.wx aN)).toNat % 2 = 1

theorem m1_pin (sp sl : Nat) (a : MPub) (s : State) (h : M1 sp sl a s) :
    WP isa (.block ([mov .x5 .x0] ++ wsEnd)) s fun t => t.gpr .x0 = a.B ∧ t.gpr .x4 = off a.B (inner a.w) := by
  obtain ⟨_, hO, -⟩ := h
  have hroom := hO.room
  have hw28 := hO.w28
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = a.B ∧ t.mem = s.mem) (by brun [hO.x0]) (by decide)
    (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEnd_ok (wx := a.w) (hO.scr.congr k₁.wr) h5₁ (by rw [hm₁]; exact hO.hw) (by omega_arith)
    (by rw [hm₁]; exact hO.harr _ (by decide)) (by unfold inner tabBytes32 at hroom; omega_arith))
    fun t ⟨⟨h4, _, _⟩, k₂⟩ => ⟨(k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans hO.x0), h4⟩

theorem m1_m2 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs) (a : MPub)
    (s : State) (h : M1 sp sl a s) : WP isa (.block (wsSetup sl ++ [enter])) s (M2 sp sl a) := by
  obtain ⟨bs, hO, hL, hP, hsrc, hl, h1, hlw, hodd⟩ := h
  have hn := hO.scr.nowrap
  have hroom := hO.room
  have hw28 := hO.w28
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes32 at hroom; omega_arith
  have eWs : sWs = 29 := rfl
  refine WP.mono (wsSetup_ok (len := a.len) hO hsl hslW hL h1 hlw) fun t ⟨hc, _, f, k⟩ => ?_
  have hb : ∀ i < 32, i ≠ sWs → word t.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi hne =>
    f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  exact ⟨_, bs, hc, by rw [hb _ hsl hslW]; exact hL, by rw [hb _ hsp hspW]; exact hP,
    hsrc.congrK (InScr.of_frm f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) k, hl, h1, hlw, hodd, hO.w2, hw28⟩

theorem m2_lpre {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    LPre aN sp sl a.bp s := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, -, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega_arith
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega_arith
  exact ⟨mi, bs, hc, hw2, hwx, show a.w < 2 ^ 30 by omega_arith, by decide, hsp, hsl, hP, by rw [hl]; exact hL, hl,
    hsrc, by omega_arith, by omega_arith, show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega_arith⟩

theorem m2_m3 {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (a : MPub) (s : State) (h : M2 sp sl a s) :
    WP isa (seqs (loadArr aN sp sl)) s (M3 a) := by
  obtain ⟨mi, bs, hc, hL, hP, hsrc, hl, h1, hlw, hodd, hw2', hw28⟩ := h
  have hw2 : 2 ≤ a.wx := by unfold MPub.wx wsWords; omega_arith
  have hwx : a.wx ≤ a.w := by unfold MPub.wx wsWords; omega_arith
  refine WP.mono (primeLoad_ok hc hw2 hwx (by omega_arith) (show aN < 8 by decide) hsp hsl hP (by rw [hl]; exact hL)
    hsrc (by omega_arith) (by omega_arith) (show (bs.length + 7) / 8 ≤ a.wx by unfold MPub.wx wsWords; omega_arith))
    fun t ⟨hc₁, hX₁, _, _⟩ => ⟨mi, hc₁, ?_⟩
  rw [← wv_mod64 _ _ _ (show 1 ≤ a.wx by omega_arith), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd

theorem ldArr_ok {t : State} {G : Addr} {Zx wx : Nat} {mi : BitVec 64} (hg : Good t G Zx wx mi)
    (hZ : slot wx 8 ≤ Zx) {j : Nat} (hj : j < 8) :
    WP isa (.block [ldh .x8 (sArr j)]) t fun t' => t'.gpr .x0 = G ∧ t'.gpr .x8 = off G (slot wx j) :=
  WP.mono (WP.keep [.x8] (Q := fun t' => t'.gpr .x8 = off G (slot wx j))
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hg.ld hZ (sArr_lt hj), hg.hdr.harr j hj]) rfl rfl rfl)
    fun t' ⟨h8, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hg.x0, h8⟩

theorem m3_pin (a : MPub) (s : State) (h : M3 a s) :
    WP isa (.block [ldh .x8 (sArr aN)]) s fun t => t.gpr .x0 = off a.B (inner a.w) ∧
      t.gpr .x8 = off (off a.B (inner a.w)) (slot a.wx aN) := by
  obtain ⟨mi, hc, -⟩ := h
  exact ldArr_ok hc.good (Nat.le_refl _) (by decide)

/-- The block of `-m⁻¹` and `setWord`'s operands. -/
abbrev minvB : List Instr :=
  [ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]

theorem m3_m4 (a : MPub) (s : State) (h : M3 a s) :
    WP isa (.block minvB) s fun t => SWPre (a.ws, 0) t := by
  obtain ⟨mi, hc, hodd⟩ := h
  refine WP.mono (minvBlock_ok hc.good (Nat.le_refl _) hodd) fun t ⟨_, hm, h12, _, h13, k⟩ => ?_
  have o := writeW_outside s.mem (off a.B (inner a.w)) (d := 8 * sMinv) (t.gpr .x15) (by decide)
  rw [← hm] at o
  have f : Frm (off a.B (inner a.w)) [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o (by simp)
  have hc' := hc.of_minv f (fun r hr => Or.inl (List.mem_singleton.mp hr)) k.wr (k.gpr .x0 (by decide))
  exact ⟨⟨_, hc'.good, Nat.le_refl _⟩, h12, h13⟩

theorem wsMod_eq (sp sl : Nat) : seqs (([.block (wsSetup sl ++ [enter])] : List (Prog isa)) ++ modSetup sp sl) =
    .seq (.block (([mov .x5 .x0] ++ wsEnd) ++ (wsNew sWs sl ++ [enter])))
      (seqs (loadArr aN sp sl ++ ([.block ([ldh .x8 (sArr aN)] ++ ([ld .x3 .x8] ++ minv ++
        [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])), setWord aOne] : List (Prog isa)))) := rfl

/-- A modulus' workspace: entered, the modulus, `-m⁻¹` and the number 1, given
that the taint analysis checks the blocks that read the slots `sp` and `sl`. -/
theorem wsMod_ct {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0, .x4]) (.block (wsNew sWs sl ++ [enter])) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr aN), ldh .x12 sW, movi .x7 0])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x1 .x5 sp, ldw .x2 .x5 sl, ldh .x8 (sArr aN)])
      hc₃).isSome = true) :
    RelCT isa (Two (M1 sp sl)) (seqs (([.block (wsSetup sl ++ [enter])] : List (Prog isa)) ++ modSetup sp sl)) fun _ _ => True := by
  rw [wsMod_eq]
  refine RelCT.seq (R := Two (M2 sp sl)) (RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : MPub) t =>
      (t.gpr .x0 = a.B ∧ t.gpr .x4 = off a.B (inner a.w)) ∧ WP isa (.block (wsNew sWs sl ++ [enter])) t
        (M2 sp sl a))
      [.x0] (pins_x0B MPub.B fun _ _ ⟨_, hO, _⟩ => hO.x0) (by taint_decide)
      fun a s h => wp_and (m1_pin sp sl a s h) (WP.block_append_iff.mp (m1_m2 hsp hsl hspW hslW a s h)))
    (two_piece [.x0, .x4] (pins_of (fun (a : MPub) r => if r = .x0 then a.B else off a.B (inner a.w))
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) hT₁ fun _ _ h => h.2))) ?_
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (R := Two M3)
    (two_post (two_map MPub.bp (m2_lpre hsp hsl) (loadArr_ct (by decide) hT₂ hT₃)) (m2_m3 hsp hsl)) ?_)
  refine RelCT.seq (R := Two fun (a : MPub) t => SWPre (a.ws, 0) t) (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun (a : MPub) t => (t.gpr .x0 = off a.B (inner a.w) ∧
        t.gpr .x8 = off (off a.B (inner a.w)) (slot a.wx aN)) ∧
      WP isa (.block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) t
        fun t => SWPre (a.ws, 0) t)
      [.x0] (pins_x0B (fun a => off a.B (inner a.w)) fun _ _ ⟨_, hc, _⟩ => hc.x0) (by taint_decide)
      fun a s h => wp_and (m3_pin a s h) (WP.block_append_iff.mp (m3_m4 a s h)))
    (two_piece [.x0, .x8] (pins_of (fun (a : MPub) r => if r = .x0 then off a.B (inner a.w) else
        off (off a.B (inner a.w)) (slot a.wx aN))
      fun a s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) (by taint_decide) fun _ _ h => h.2))) ?_
  exact two_map (fun a : MPub => (a.ws, 0)) (fun _ _ h => h) (setWord_ct (by decide) (by taint_decide))

theorem sp0_sp1 (a : DPub) (s : State) (h : SetupP a s) : WP isa (.block head) s (SP1 a) := by
  obtain ⟨pb, hs, h0, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega_arith
  have hn := hs.nowrap
  have hroom := room_k hk1 hZ
  rw [show (a.k + 7) / 8 = a.w from rfl] at hroom
  have h8 := hdr_lt_slot a.w 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have hi8 : 8 * 32 ≤ inner a.w := by simp only [inner, slot, hdrBytes]; omega_arith
  have hiZ : inner a.w + slot a.w 8 ≤ a.Z := by unfold tabBytes32 at hroom; omega_arith
  refine WP.mono (head_ok hs h0 (show slot a.w 8 ≤ a.Z by unfold inner tabBytes32 at hroom; omega_arith) (by omega_arith) hK)
    fun s₁ ⟨_, hW, hA, f₁, k₁⟩ => ?_
  have hr₁ : ∀ i < 32, i ≠ sW → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₁.mem a.B (8 * i) = word s.mem a.B (8 * i) := fun i hi h1 h2 => f₁.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  exact ⟨pb, ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans h0, hW, hA, hroom, by omega_arith, by omega_arith⟩, hk1, hk2, hZ,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hD,
    by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hK,
    hsrc.congrK (InScr.of_frm f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) k₁, hl, hodd⟩

/-- p's workspace's public data. -/
abbrev DPub.m (a : DPub) : MPub := ⟨a.B, a.Z, a.w, a.k, a.dp⟩

theorem sp1_m1 (a : DPub) (s : State) (h : SP1 a s) : M1 sDom sK a.m s := by
  obtain ⟨pb, hO, hk1, hk2, hZ, hD, hK, hsrc, hl, hodd⟩ := h
  have ew : 8 * a.w ≤ a.k + 7 ∧ a.k ≤ 8 * a.w := by unfold DPub.w; omega_arith
  exact ⟨pb, hO, hK, hD, hsrc, hl, show 1 ≤ a.k by omega_arith, show a.k ≤ 8 * a.w by omega_arith, hodd⟩

/-- `head`, the workspaces, p, `-p⁻¹` and the number 1. -/
theorem setup_ct : RelCT isa (Two SetupP) (seqs (([.block head] : List (Prog isa)) ++ pSetup)) fun _ _ => True := by
  refine RelCT.seq (R := Two SP1) (two_piece [.x0] (pins_x0B DPub.B fun _ _ ⟨_, _, h0, _⟩ => h0) (by taint_decide)
    sp0_sp1) ?_
  exact two_map DPub.m sp1_m1 (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide)
    (by taint_decide) (by taint_decide))

end VG.Proof.Ffdh.AArch64

end

end

/-!
# FFDH on AArch64: the comparisons in constant time

In runs on workspaces of the same layout (`Two GoodW`), whatever the
numbers in them: the header loads are checked by the taint analysis from
`x0`, the loops from the registers the header gave (`w` and the bases).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A workspace is one after code that keeps its memory, `x0` and the
permissions. -/
theorem GoodW.keep {L : Ws} {s t : State} (h : GoodW L s) (hm : t.mem = s.mem) (h0 : t.gpr .x0 = s.gpr .x0)
    (hwr : t.wr = s.wr) : GoodW L t := by
  obtain ⟨mi, hg, hZ⟩ := h
  exact ⟨mi, ⟨hg.scr.congr hwr, h0.trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ⟩

/-- The registers the comparison loops need, from the header. -/
def CmpRegs (a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.gpr .x16 = off L.B (slot L.w a) ∧ t.gpr .x17 = off L.B (slot L.w b)

theorem pins_cmpRegs (a b : Nat) : Pins (CmpRegs a b) [.x14, .x16, .x17] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else
      if r = .x16 then off L.B (slot L.w a) else off L.B (slot L.w b))
    fun L s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

/-- A comparison: its first block (checked by the taint analysis from `x0`),
then code checked from the registers it loads. -/
theorem cmp_ct {a b : Nat} {l : List Instr} {c : Prog isa}
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hl : ∀ (L : Ws) s, GoodW L s → WP isa (.block (ptrs a b ++ l)) s (CmpRegs a b L))
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ l)) hc₁).isSome = true)
    (hT' : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) c hc₂).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (ptrs a b ++ l)) c) fun _ _ => True :=
  RelCT.seq (two_piece [.x0] pins_goodW hT hl) (two_taint [.x14, .x16, .x17] (pins_cmpRegs a b) hT')

theorem ptrsCmp_ok {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7])) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  exact WP.mono (cmpHead_ok hg hZ ha hb) fun _ h => ⟨h.2.2.1, h.1, h.2.1⟩

theorem ptrsEq_ok {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b ++ [movi .x9 0, mov .x14 .x12])) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi => hg.ld hZ hi
  exact WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := CmpRegs a b L)
    (by unfold ptrs CmpRegs; brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt hb), hdr_enc (show sW < 32 by decide),
      hl (sArr a) (sArr_lt ha), hl (sArr b) (sArr_lt hb), hl sW (by decide), hg.hdr.harr a ha,
      hg.hdr.harr b hb, hg.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `ltArr a b`, given the taint analysis's check of its first block. -/
theorem ltArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (ltArr a b)) fun _ _ => True :=
  cmp_ct (ptrsCmp_ok ha hb) hT (by taint_decide)

/-- `geArr a b`. -/
theorem geArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (geArr a b)) fun _ _ => True :=
  cmp_ct (ptrsCmp_ok ha hb) hT (by taint_decide)

/-- `eqArr a b`. -/
theorem eqArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x9 0, mov .x14 .x12]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (eqArr a b)) fun _ _ => True :=
  cmp_ct (ptrsEq_ok ha hb) hT (by taint_decide)

/-- Layouts of at least one word and fewer than `2^31`. -/
def GoodW1 (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

theorem two_goodW1 {s₁ s₂ : State} (h : Two GoodW1 s₁ s₂) : Two GoodW s₁ s₂ := two_mono (fun _ _ h => h.1) h

theorem tmpPtr_ok (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [ldh .x16 (sArr aTmp)]) s fun t => GoodW1 L t ∧ t.gpr .x16 = off L.B (slot L.w aTmp) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  exact WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w aTmp) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt (show aTmp < 8 by decide)), hg.ld hZ (sArr_lt (show aTmp < 8 by decide)),
      hg.hdr.harr aTmp (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h16, hm⟩, k⟩ => ⟨⟨GoodW.keep ⟨mi, hg, hZ⟩ hm (k.gpr .x0 (by decide)) k.wr, hw⟩, h16⟩

theorem or1_ok (L : Ws) (s : State) (h : GoodW1 L s ∧ s.gpr .x16 = off L.B (slot L.w aTmp)) :
    WP isa (.block [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16]) s (GoodW1 L) := by
  obtain ⟨⟨⟨mi, hg, hZ⟩, hw⟩, h16⟩ := h
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := L.w) (show aTmp < 8 by decide)) hZ
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (slot L.w aTmp))
      (word s.mem L.B (slot L.w aTmp) ||| 1))
    (by brun [h16, hg.scr.ld (show slot L.w aTmp + 8 ≤ L.Z by omega_arith), hg.scr.st (show slot L.w aTmp + 8 ≤ L.Z by omega_arith)]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := slot L.w aTmp) (word s.mem L.B (slot L.w aTmp) ||| 1) (by omega_arith)
  rw [← hm] at o
  exact ⟨⟨mi, hg.of_outside (by omega_arith) o k.wr (k.gpr .x0 (by decide)), hZ⟩, hw⟩

theorem ltP_eq : seqs (([.block [ldh .x16 (sArr aTmp)], .block [ld .x3 .x16, movi .x4 1,
    .logic .orr .x .x3 .x3 .x4, st .x3 .x16]] : List (Prog isa)) ++ ltArr aTmp aN) = .seq (.block [ldh .x16 (sArr aTmp)])
    (.seq (.block [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16]) (seqs (ltArr aTmp aN))) := rfl

/-- `ltP a` (`a ≠ aTmp`). -/
theorem ltP_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr aTmp)])
      hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aTmp aN ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₂).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (ltP a)) fun _ _ => True := by
  unfold ltP
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) ?_
  rw [ltP_eq]
  refine RelCT.seq (R := Two GoodW1) (two_post ((copyArr_ct (show aTmp < 8 by decide) ha hT₁).mono
      (fun _ _ h => two_goodW1 h) fun _ _ h => h) fun L s h => ?_)
    (RelCT.seq (two_piece [.x0] (fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1) (by taint_decide) tmpPtr_ok)
      (RelCT.seq (two_piece [.x16] (pins_of (fun L _ => off L.B (slot L.w aTmp)) fun L s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide) or1_ok)
        ((ltArr_ct (show aTmp < 8 by decide) (show aN < 8 by decide) hT₂).mono (fun _ _ h => two_goodW1 h)
          fun _ _ h => h)))
  obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  exact WP.mono (copyArr_ok hg hZ hw hw' (show aTmp < 8 by decide) ha (Ne.symm haT)) fun t ⟨_, ho, k⟩ =>
    ⟨⟨mi, hg.of_outside (by omega_arith) ho k.wr (k.gpr .x0 (by decide)), hZ⟩, hw, hw'⟩

/-- `isOdd a`. -/
theorem isOdd_ct {a : Nat} (ha : a < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr a)]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (isOdd a)) fun _ _ => True := by
  unfold isOdd
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x16 = off L.B (slot L.w a)) [.x0] pins_goodW hT
    fun L s ⟨mi, hg, hZ⟩ => ?_) (two_taint [.x16] (pins_of (fun L _ => off L.B (slot L.w a)) fun L s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide))
  exact WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w a))
    (by brun [hg.x0, hdr_enc (sArr_lt ha), hg.ld hZ (sArr_lt ha), hg.hdr.harr a ha]) rfl rfl rfl) fun t h => h.1

/-- `GoodW1` after a change of memory at offsets `o ≥ 128`. -/
theorem GoodW1.of_outside {L : Ws} {s t : State} (h : GoodW1 L s) {o n : Nat} (ho : 8 * 16 ≤ o)
    (hout : Outside L.B o n s.mem t.mem) (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : GoodW1 L t :=
  let ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  ⟨⟨mi, hg.of_outside ho hout hwr h0, hZ⟩, hw⟩

theorem GoodW1.keep {L : Ws} {s t : State} (h : GoodW1 L s) (hm : t.mem = s.mem) (h0 : t.gpr .x0 = s.gpr .x0)
    (hwr : t.wr = s.wr) : GoodW1 L t := ⟨GoodW.keep h.1 hm h0 hwr, h.2⟩

theorem pins_goodW1 : Pins GoodW1 [.x0] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

/-- A store of `x9` into the header slot `sl ≥ 16`. -/
theorem stF_ok {sl : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [sth .x9 sl]) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 hsl'
  have h8' := hdr_lt_slot L.w 8 hsl'
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (8 * sl)) (s.gpr .x9))
    (by brun [hg.x0, hdr_enc hsl', hg.scr.st (show 8 * sl + 8 ≤ L.Z by omega_arith)]) rfl rfl rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sl) (s.gpr .x9) (by omega_arith)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega_arith) o k.wr (k.gpr .x0 (by decide))

/-- `andF`. -/
theorem andF_ok (L : Ws) (s : State) (h : GoodW1 L s) : WP isa (.block andF) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 (show sF < 32 by decide)
  have h8' := hdr_lt_slot L.w 8 (show sF < 32 by decide)
  have eF : sF = 30 := rfl
  refine WP.mono (WP.keep [.x3, .x9] (Q := fun t' => ∃ v : BitVec 64, t'.mem = s.mem.writeW (off L.B (8 * sF)) v)
    (by unfold andF; brun [hg.x0, hdr_enc (show sF < 32 by decide), hg.scr.ld (show 8 * sF + 8 ≤ L.Z by omega_arith),
      hg.scr.st (show 8 * sF + 8 ≤ L.Z by omega_arith)]; exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sF) v (by omega_arith)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega_arith) o k.wr (k.gpr .x0 (by decide))

/-- `range a` (`a ≠ aTmp`). -/
theorem range_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aOne a ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr aTmp)])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aTmp aN ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₃).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (range a)) fun _ _ => True := by
  rw [show range a = ltArr aOne a ++ (.block [sth .x9 sF] :: (ltP a ++ [.block andF])) by simp [range, gt1]]
  refine RelCT.seqs_append (by simp [ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post ((ltArr_ct (show aOne < 8 by decide) ha hT₁).mono (fun _ _ h => two_goodW1 h) fun _ _ h => h)
      fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) ha) fun t ⟨_, hm, k⟩ =>
      GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr .x0 (by decide)) k.wr
  refine seqs_cons_ct (by simp [ltP, copyArr]) (RelCT.seq (R := Two GoodW1)
    (two_piece [.x0] pins_goodW1 (by taint_decide) (stF_ok (by decide) (by decide))) ?_)
  refine RelCT.seqs_append (by simp [ltP, copyArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post (ltP_ct ha haT hT₂ hT₃) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
    exact WP.mono (ltP_ok hg hZ hw hw' ha haT) fun t ⟨_, ho, k⟩ =>
      GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ (by omega_arith) ho k.wr (k.gpr .x0 (by decide))
  exact two_taint [.x0] pins_goodW1 (by taint_decide)

end VG.Proof.Ffdh.AArch64

end

end

/-!
# FFDH on AArch64: the scan for the first nonzero octet

`scan sp`, in the outer workspace, over the `p_len` octets `bs` at the
pointer in slot `sp`: `lead bs` iterations, each reading an octet and going
on while it is zero and not the last; the pointer and length of the octets
from `lead bs` into `sEp` and `sEl`, and that octet into `x3`
(`scan_ok`). The octets are public, and so is the number of iterations:
two runs on the same octets agree (`scan_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Impl.Bignum.Public (sK)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero ne_zero_iff)

/-- The loop's body. -/
def scanBody : List Instr :=
  [.ldrb .x4 .x1 0, movi .x7 0, movi .x8 1, .subs .x .x3 .x4 .x8, .csel .x .x5 .x7 .x8,
    movi .x9 2, .subs .x .x3 .x2 .x9, .csel .x .x6 .x8 .x7, .logic .and .x .x5 .x5 .x6, .add .x .x1 .x1 .x5,
    .sub .x .x2 .x2 .x5]

theorem scan_eq (sp : Nat) : seqs (scan sp) =
    .seq (.block [ldh .x1 sp, ldh .x2 sK]) (.seq (.loop (.block scanBody) (.nonzero .x .x5))
      (.block [sth .x1 sEp, sth .x2 sEl, .ldrb .x3 .x1 0])) := rfl

/-- The registers before iteration `j`. -/
def ScanAt (s₀ : State) (p : Addr) (n j : Nat) (t : State) : Prop :=
  t.gpr .x1 = off p j ∧ t.gpr .x2 = BitVec.ofNat 64 (n - j) ∧ t.mem = s₀.mem ∧
    Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] s₀ t

theorem scan_flag8 : ∀ (b : Byte) (d : Bool),
    ((if (!decide (BitVec.setWidth 64 (BitVec.setWidth 32 b) = 0)) = true then BitVec.setWidth 64 0#16
        else BitVec.setWidth 64 1#16) &&& if d = true then BitVec.setWidth 64 1#16 else BitVec.setWidth 64 0#16) =
      BitVec.ofNat 64 (decide (b = 0) && d).toNat := by
  decide

theorem scan_flag (b : Byte) {m : Nat} (hm : m < 2 ^ 64) :
    ((if (!decide (BitVec.setWidth 64 (BitVec.setWidth 32 b) = 0)) = true then BitVec.setWidth 64 0#16
        else BitVec.setWidth 64 1#16) &&&
      if decide (2 ≤ (BitVec.ofNat 64 m).toNat) = true then BitVec.setWidth 64 1#16 else BitVec.setWidth 64 0#16) =
      BitVec.ofNat 64 (decide (b = 0 ∧ 2 ≤ m)).toNat := by
  rw [scan_flag8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Bool.decide_and]

theorem subs_c2 (x : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.setWidth 64 (2#16))).toNat + (true).toNat) = decide (2 ≤ x.toNat) := by
  have h1 : (~~~(BitVec.setWidth 64 (2#16))).toNat = 2 ^ 64 - 3 := by decide
  rw [h1, Bool.toNat_true]
  have := x.isLt
  by_cases h : 2 ≤ x.toNat <;> simp [h] <;> omega_arith

/-- One iteration from `j ≤ lead bs`: `x5 := j < lead bs` (as 1 or 0), and the
pointer and the length moved by it. -/
theorem scanStep_ok {s₀ : State} {p : Addr} {bs : List Byte} (hl : bs.length < 2 ^ 32) (hne : bs ≠ [])
    (hrd : ∀ i < bs.length, InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 i) 1)
    (hval : ∀ i (h : i < bs.length), s₀.mem (p + BitVec.ofNat 64 i) = bs[i]) {j : Nat} (hj : j ≤ lead bs)
    {t : State} (ht : ScanAt s₀ p bs.length j t) :
    WP isa (.block scanBody) t fun t' => ScanAt s₀ p bs.length (min (j + 1) (lead bs)) t' ∧
      ((t'.gpr .x5).toNat ≠ 0 ↔ j + 1 ≠ lead bs + 1) := by
  have hL := lead_lt hne
  have hjl : j < bs.length := by omega_arith
  obtain ⟨h1, h2, hm, kt⟩ := ht
  have hld : InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 j) 1 := by rw [kt.rd, kt.wr]; exact hrd j hjl
  have hb : t.mem (p + BitVec.ofNat 64 j) = bs[j] := by rw [hm]; exact hval j hjl
  -- Whether the scan goes on.
  have hgo : (bs[j] = 0 ∧ 2 ≤ bs.length - j) ↔ j < lead bs := by
    constructor
    · rintro ⟨hz, h2⟩
      by_contra hc
      have hje : j = lead bs := by omega_arith
      subst hje
      exact lead_nonzero hne (by omega_arith) hz
    · intro hlt
      obtain ⟨_, hz⟩ := lead_zero j hlt
      exact ⟨hz, by omega_arith⟩
  generalize hc : decide (bs[j] = 0 ∧ 2 ≤ bs.length - j) = c
  have hv : (BitVec.ofNat 64 c.toNat).toNat ≠ 0 ↔ j < lead bs := by
    rw [← hgo]
    cases c
    · exact ⟨fun h => absurd (by decide) h, fun h => absurd h (of_decide_eq_false hc)⟩
    · exact ⟨fun _ => of_decide_eq_true hc, fun _ => by decide⟩
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] (Q := fun t' =>
      t'.gpr .x5 = BitVec.ofNat 64 c.toNat ∧ t'.gpr .x1 = off p (j + c.toNat) ∧
      t'.gpr .x2 = BitVec.ofNat 64 (bs.length - j) - BitVec.ofNat 64 c.toNat ∧ t'.mem = t.mem)
    (by
      unfold scanBody
      brun [h1, h2, hld, VG.Proof.MlKem.AArch64.read_one, hb, subs_one_c, subs_c2, scan_flag _ (show bs.length - j < 2 ^ 64 by omega_arith), hc]
      done)
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5, h1', h2', hm'⟩, k⟩ => ?_
  have hc' : c = decide (j < lead bs) := by rw [← hc]; exact decide_eq_decide.mpr hgo
  subst hc'
  refine ⟨⟨?_, ?_, hm'.trans hm, (kt.trans k).mono (by decide)⟩, ?_⟩
  · rw [h1']
    by_cases hlt : j < lead bs
    · rw [decide_eq_true hlt, Nat.min_eq_left (by omega_arith)]; rfl
    · rw [decide_eq_false hlt, Nat.min_eq_right (by omega_arith)]
      simp only [Bool.toNat_false, Nat.add_zero]; congr 1; omega_arith
  · rw [h2']
    by_cases hlt : j < lead bs
    · rw [decide_eq_true hlt, Nat.min_eq_left (by omega_arith), Bool.toNat_true,
        VG.Proof.Bignum.AArch64.ofNat_sub_one' (by omega_arith) (by omega_arith)]
      exact congrArg _ (by omega_arith)
    · rw [decide_eq_false hlt, Nat.min_eq_right (by omega_arith), Bool.toNat_false]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith
  · rw [h5, hv]; omega_arith

/-- `scan sp`, in the outer workspace, over the octets `bs` at the pointer in
slot `sp`, `p_len` of them. -/
theorem scan_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w) {sp : Nat} (hsp : sp < 32) {p : Addr}
    {bs : List Byte} (hp : word s.mem B (8 * sp) = p) (hk : word s.mem B (8 * sK) = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ []) (hl : bs.length < 2 ^ 32) (hsrc : Src s B Z p bs) :
    WP isa (seqs (scan sp)) s fun t =>
      word t.mem B (8 * sEp) = off p (lead bs) ∧ word t.mem B (8 * sEl) = BitVec.ofNat 64 (bs.length - lead bs) ∧
      t.gpr .x3 = BitVec.ofNat 64 (bs[lead bs]'(lead_lt hne)).toNat ∧
      Frm B [(8 * sEp, 8), (8 * sEl, 8)] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have hn := h.scr.nowrap
  have hL := lead_lt hne
  have hroom := h.room
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  rw [scan_eq]
  refine WP.seq (WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = p ∧ t.gpr .x2 = BitVec.ofNat 64 bs.length ∧
      t.mem = s.mem) (by brun [h.x0, hdr_enc hsp, hdr_enc (show sK < 32 by decide), h.ld hsp, h.ld (show sK < 32 by decide),
        hp, hk]) rfl rfl rfl) fun s₁ ⟨⟨h1₁, h2₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (count_loop (cr := .x5) (n := lead bs + 1) (by omega_arith)
    (fun k t => ScanAt s₁ p bs.length (min k (lead bs)) t)
    (fun k hk t ht => by
      have e : min k (lead bs) = k := Nat.min_eq_left (by omega_arith)
      rw [e] at ht
      refine WP.mono (scanStep_ok hl hne (fun i hi => by rw [k₁.rd, k₁.wr]; exact hsrc.rd i hi)
        (fun i hi => by rw [hm₁]; exact hsrc.val i hi) (by omega_arith) ht) fun t' ⟨ht', hc⟩ => ⟨ht', ?_⟩
      rw [hc])
    ⟨by rw [h1₁]; simp, by rw [h2₁]; simp, rfl, Keep.refl _ _⟩) fun s₂ h₂ => ?_)
  rw [Nat.min_eq_right (by omega_arith)] at h₂
  obtain ⟨h1₂, h2₂, hm₂, k₂⟩ := h₂
  have h0₂' : s₂.gpr .x0 = B := by rw [k₂.gpr .x0 (by decide), k₁.gpr .x0 (by decide)]; exact h.x0
  have hs₂ : Scr s₂ B Z := h.scr.congr (k₂.wr.trans k₁.wr)
  have hld : InRegions (s₂.rd ++ s₂.wr) (off p (lead bs)) 1 := by
    rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hsrc.rd _ hL
  have eEp : sEp = 23 := rfl
  have eEl : sEl = 24 := rfl
  have hEp := hdr_lt_slot w 8 (show sEp < 32 by decide)
  have hEl := hdr_lt_slot w 8 (show sEl < 32 by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW
      (off B (8 * sEl)) (BitVec.ofNat 64 (bs.length - lead bs)) ∧
      t.gpr .x3 = BitVec.setWidth 64 (BitVec.setWidth 32 (((s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW
      (off B (8 * sEl)) (BitVec.ofNat 64 (bs.length - lead bs))).read (off p (lead bs)) 1)))
    (by brun [h0₂', h1₂, h2₂, hdr_enc (show sEp < 32 by decide), hdr_enc (show sEl < 32 by decide),
      hs₂.st (d := 8 * sEp) (by omega_arith), hs₂.st (d := 8 * sEl) (by omega_arith), hld])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h3⟩, k⟩ => ?_
  have o₁ := writeW_outside s₂.mem B (d := 8 * sEp) (off p (lead bs)) (by omega_arith)
  have o₂ := writeW_outside (s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))) B (d := 8 * sEl)
    (BitVec.ofNat 64 (bs.length - lead bs)) (by omega_arith)
  have hout : Z ≤ ofs B (off p (lead bs)) := hsrc.out _ hL
  have hbyte : ((s₂.mem.writeW (off B (8 * sEp)) (off p (lead bs))).writeW (off B (8 * sEl))
      (BitVec.ofNat 64 (bs.length - lead bs))) (off p (lead bs)) = bs[lead bs] := by
    rw [o₂ _ (Or.inr (by omega_arith)), o₁ _ (Or.inr (by omega_arith)), hm₂, hm₁]; exact hsrc.val _ hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, o₂.word (by omega_arith) (by omega_arith)]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [h3, VG.Proof.MlKem.AArch64.read_one, hbyte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (bs[lead bs]'hL).isLt
    omega_arith
  · intro x hx
    rw [hm, o₂ x (hx (8 * sEl, 8) (by simp)), o₁ x (hx (8 * sEp, 8) (by simp)), hm₂, hm₁]
  · exact ((k₁.trans k₂).trans k).mono (by decide)

/-! ## Constant time -/

/-- The public data of `scan sp`: the workspace, the pointer and the octets. -/
structure ScanPub where
  B : Addr
  Z : Nat
  w : Nat
  p : Addr
  bs : List Byte

/-- `scan_ok`'s hypotheses. -/
def ScanPre (sp : Nat) (a : ScanPub) (s : State) : Prop :=
  Outer s a.B a.Z a.w ∧ word s.mem a.B (8 * sp) = a.p ∧ word s.mem a.B (8 * sK) = BitVec.ofNat 64 a.bs.length ∧
    a.bs ≠ [] ∧ a.bs.length < 2 ^ 32 ∧ Src s a.B a.Z a.p a.bs ∧ sp < 32

/-- Before iteration `j` of the loop. -/
def ScanJ (a : ScanPub) (j : Nat) (t : State) : Prop :=
  t.gpr .x1 = off a.p j ∧ t.gpr .x2 = BitVec.ofNat 64 (a.bs.length - j) ∧ a.bs ≠ [] ∧
    a.bs.length < 2 ^ 32 ∧ Src t a.B a.Z a.p a.bs ∧ t.gpr .x0 = a.B

theorem scanJ_step (a : ScanPub) (j : Nat) (t : State) (hj : j < lead a.bs + 1) (h : ScanJ a j t) :
    WP isa (.block scanBody) t fun t' => isa.eval (.nonzero .x .x5) t' = some (decide (j + 1 < lead a.bs + 1)) ∧
      (j + 1 < lead a.bs + 1 → ScanJ a (j + 1) t') ∧ (j + 1 = lead a.bs + 1 → ScanJ a (lead a.bs) t') := by
  obtain ⟨h1, h2, hne, hl, hsrc, h0⟩ := h
  refine WP.mono (scanStep_ok (s₀ := t) hl hne hsrc.rd hsrc.val (j := j) (by omega_arith)
    ⟨h1, h2, rfl, Keep.refl _ _⟩) fun t' ⟨⟨h1', h2', hm', k'⟩, hc⟩ => ?_
  have hs' : Src t' a.B a.Z a.p a.bs := hsrc.congr (by rw [hm']; exact InScr.refl _ _ _) k'.rd k'.wr
  have h0' : t'.gpr .x0 = a.B := (k'.gpr .x0 (by decide)).trans h0
  refine ⟨?_, fun hlt => ?_, fun he => ?_⟩
  · rw [eval_nonzero, ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr (by rw [hc]; omega_arith))
  · rw [Nat.min_eq_left (by omega_arith)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩
  · rw [Nat.min_eq_right (by omega_arith)] at h1' h2'
    exact ⟨h1', h2', hne, hl, hs', h0'⟩

/-- `scan sp` leaks the same in runs on the same octets. -/
theorem scan_ct {sp : Nat} {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sp, ldh .x2 sK]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0, .x1]) (.block [sth .x1 sEp, sth .x2 sEl, .ldrb .x3 .x1 0]) hc₂).isSome =
      true) :
    RelCT isa (Two (ScanPre sp)) (seqs (scan sp)) fun _ _ => True := by
  rw [scan_eq]
  refine RelCT.seq (R := Two fun a t => 0 < lead a.bs + 1 ∧ ScanJ a 0 t)
    (two_piece [.x0] (pins_of (fun a _ => a.B) fun a s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1.x0) hT₁ fun a s h => ?_)
    (RelCT.seq (R := Two fun a t => ScanJ a (lead a.bs) t)
      (two_loop (fun a => lead a.bs + 1)
        (two_taint [.x1, .x2] (pins_of (fun (p : ScanPub × Nat) r => if r = .x1 then off p.1.p p.2 else
            BitVec.ofNat 64 (p.1.bs.length - p.2)) fun p t h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.2.1
          · exact h.2.2.1) (by taint_decide))
        fun a j t hj h => scanJ_step a j t hj h)
      (two_taint [.x0, .x1] (pins_of (fun a r => if r = .x0 then a.B else off a.p (lead a.bs)) fun a t h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.2.2.2.2.2
        · exact h.1) hT₂))
  obtain ⟨hO, hp, hk, hne, hl, hsrc, hsp⟩ := h
  have l1 := hO.ld hsp
  have l2 := hO.ld (show sK < 32 by decide)
  exact WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = a.p ∧ t.gpr .x2 = BitVec.ofNat 64 a.bs.length ∧
      t.mem = s.mem)
    (by brun [hO.x0, hdr_enc hsp, hdr_enc (show sK < 32 by decide), l1, l2, hp, hk])
    rfl rfl rfl)
    fun t ⟨⟨h1, h2, hm⟩, k⟩ => ⟨by omega_arith, by rw [h1]; simp, by rw [h2]; simp, hne, hl,
      hsrc.congr (by rw [hm]; exact InScr.refl _ _ _) k.rd k.wr, (k.gpr .x0 (by decide)).trans hO.x0⟩

/-- What `scan` changes: two header slots. -/
theorem scanR_le : ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by decide

/-- A header slot other than those `scan` writes is outside what it changes. -/
theorem scanR_word {i : Nat} (h1 : i ≠ sEp) (h2 : i ≠ sEl) :
    ∀ r ∈ [(8 * sEp, 8), (8 * sEl, 8)], 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sEp sEl sFn at *
  exact ⟨by omega_arith, by omega_arith⟩

end VG.Proof.Ffdh.AArch64
