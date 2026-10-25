module

import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Gh
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint

/-!
# AES-GCM-SIV's interleaved loop: hashing a group between the rounds

`GEnv`: what the POLYVAL loads of a group need: its blocks at `rdx` (those
from `lo` on, which the loads to come read), as they are, and the powers in
the working space. `ghStep` is one load (`ghLoad_ok`), `ghFin` the reduction
of both lanes and their sum into `Y`. `QG` is what holds before the blocks
after round `j` of a batch, and `gq_ok` is `batch_ok`'s obligation for the
loads `gq base fin` place between the rounds, as for AES-GCM
(`Proof/Gcm/X86_64/Stitch/Group.lean`, whose products `accN` and `FinOk`
this uses).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (reduce_lanes combine_ok)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (ghLoad gq)
open VG.Proof.Gcm.X86_64.Stitch (accN accN_succ off2 offp ite_t ite_f yNew FinOk gRegs gRegs_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block)

structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → s.mem.readW (a + BitVec.ofNat 64 (16 * i)) 128 = X i
  pv : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  ina : ∀ k < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32
  inp : ∀ k < 8, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s : State} (h : GEnv s₀ lo a X P s) (hl : lo ≤ lo') : GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.yframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s s' : State} {rs : List XReg} (h : GEnv s₀ lo a X P s) (f : YFrame rs s s') : GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk l hl => by rw [f.mem]; exact h.pv k hk l hl, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk⟩

/-- One GHASH load, the `n`-th of the order `ord`. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {ord : Nat → Nat} {n : Nat} (hk : ord n < 8) (hlo : lo ≤ 2 * ord n) {s : State}
    (hE : GEnv s₀ lo a X P s) (hp : ∀ l < 2, prod (s.proj l) = accN ord X P yl l n)
    (hy : ∀ l < 2, s.lane .xmm2 l = yl l) :
    WP isa (.block (ghLoad (ord n))) s fun s' => GEnv s₀ lo a X P s' ∧
      (∀ l < 2, prod (s'.proj l) = accN ord X P yl l (n + 1)) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine WP.mono (ghLoad_ok hk s (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.yframe f', fun l hl => ?_, fun l hl => ?_, f'⟩
  · rw [p' l hl, hp l hl, accN_succ, hE.rdx, hE.r11, off2, offp, hE.xs _ (by omega) (by omega),
      hE.pv _ hk l hl, hy l hl]
    rfl
  · rw [f'.lane _ (by decide) l hl, hy l hl]

/-- The reduction of both lanes, and their sum into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {s : State}
    (hE : GEnv s₀ lo a X P s) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Vpclmul.reduce .xmm7 ++ Impl.Gcm.X86_64.Vpclmul.combine)) s fun s' =>
      GEnv s₀ lo a X P s' ∧ s'.lane .xmm2 0 = reduce (prod (s.proj 0)) ^^^ reduce (prod (s.proj 1)) ∧
      s'.lane .xmm2 1 = 0 ∧ YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (reduce_lanes s h1) fun s₁ ⟨r₁, f₁⟩ => WP.mono (combine_ok s₁) fun s' ⟨c', y', f'⟩ =>
    ⟨(hE.yframe f₁).yframe f', by rw [c', r₁ 0 (by decide), r₁ 1 (by decide)], y',
      f₁.comp f'⟩

/-! ## The GHASH work of a batch -/

/-- What holds before the blocks after round `j` of a batch. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block)
    (yl : Nat → Block) (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) (s : State) : Prop :=
  GEnv s₀ (lo j) a X P s ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
  (if fin ∧ 5 < j then s.lane .xmm2 0 = yNew ord X P yl ∧ s.lane .xmm2 1 = 0
   else (∀ l < 2, prod (s.proj l) = accN ord X P yl l (base + min (j - 1) 4)) ∧
     ∀ l < 2, s.lane .xmm2 l = yl l)

theorem QG.yframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j : Nat} {s s' : State} {rs : List XReg}
    (h : QG s₀ lo a X P yl ord base fin j s) (f : YFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QG s₀ lo a X P yl ord base fin j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => f.lane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 2, prod (s'.proj l) = prod (s.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.yframe f, fun l hl => by rw [k .xmm1 (by decide) l hl]; exact h1 l hl,
    ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1, by rw [k .xmm2 (by decide) 1 (by decide)]; exact h2.2⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl, fun l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {base : Nat} {fin : Bool}
    (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → ordE (base + j - 1) < 8 ∧ lo j ≤ 2 * ordE (base + j - 1))
    (hfin : fin = true → base = 4) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → QG s₀ lo a X P yl ordE base fin j s →
      WP isa (.block (gq base fin j)) s fun s' =>
        QG s₀ lo a X P yl ordE base fin (j + 1) s' ∧ YFrame gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    obtain ⟨hk, hlo⟩ := hrd j hj1 hl4
    rw [ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega] at h2
    have hn : base + (j - 1) = base + j - 1 := by omega
    rw [hn] at h2
    refine WP.mono (ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
        f'.mono (by decide)⟩
    rw [ite_f (by omega), show min (j + 1 - 1) 4 = j by omega, show base + j = base + j - 1 + 1 by omega]
    exact ⟨p', y'⟩
  · by_cases h5 : fin = true ∧ j = 5
    · -- The reduction.
      obtain ⟨hf, rfl⟩ := h5
      rw [ite_f (by omega)] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega, ite_false, hf, and_self, ite_true]
      have hb := hfin hf
      subst hb
      refine WP.mono (ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_t ⟨rfl, by omega⟩]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide)]; rfl, y1⟩
    · -- Nothing.
      have hg : gq base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false]
        rw [ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [ite_t hf] at h2; rw [ite_t ⟨hf.1, by omega⟩]; exact h2
      · rw [ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · -- `j = 5` with `fin` is the reduction.
          have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega⟩ h5
        · rw [ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega]; exact h2

end VG.Proof.AesGcmSiv.X86_64.Stitch
