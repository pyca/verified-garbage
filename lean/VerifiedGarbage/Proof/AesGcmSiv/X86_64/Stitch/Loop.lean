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
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesGcmSiv.X86_64.Stitch.Group`, which only this module used -/

section

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
  · rw [p' l hl, hp l hl, accN_succ, hE.rdx, hE.r11, off2, offp, hE.xs _ (by omega_using [hlo]) (by omega_using [hk, hl]),
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
  obtain k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => f.lane r (fun h => hrs r h hr) l hl
  obtain kp : ∀ l < 2, prod (s'.proj l) = prod (s.proj l) := fun l hl => by
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
    rw [ite_f (by omega_using [hl4])] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega_using [hl4]] at h2
    obtain hn : base + (j - 1) = base + j - 1 := by omega_using [hj1]
    rw [hn] at h2
    refine WP.mono (ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
        f'.mono (by decide)⟩
    rw [ite_f (by omega_using [hl4]), show min (j + 1 - 1) 4 = j by omega_using [hl4], show base + j = base + j - 1 + 1 by omega_using [hj1]]
    exact ⟨p', y'⟩
  · by_cases h5 : fin = true ∧ j = 5
    · -- The reduction.
      obtain ⟨hf, rfl⟩ := h5
      rw [ite_f (by omega_using [])] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega_using [], ite_false, hf, and_self, ite_true]
      obtain hb := hfin hf
      subst hb
      refine WP.mono (ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_t ⟨rfl, by omega_using []⟩]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide)]; rfl, y1⟩
    · -- Nothing.
      obtain hg : gq base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega_using [hl4], ite_false]
        rw [ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [ite_t hf] at h2; rw [ite_t ⟨hf.1, by omega_using [hl4]⟩]; exact h2
      · rw [ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · -- `j = 5` with `fin` is the reduction.
          have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega_using [hl4, this]⟩ h5
        · rw [ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega_using [hl4]]; exact h2

end VG.Proof.AesGcmSiv.X86_64.Stitch

end

end


/-!
# AES-GCM-SIV's interleaved loop: the body

`EInv s₀ P e s`: `e` groups of sixteen blocks are deciphered (`AInv`), the
plaintext of the first `e - 1` absorbed into `Y` (in `xmm2`), the powers `P`
in the working space; `rdx` points to group `e - 1`, the next to hash.
`body_ok`: a body deciphers group `e` (two batches, `batch_ok`) while it
hashes group `e - 1` between their rounds (`gq_ok`), which they do not write
(`QG.data`), as AES-GCM's encryption does (`Proof/Gcm/X86_64/Stitch/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (batch gA gB body gq)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr FinOk gRegs gRegs_ok ite_t ite_f nextE_ok
  ghash_append16)
open VG.Proof.Aes.X86_64.AesNi (run_sep)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block ghashFrom)

/-- A block's 16 bytes, as POLYVAL's field element. -/
theorem readW_ofBytes (m : Mem) (a : Addr) : m.readW a 128 = Spec.GcmSiv.ofBytes (bytesAt m a 16) := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-! ## The POLYVAL state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  obtain kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    ⟩, fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega_using [ha])
    rw [e, hf.readW (r := ⟨bAddr s₀ (16 * g + i), 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega_using [hg, hi']) hc (hsep i hi hi') h₁ h₂) (by decide)]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_using [hk, hl]) (by omega_using [hk, hl]))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_using [hc]))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map fun k => Spec.GcmSiv.ofBytes (ctb s₀ k))
  y1 : s.lane .xmm2 1 = 0

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => Spec.GcmSiv.ofBytes (ctb s₀ (16 * (e - 1) + i))
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  obtain hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          readW_ofBytes, hI.a.blocks _ (by omega_arith)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_arith, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith)) }
  obtain hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  obtain hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hsepA : ∀ c, 16 * e ≤ c → ∀ i, 0 ≤ i → i < 16 → ¬ (c ≤ 16 * (e - 1) + i ∧ 16 * (e - 1) + i < c + 8) :=
    fun c hc i _ hi => by omega_arith
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (batch_ok hp gA gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 0 false)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega_arith) (by omega_arith) ha (hsepA _ (Nat.le_refl _)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega_arith) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  obtain hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (dp s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hQ₂' : QG s₀ (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (batch_ok hp gB gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 4 true)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega_arith) (by omega_arith) ha (hsepA _ (by omega_arith)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega_arith) hA₂ hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  -- The memory of the powers is kept.
  obtain dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨bAddr s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  obtain keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
        hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide), f₁.mem]
  obtain gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (fun h => hg' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> decide)) l hl]
  obtain hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega_arith]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  obtain hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  refine ⟨⟨hA', by omega_arith, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega_arith)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega_arith, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega_arith, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith), show e + 1 - 1 = e by omega_arith]

end VG.Proof.AesGcmSiv.X86_64.Stitch
