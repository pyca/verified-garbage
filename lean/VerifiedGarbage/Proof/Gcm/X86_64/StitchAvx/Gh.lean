import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Aes
import VerifiedGarbage.Proof.Framework.X86_64.Lane0

/-!
# Interleaved counter mode and GHASH in AVX: the GHASH work

`ghLoad_ok`: `ghLoad k` loads the power at `scratch + 16 k` into `xmm12` and
block `k` at `rdx + 16 k` into `xmm7`, and adds their product to the
product's lower lanes, as the SSE instructions it stands for do
(`WP.lane0`, `Pclmul.ldrev_ok`, `acc_ok`). `accN` is the product after the
first `n` loads of an order, `GEnv` what the loads need, `ghStep` one load
and `ghFin` the reduction into `Y`. The GHASH work between the rounds of a
batch is `gq ord base fin`; `QG` is what holds before the blocks after round
`j`, and `gq_ok` is the obligation of `batch_ok` for it.

Nothing here computes in the field: what the products add up to is
`Proof/Gcm/X86_64/StitchAvx/Ok.lean`'s.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod Only ldrev_ok pxor72_ok acc_ok reduce_ok)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (ghLoad aregs gq)
open VG.Proof.Gcm.X86_64.Stitch (SPre pp dp nb pR bAddr in_sub in_sub_int in_rdwr addr_eq)
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame run_sep)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt)

/-! ## A load -/

/-- The SSE instructions of `ghLoad k`. -/
def ghSse (k : Nat) : List Instr :=
  .movdquLoad .xmm12 (at_ .r11 (16 * k)) ::
    ([.movdquLoad .xmm7 (at_ .rdx (16 * k)), .xop (.bin .pshufb .xmm7 .xmm0)] ++
      ((if k = 0 then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12))

theorem lane0_ghLoad (k : Nat) : lane0Block (ghLoad k) = some (ghSse k) := by
  unfold ghLoad ghSse; split <;> rfl

/-- The registers a load writes. -/
abbrev gl : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11]

theorem ghLoad_dst (k : Nat) : ∀ r, r ∉ gl → r ∉ (ghLoad k).filterMap vdst := by
  intro r hr
  simp only [gl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  unfold ghLoad
  split <;> simp [Impl.Gcm.X86_64.StitchAvx.acc, vdst, h1, h2, h3, h4, h5, h6]

theorem ghLoad_noGpr (k : Nat) : (ghLoad k).all noGpr = true := by
  unfold ghLoad; split <;> rfl

theorem ghSse_ok (k : Nat) (t : State) (h0 : t.xmm .xmm0 = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (ghSse k)) t fun t' =>
      prod t' = (prod t).acc
        ((if k = 0 then t.xmm .xmm2 else 0) ^^^ blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧
      Only gl t t' := by
  let t₁ := t.setXmm .xmm12 (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128)
  have o₁ : Only [.xmm12] t t₁ := ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [t₁, State.setXmm, hr]⟩
  rw [ghSse, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load128, Pclmul.ea_at, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdx (16 * k) t₁ (by decide) (by rw [o₁.xmm _ (by decide)]; exact h0)
    (by rw [o₁.gpr _ (by decide), o₁.rd, o₁.wr]; exact hin)) fun t₂ ⟨e₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [o₁.gpr _ (by decide), o₁.mem] at e₂
  have fin : ∀ t₃, Only [.xmm7] t₂ t₃ → t₃.xmm .xmm7 =
      (if k = 0 then t.xmm .xmm2 else 0) ^^^ blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) →
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12)) t₃ fun t' =>
        prod t' = (prod t).acc
          ((if k = 0 then t.xmm .xmm2 else 0) ^^^ blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
          (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧ Only gl t t' := by
    intro t₃ o₃ e₃
    refine WP.mono (acc_ok .xmm7 .xmm12 t₃ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩
    · rw [p', e₃, o₃.xmm _ (by decide), o₂.xmm _ (by decide), o₃.prod (by decide) (by decide) (by decide),
        o₂.prod (by decide) (by decide) (by decide), o₁.prod (by decide) (by decide) (by decide)]
      simp [t₁, State.setXmm]
    · exact ((o₁₂.trans o₃).trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with ((h | h) | h) | (h | h | h | h) <;> simp [h]
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true] at fin ⊢
    rw [WP.block_append_iff]
    refine WP.mono (pxor72_ok t₂) fun t₃ ⟨e₃, o₃⟩ => fin t₃ o₃ ?_
    have h2 : t₂.xmm .xmm2 = t.xmm .xmm2 := by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide)]
    rw [e₃, e₂, h2]
  · simp only [hk, ite_false, List.nil_append] at fin ⊢
    exact fin t₂ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by rw [e₂]; simp)

/-- The power at `scratch + 16 k` into `xmm12`, and block `k` at `rdx + 16 k`
(with `Y` added to block 0) added to the product with it. -/
theorem ghLoad_ok (k : Nat) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hpin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (ghLoad k)) s fun s' =>
      prod (s'.proj 0) = (prod (s.proj 0)).acc
        ((if k = 0 then s.lane .xmm2 0 else 0) ^^^ blockAt s.mem (s.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
        (s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧
      YFrame gl s s' := by
  refine WP.mono (WP.lane0 (lane0_ghLoad k) (ghSse_ok k (s.proj 0) (by simpa using h0) hin hpin))
    fun s' ⟨⟨p, o⟩, hi, hg⟩ => ⟨p, ?_⟩
  have hg := hg (ghLoad_noGpr k)
  refine ⟨hg, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · exact hi r (ghLoad_dst k r hr)

/-! ## The products of a group -/

/-- The input of the `k`-th load: block `k`, with `Y` added to block 0. -/
def inp (X : Nat → Block) (y : Block) (k : Nat) : Block := (if k = 0 then y else 0) ^^^ X k

/-- The product after the first `n` loads, in the order `ord`. -/
def accN (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Block) (y : Block) (n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (inp X y (ord i)) (P (ord i))) Prod.zero

theorem accN_succ (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Block) (y : Block) (n : Nat) :
    accN ord X P y (n + 1) = (accN ord X P y n).acc (inp X y (ord n)) (P (ord n)) := by
  simp only [accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after the sixteen blocks of a group. -/
abbrev yNew (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Block) (y : Block) : Block :=
  reduce (accN ord X P y 16)

/-- What the loads of a group need: its blocks at `rdx` (those from `lo` on,
which the loads to come read), the powers in the working space, and the
mask. -/
structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → Block) (P : Nat → Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  ina : ∀ k < 16, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16
  inp : ∀ k < 16, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16
  m0 : s.lane .xmm0 0 = revMask

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block}
    {s : State} (h : GEnv s₀ lo a X P s) (hl : lo ≤ lo') : GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.yframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block}
    {s s' : State} {rs : List XReg} (h : GEnv s₀ lo a X P s) (f : YFrame rs s s') (h0 : .xmm0 ∉ rs) :
    GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk => by rw [f.mem]; exact h.pv k hk, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk, by rw [f.lane _ h0 0 (by decide)]; exact h.m0⟩

theorem ofInt_add (a : Addr) (k : Nat) : a + BitVec.ofInt 64 ((16 * k : Nat) : Int) = a + BitVec.ofNat 64 (16 * k) := by
  rw [BitVec.ofInt_natCast]

/-- The product of the lower lanes, kept by a frame without `xmm8`–`xmm10`. -/
theorem prod_yframe {s s' : State} {rs : List XReg} (f : YFrame rs s s') (h8 : .xmm8 ∉ rs) (h9 : .xmm9 ∉ rs)
    (h10 : .xmm10 ∉ rs) : prod (s'.proj 0) = prod (s.proj 0) := by
  simp only [prod, State.proj_xmm, f.lane _ h8 0 (by decide), f.lane _ h9 0 (by decide),
    f.lane _ h10 0 (by decide)]

/-- One GHASH load, the `n`-th of the order `ord`. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block}
    {y : Block} {ord : Nat → Nat} {n : Nat} (hk : ord n < 16) (hlo : lo ≤ ord n) {s : State}
    (hE : GEnv s₀ lo a X P s) (hp : prod (s.proj 0) = accN ord X P y n) (hy : s.lane .xmm2 0 = y) :
    WP isa (.block (ghLoad (ord n))) s fun s' => GEnv s₀ lo a X P s' ∧
      prod (s'.proj 0) = accN ord X P y (n + 1) ∧ s'.lane .xmm2 0 = y ∧ YFrame gl s s' := by
  refine WP.mono (ghLoad_ok _ s hE.m0 (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.yframe f' (by decide), ?_, by rw [f'.lane _ (by decide) 0 (by decide), hy], f'⟩
  rw [p', hp, accN_succ, hE.rdx, hE.r11, ofInt_add, ofInt_add, hE.xs _ hlo hk, hE.pv _ hk, hy]
  rfl

/-- The reduction into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block} {s : State}
    (hE : GEnv s₀ lo a X P s) (h1 : s.lane .xmm1 0 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.StitchAvx.reduce .xmm2)) s fun s' =>
      GEnv s₀ lo a X P s' ∧ s'.lane .xmm2 0 = reduce (prod (s.proj 0)) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.reduce .xmm2) rfl
    (reduce_ok .xmm2 (s.proj 0) (by decide) (by decide) (by decide) (by decide) (by simpa using h1)))
    fun s' ⟨⟨r, o⟩, hi, hg⟩ => ?_
  have f : YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' :=
    ⟨hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr, fun r hr l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · simpa using o.xmm r hr
      · refine hi r ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h8, h9, h10, h11, h2⟩ := hr
        simp [Impl.Gcm.X86_64.StitchAvx.reduce, Impl.Gcm.X86_64.StitchAvx.fold, vdst, h8, h9, h10, h11, h2]⟩
  exact ⟨hE.yframe f (by decide), by simpa using r, f⟩

theorem ite_t {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : ite c a b = a := by
  simp [h]

theorem ite_f {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : ite c a b = b := by
  simp [h]

/-! ## The GHASH work of a batch -/

/-- What holds before the blocks after round `j` of a batch. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → Block) (P : Nat → Block)
    (y : Block) (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) (s : State) : Prop :=
  GEnv s₀ (lo j) a X P s ∧ s.lane .xmm1 0 = poly ∧
  (if fin ∧ 5 < j then s.lane .xmm2 0 = yNew ord X P y
   else prod (s.proj 0) = accN ord X P y (base + min (j - 1) 4) ∧ s.lane .xmm2 0 = y)

/-- The registers the GHASH work of a batch writes. -/
abbrev gRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

theorem gRegs_ok : ∀ r ∈ gRegs, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG.yframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block}
    {y : Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j : Nat} {s s' : State} {rs : List XReg}
    (h : QG s₀ lo a X P y ord base fin j s) (f : YFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QG s₀ lo a X P y ord base fin j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), s'.lane r 0 = s.lane r 0 :=
    fun r hr => f.lane r (fun h => hrs r h hr) 0 (by decide)
  have kp : prod (s'.proj 0) = prod (s.proj 0) := by
    simp only [prod, State.proj_xmm, k .xmm8 (by decide), k .xmm9 (by decide), k .xmm10 (by decide)]
  refine ⟨hE.yframe f (fun h => hrs _ h (by decide)), by rw [k .xmm1 (by decide)]; exact h1, ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    rw [k .xmm2 (by decide)]; exact h2
  · rw [ite_f (by assumption)] at h2
    exact ⟨by rw [kp]; exact h2.1, by rw [k .xmm2 (by decide)]; exact h2.2⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Block}
    {y : Block} {ord : Nat → Nat} {base : Nat} {fin : Bool}
    (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → ord (base + j - 1) < 16 ∧ lo j ≤ ord (base + j - 1))
    (hfin : fin = true → base = 12) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (Stitch.nr s₀) (Stitch.sch s₀) s → QG s₀ lo a X P y ord base fin j s →
      WP isa (.block (gq ord base fin j)) s fun s' =>
        QG s₀ lo a X P y ord base fin (j + 1) s' ∧ YFrame gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    obtain ⟨hk, hlo⟩ := hrd j hj1 hl4
    rw [ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega, show base + (j - 1) = base + j - 1 by omega] at h2
    refine WP.mono (ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), by rw [f'.lane _ (by decide) 0 (by decide)]; exact h1, ?_⟩,
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
      refine WP.mono (ghFin hE h1) fun s' ⟨hE', y0, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), by rw [f'.lane _ (by decide) 0 (by decide)]; exact h1, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_t ⟨rfl, by omega⟩, y0, h2.1]; rfl
    · -- Nothing.
      have hg : gq ord base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false]
        rw [ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [ite_t hf] at h2; rw [ite_t ⟨hf.1, by omega⟩]; exact h2
      · rw [ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega⟩ h5
        · rw [ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega]; exact h2

/-- The GHASH state, kept by the data a batch writes. -/
theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Block} {y : Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 4 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 4))
    {t t' : State} (h : QG s₀ lo a X P y ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 64⟩] t.mem t'.mem) : QG s₀ lo a X P y ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : prod (t'.proj 0) = prod (t.proj 0) := by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) 0 (by decide),
      hlane .xmm9 (by decide) (by decide) 0 (by decide), hlane .xmm10 (by decide) (by decide) 0 (by decide)]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact hE.m0⟩,
    by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h1, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk
  · split
    · rw [ite_t (by assumption)] at h2
      rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2
    · rw [ite_f (by assumption)] at h2
      exact ⟨by rw [kp]; exact h2.1, by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.2⟩

end VG.Proof.Gcm.X86_64.StitchAvx
