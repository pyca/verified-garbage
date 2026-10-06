import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow

/-!
# Interleaved counter mode and GHASH with AVX-512: the GHASH of 48 blocks

`gq48_ok`: the GHASH work between the rounds of the three groups of
`StitchZ.body48` and `dbody48` (`gq48`): the pairs of loads of each group
(`pair_ok`) add up the products of its sixteen blocks with their powers
(`T g k l` for load `k` of group `g` in lane `l`), the first pair of the
first group with `Y`, and after round 6 of the third group the reduction
constant is reloaded and the four lanes reduced into `Y` (`fin_ok`). The
products so added and reduced are `GHASH` over the 48 blocks for the powers
`pow48` stores (`FinOk48`), which needs the field: `StitchZ/Ok.lean` proves
it.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre pp ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB ea_at)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (gq48 pair fin48 fin tab)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## The products of 48 blocks -/

/-- The input of load `k` of group `g` in lane `l`: block `16 g + 4 k + l`,
with `Y` (`yl l`) added to block 0. -/
def inp48 (X : Nat → Block) (yl : Nat → Block) (g k l : Nat) : Block :=
  (if g = 0 ∧ k = 0 then yl l else 0) ^^^ X (16 * g + 4 * k + l)

/-- Pair `i` is loads `pa i` and `pa i + 1` of group `i / 2`. -/
abbrev pa (i : Nat) : Nat := 2 * (i % 2)

/-- The products of lane `l` after the first `n` pairs, with the powers `T`. -/
def acc48 (X : Nat → Block) (T : Nat → Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => (p.acc (inp48 X yl (i / 2) (pa i) l) (T (i / 2) (pa i) l)).acc
    (inp48 X yl (i / 2) (pa i + 1) l) (T (i / 2) (pa i + 1) l)) Prod.zero

theorem acc48_succ (X : Nat → Block) (T : Nat → Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) :
    acc48 X T yl l (n + 1) = ((acc48 X T yl l n).acc (inp48 X yl (n / 2) (pa n) l) (T (n / 2) (pa n) l)).acc
      (inp48 X yl (n / 2) (pa n + 1) l) (T (n / 2) (pa n + 1) l) := by
  simp only [acc48, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after 48 blocks: the four lanes' products, each reduced, lanes 2 and
3 added to 0 and 1, and those two added. -/
abbrev yNew48 (X : Nat → Block) (T : Nat → Nat → Nat → Block) (yl : Nat → Block) : Block :=
  (reduceB (acc48 X T yl 0 6) ^^^ reduceB (acc48 X T yl 2 6)) ^^^
    (reduceB (acc48 X T yl 1 6) ^^^ reduceB (acc48 X T yl 3 6))

/-- What the products of 48 blocks add up to, for the powers `T`: `GHASH`
over them, from `Y` in lane 0. -/
def FinOk48 (H : Block) (T : Nat → Nat → Nat → Block) : Prop :=
  ∀ X yl, (∀ l, 1 ≤ l → l < 4 → yl l = 0) → yNew48 X T yl = ghashFrom H (yl 0) ((List.range 48).map X)

/-! ## Hashing three groups between their rounds -/

/-- The blocks from `lo` on (of 48) at `a`, the powers at `scratch`, the
reduction constant at `scratch + 832`, and the mask. -/
structure GEnv48 (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → Block) (T : Nat → Nat → Nat → Block)
    (s : State) : Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 48 → blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l
  pm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly
  ina : ∀ o : Nat, o + 64 ≤ 768 → InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 (o : Int)) 64
  inp : ∀ o : Nat, o + 64 ≤ 1024 → InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 (o : Int)) 64
  m0 : ∀ l < 4, s.zlane .xmm0 l = revMask

theorem GEnv48.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {s : State} (h : GEnv48 s₀ lo a X T s) (hl : lo ≤ lo') : GEnv48 s₀ lo' a X T s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv48.zframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {s s' : State} {rs : List XReg} (h : GEnv48 s₀ lo a X T s) (f : ZFrame rs s s') (h0 : .xmm0 ∉ rs) :
    GEnv48 s₀ lo a X T s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun g hg k hk l hl => by rw [f.mem]; exact h.pv g hg k hk l hl, fun l hl => by rw [f.mem]; exact h.pm l hl,
    fun o ho => by rw [f.rd, f.wr]; exact h.ina o ho, fun o ho => by rw [f.rd, f.wr]; exact h.inp o ho,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.m0 l hl⟩

/-- The pairs done after round `j` of group `b`. -/
abbrev np (b j : Nat) : Nat := 2 * b + (if j ≤ 1 then 0 else if j ≤ 3 then 1 else 2)

/-- What holds before the blocks after round `j` of group `b`: the products
of the pairs done (or, before the first, `Y` in `zmm2`), or, after the
reduction, the new `Y`. -/
def QG48 (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → Block) (T : Nat → Nat → Nat → Block)
    (yl : Nat → Block) (b j : Nat) (s : State) : Prop :=
  GEnv48 s₀ (lo j) a X T s ∧
  (if b = 2 ∧ 6 < j then s.zlane .xmm2 0 = yNew48 X T yl ∧ ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0
   else (0 < np b j → ∀ l < 4, prod (s.zproj l) = acc48 X T yl l (np b j)) ∧
     (np b j = 0 → ∀ l < 4, s.zlane .xmm2 l = yl l))

/-- The registers the GHASH work writes. -/
abbrev gRegs48 : List XReg := [.xmm12, .xmm7, .xmm13, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11]

theorem gRegs48_ok : ∀ r ∈ gRegs48, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG48.zframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {yl : Nat → Block} {b j : Nat} {s s' : State} {rs : List XReg}
    (h : QG48 s₀ lo a X T yl b j s) (f : ZFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QG48 s₀ lo a X T yl b j s' := by
  obtain ⟨hE, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.zframe f (fun h => hrs _ h (by decide)), ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1,
      fun l h1 h4 => by rw [k .xmm2 (by decide) l h4]; exact h2.2 l h1 h4⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
      fun hj l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 hj l hl⟩

theorem off48 (a : Addr) (g k l : Nat) :
    a + BitVec.ofInt 64 ((256 * g + 64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (16 * (16 * g + 4 * k + l)) := by
  rw [ofInt_add_ofNat, show 256 * g + 64 * k + 16 * l = 16 * (16 * g + 4 * k + l) by omega]

/-- A pair, the `i`-th of the 48 blocks, in group `b = i / 2`. -/
theorem pairStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {yl : Nat → Block} {i ka g : Nat} {first : Bool} (hka : ka = pa i) (hg' : g = i / 2)
    (hf : first = decide (i = 0)) (hi : i < 6) (hlo : lo ≤ 16 * (i / 2) + 4 * pa i) {s : State}
    (hE : GEnv48 s₀ lo a X T s) (hp : 0 < i → ∀ l < 4, prod (s.zproj l) = acc48 X T yl l i)
    (hy : i = 0 → ∀ l < 4, s.zlane .xmm2 l = yl l) :
    WP isa (.block (pair ka (ka + 1) g first)) s fun s' => GEnv48 s₀ lo a X T s' ∧
      (∀ l < 4, prod (s'.zproj l) = acc48 X T yl l (i + 1)) ∧ ZFrame gRegs48 s s' := by
  subst hka hg' hf
  have hg : i / 2 < 3 := by omega
  have hpa : pa i ≤ 2 := by simp only [pa]; omega
  have hk : pa i + 1 < 4 := by omega
  refine WP.mono (pair_ok (ka := pa i) (kb := pa i + 1) (g := i / 2) (decide (i = 0)) s hE.m0
      (by rw [hE.rdx]; exact hE.ina _ (by omega)) (by rw [hE.rdx]; exact hE.ina _ (by omega))
      (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega))
      (by rw [hE.r11]; exact hE.inp _ (by simp only [tab]; omega)))
    fun s' ⟨p', f'⟩ => ⟨hE.zframe f' (by decide), fun l hl => ?_, f'⟩
  rw [p' l hl, acc48_succ, hE.rdx, hE.r11, off48, off48, ofInt_add_ofNat, ofInt_add_ofNat,
    hE.xs _ (by omega) (by omega), hE.xs _ (by omega) (by omega), hE.pv _ hg _ (by omega) l hl,
    hE.pv _ hg _ hk l hl]
  by_cases h0 : i = 0
  · subst h0
    simp only [decide_true, ite_true, inp48, show (0 : Nat) / 2 = 0 from rfl, pa, Nat.zero_mod, Nat.mul_zero,
      and_self, Nat.zero_add, hy rfl l hl,
      show acc48 X T yl l 0 = Prod.zero from rfl, true_and, Nat.one_ne_zero, ite_false, Stitch.zero_xor_b]
  · have c1 : ¬ (i / 2 = 0 ∧ pa i = 0) := by simp only [pa]; omega
    have c2 : ¬ (i / 2 = 0 ∧ pa i + 1 = 0) := by omega
    simp only [h0, decide_false, Bool.false_eq_true, ite_false, hp (by omega) l hl, inp48, c1, c2,
      Stitch.zero_xor_b]

/-- The reduction constant reloaded, and the four lanes reduced into `Y`. -/
theorem fin48_ok {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block} {s : State}
    (hE : GEnv48 s₀ lo a X T s) :
    WP isa (.block fin48) s fun s' => GEnv48 s₀ lo a X T s' ∧
      s'.zlane .xmm2 0 =
        (reduceB (prod (s.zproj 0)) ^^^ reduceB (prod (s.zproj 2))) ^^^
          (reduceB (prod (s.zproj 1)) ^^^ reduceB (prod (s.zproj 3))) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧ ZFrame gRegs48 s s' := by
  let q := s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((832 : Nat) : Int)) 64 := by
    rw [hE.r11]; exact hE.inp 832 (by decide)
  rw [fin48, WP.block_cons_iff]
  refine ⟨ldZ s .xmm1 q, by simp only [isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have h1 : ∀ l < 4, (ldZ s .xmm1 q).zlane .xmm1 l = poly := fun l hl => by
    rw [ldZ_zlane _ _ _ hl, ofInt_add_ofNat, hE.r11]; exact hE.pm l hl
  have f₁ : ZFrame [.xmm1] s (ldZ s .xmm1 q) :=
    ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ldZ_zlane_ne _ _ (fun h => hr (by simp [h])) hl⟩
  have kp : ∀ l < 4, prod ((ldZ s .xmm1 q).zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, ldZ_zlane_ne _ _ (show XReg.xmm8 ≠ .xmm1 by decide) hl,
      ldZ_zlane_ne _ _ (show XReg.xmm9 ≠ .xmm1 by decide) hl, ldZ_zlane_ne _ _ (show XReg.xmm10 ≠ .xmm1 by decide) hl]
  refine WP.mono (fin_ok _ h1) fun s' ⟨y0, y1, f'⟩ =>
    ⟨(hE.zframe f₁ (by decide)).zframe f' (by decide), ?_, y1, (f₁.comp f').mono (by decide)⟩
  rw [y0, kp 0 (by decide), kp 1 (by decide), kp 2 (by decide), kp 3 (by decide)]

/-- `batch_ok`'s obligation for the GHASH work between the rounds of group
`b`: the pairs after rounds 1 and 3 (whose blocks are not yet decrypted:
`lo`), and, for the third group, the reduction after round 6. -/
theorem gq48_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {T : Nat → Nat → Nat → Block}
    {yl : Nat → Block} {b : Nat} (hb : b < 3) (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd1 : lo 1 ≤ 16 * b) (hrd3 : lo 3 ≤ 16 * b + 8) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (Stitch.nr s₀) (Stitch.sch s₀) s → QG48 s₀ lo a X T yl b j s →
      WP isa (.block (gq48 b j)) s fun s' => QG48 s₀ lo a X T yl b (j + 1) s' ∧ ZFrame gRegs48 s s' := by
  intro j hj1 hj9 s _ ⟨hE, h2⟩
  by_cases h1 : j = 1
  · subst h1
    rw [ite_f (by omega)] at h2
    rw [show gq48 b 1 = pair 0 (0 + 1) b (decide (b = 0)) from rfl]
    have n1 : np b 1 = 2 * b := rfl
    refine WP.mono (pairStep (yl := yl) (i := 2 * b) (by simp only [pa]; omega) (by omega)
        (by simp only [decide_eq_decide]; omega) (by omega) (by simp only [pa]; omega) hE
        (fun h => by rw [← n1]; exact h2.1 (by omega)) (fun h => by rw [← n1] at h; exact h2.2 h))
      fun s' ⟨hE', p', f'⟩ => ⟨⟨hE'.mono (hmono 1), ?_⟩, f'⟩
    rw [ite_f (by omega)]
    have n2 : np b (1 + 1) = 2 * b + 1 := rfl
    exact ⟨fun _ => by rw [n2]; exact p', fun h => absurd h (by omega)⟩
  by_cases h3 : j = 3
  · subst h3
    rw [ite_f (by omega)] at h2
    rw [show gq48 b 3 = pair 2 (2 + 1) b false from rfl]
    have n3 : np b 3 = 2 * b + 1 := rfl
    refine WP.mono (pairStep (yl := yl) (i := 2 * b + 1) (by simp only [pa]; omega) (by omega)
        (by rw [eq_comm, decide_eq_false_iff_not]; omega) (by omega) (by simp only [pa]; omega)
        (hE.mono (Nat.le_refl _))
        (fun _ => by rw [← n3]; exact h2.1 (by omega)) (fun h => absurd h (by omega)))
      fun s' ⟨hE', p', f'⟩ => ⟨⟨hE'.mono (hmono 3), ?_⟩, f'⟩
    rw [ite_f (by omega)]
    have n4 : np b (3 + 1) = 2 * b + 1 + 1 := rfl
    exact ⟨fun _ => by rw [n4]; exact p', fun h => absurd h (by omega)⟩
  by_cases h6 : b = 2 ∧ j = 6
  · obtain ⟨rfl, rfl⟩ := h6
    rw [ite_f (by decide)] at h2
    rw [show gq48 2 6 = fin48 from rfl]
    refine WP.mono (fin48_ok hE) fun s' ⟨hE', y0, y1, f'⟩ => ⟨⟨hE'.mono (hmono 6), ?_⟩, f'⟩
    rw [ite_t (by decide)]
    have p := h2.1 (by decide)
    rw [show np 2 6 = 6 from rfl] at p
    refine ⟨by rw [y0, p 0 (by decide), p 1 (by decide), p 2 (by decide), p 3 (by decide)], y1⟩
  · -- Nothing.
    have hg : gq48 b j = [] := by
      simp only [gq48, h1, h3, ite_false]
      split
      · rename_i h; exact absurd h h6
      · rfl
    rw [hg]
    refine WP.block_nil ⟨⟨hE.mono (hmono j), ?_⟩, ZFrame.refl _ _⟩
    have hnp : np b (j + 1) = np b j := by
      rcases (by omega : j = 2 ∨ 4 ≤ j) with rfl | h4
      · rfl
      · simp only [np, show ¬ (j + 1 ≤ 1) by omega, show ¬ (j + 1 ≤ 3) by omega, show ¬ (j ≤ 1) by omega,
          show ¬ (j ≤ 3) by omega, ite_false]
    by_cases hr : b = 2 ∧ 6 < j
    · rw [ite_t (by omega)]; rw [ite_t hr] at h2; exact h2
    · rw [ite_f (by omega)]; rw [ite_f hr] at h2; rw [hnp]; exact h2

end VG.Proof.Gcm.X86_64.StitchZ
