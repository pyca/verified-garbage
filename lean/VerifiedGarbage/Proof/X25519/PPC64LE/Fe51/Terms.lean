module
-- separate module: the five-limb field's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.X25519.PPC64LE.Fe51
public import VerifiedGarbage.Proof.X25519.PPC64LE.Fe51.Limbs
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE, five 51-bit limbs: products and their reduction

`terms ts` adds each product of `ts` to its column's two sums, `lo k` and
`hi k` (`term_ok`, and `terms_ok` by induction on the list): `Acc c n s`
says that the columns with a product so far (`0 < n k`) hold
`c k = lo k + 2⁵¹ hi k`, the sum of `n k` products below `2¹¹²`. `tail o`
stores at `o` an element congruent to the columns' number (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE.Fe51
open VG.Spec.X25519 (P)

/-! ## What code keeps -/

/-- `Rest` for a block whose instructions write only `ws`, by evaluation. -/
theorem WP.rest {is : List Instr} {s : State} {Q : State → Prop} (ws : List Reg)
    (h : WP isa (.block is) s Q) (hc : writesOnly ws (.block is) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ Rest ws s s' := by
  obtain ⟨t, s', he, hq, hk⟩ := WP.keep ws h hc rfl
  exact ⟨t, s', he, hq, hk.1, hk.2.1, hk.2.2, Exec.sp he⟩

/-! ## Elements -/

/-- Limb `k` of the element at `o`. -/
abbrev lw (m : Mem) (B : Addr) (o k : Nat) : Nat := dw m B (o + 8 * k)

/-- The number of the element at `o`. -/
def V5 (m : Mem) (B : Addr) (o : Nat) : Nat := val5 (lw m B o)

/-- The element at `o` is reduced: its limbs are below `2⁵¹ + 2¹⁸`. -/
def Tight (m : Mem) (B : Addr) (o : Nat) : Prop := ∀ k < 5, lw m B o k < 2 ^ 51 + 2 ^ 18

/-! ## Products -/

/-- The registers the products write. -/
abbrev accRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r28, .r29, .r30, .r31]

theorem lo_hi : ∀ k < 5, lo k ∈ accRegs ∧ hi k ∈ accRegs ∧ lo k ≠ .r4 ∧ hi k ≠ .r4 ∧
    ∀ j < 5, lo k ≠ hi j ∧ (lo k = lo j → k = j) ∧ (hi k = hi j → k = j) := by decide

/-- A product's value: the registers' product is `2¹³` times it. -/
def pv (s : State) (t : Term) : Nat := (s.gpr t.2.1).toNat * (s.gpr t.2.2.1).toNat / 2 ^ 13

/-- The columns' sums after a product of value `p`. -/
def stepC (first : Bool) (k p : Nat) (c : Nat → Nat) (q : Nat) : Nat :=
  if q = k then (if first then 0 else c q) + p else c q

/-- The columns' sums after the products `ts`, from `c`. -/
def accC (s : State) : List Term → (Nat → Nat) → Nat → Nat
  | [], c => c
  | t :: ts, c => accC s ts (stepC t.1 t.2.2.2 (pv s t) c)

/-- The columns' numbers of products after `ts`, from `n`. -/
def accN : List Term → (Nat → Nat) → Nat → Nat
  | [], n => n
  | t :: ts, n => accN ts (stepC t.1 t.2.2.2 1 n)

/-- A product that is not its column's first follows one, and a column has at most five. -/
def wfN : List Term → (Nat → Nat) → Bool
  | [], _ => true
  | t :: ts, n => (t.1 || decide (0 < n t.2.2.2)) && decide ((if t.1 then 0 else n t.2.2.2) < 5) &&
      wfN ts (stepC t.1 t.2.2.2 1 n)

/-- The products' registers are not those they write, and their columns are below 5. -/
def wfR (ts : List Term) : Bool :=
  ts.all fun t => !accRegs.contains t.2.1 && !accRegs.contains t.2.2.1 && decide (t.2.2.2 < 5)

/-- The columns with a product hold their sums. -/
structure Acc (c n : Nat → Nat) (s : State) : Prop where
  val : ∀ k < 5, 0 < n k → (s.gpr (lo k)).toNat + 2 ^ 51 * (s.gpr (hi k)).toNat = c k
  low : ∀ k < 5, 0 < n k → (s.gpr (lo k)).toNat < n k * 2 ^ 51
  bnd : ∀ k < 5, 0 < n k → c k < n k * 2 ^ 112

theorem Acc.zero (c : Nat → Nat) (s : State) : Acc c (fun _ => 0) s :=
  ⟨fun _ _ h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.lt_irrefl 0),
    fun _ _ h => absurd h (Nat.lt_irrefl 0)⟩

/-- The sums after a product, from what its code leaves in the column's registers. -/
theorem Acc.step {c n : Nat → Nat} {s s' : State} {k p : Nat} {first : Bool} (hk : k < 5) (h : Acc c n s)
    (hp : p < 2 ^ 112)
    (hlo : (s'.gpr (lo k)).toNat = (if first then 0 else (s.gpr (lo k)).toNat) + p % 2 ^ 51)
    (hhi : (s'.gpr (hi k)).toNat = (if first then 0 else (s.gpr (hi k)).toNat) + p / 2 ^ 51)
    (hf : first = false → 0 < n k)
    (hoth : ∀ r, r ≠ .r4 → r ≠ lo k → r ≠ hi k → s'.gpr r = s.gpr r) :
    Acc (stepC first k p c) (stepC first k 1 n) s' := by
  obtain ⟨-, -, -, -, lj⟩ := lo_hi k hk
  have oth : ∀ q < 5, q ≠ k → s'.gpr (lo q) = s.gpr (lo q) ∧ s'.gpr (hi q) = s.gpr (hi q) := fun q hq hqk => by
    obtain ⟨-, -, q4, h4, qj⟩ := lo_hi q hq
    exact ⟨hoth _ q4 (fun e => hqk ((qj k hk).2.1 e)) (qj k hk).1,
      hoth _ h4 (fun e => (lj q hq).1 e.symm) (fun e => hqk ((qj k hk).2.2 e))⟩
  refine ⟨fun q hq hn => ?_, fun q hq hn => ?_, fun q hq hn => ?_⟩
  all_goals
    by_cases hqk : q = k
    · subst hqk
      simp only [stepC, ↓reduceIte] at hn ⊢
      cases first
      · have v := h.val q hq (hf rfl); have l := h.low q hq (hf rfl); have b := h.bnd q hq (hf rfl)
        simp only [Bool.false_eq_true, ↓reduceIte] at hlo hhi ⊢
        omega_using [v, l, b, hlo, hhi, hp]
      · simp only [↓reduceIte] at hlo hhi ⊢
        omega_using [hlo, hhi, hp]
    · simp only [stepC, hqk, ↓reduceIte] at hn ⊢
      first
        | rw [(oth q hq hqk).1, (oth q hq hqk).2]; exact h.val q hq hn
        | rw [(oth q hq hqk).1]; exact h.low q hq hn
        | exact h.bnd q hq hn

section
variable {b : Addr}

theorem term_ok {first : Bool} {x y : Reg} {k : Nat} (hk : k < 5) (hx : x ∉ accRegs) (hy : y ∉ accRegs)
    {c n : Nat → Nat} {s : State} (h : Acc c n s) (hf : first = false → 0 < n k)
    (hn : (if first then 0 else n k) < 5) (hp : pv s (first, x, y, k) < 2 ^ 112) :
    WP isa (.block (term first x y k)) s fun s' =>
      Acc (stepC first k (pv s (first, x, y, k)) c) (stepC first k 1 n) s' ∧
      Rest accRegs s s' ∧ s'.mem = s.mem := by
  obtain ⟨lk, hk', l4, h4, lj⟩ := lo_hi k hk
  have lhk : lo k ≠ hi k := (lj k hk).1
  have x4 : x ≠ .r4 := fun e => hx (e ▸ by decide)
  have xl : x ≠ lo k := fun e => hx (e ▸ lk)
  have y4 : y ≠ .r4 := fun e => hy (e ▸ by decide)
  have yl : y ≠ lo k := fun e => hy (e ▸ lk)
  have hX := (s.gpr x).isLt
  have hY := (s.gpr y).isLt
  have hN : (s.gpr x).toNat * (s.gpr y).toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hX hY
  obtain ⟨e1, e2⟩ := prod_halves ((s.gpr x).toNat * (s.gpr y).toNat)
  simp only [pv] at hp ⊢
  generalize hNN : (s.gpr x).toNat * (s.gpr y).toNat = N at *
  cases first with
  | true =>
    simp only [term, ↓reduceIte]
    refine wp_mul fun s1 u1 => wp_lsr (by decide) fun s2 u2 => wp_mulhu fun s3 u3 => WP.block_nil ?_
    have gx : s2.gpr x = s.gpr x := by rw [u2.other _ xl, u1.other _ x4]
    have gy : s2.gpr y = s.gpr y := by rw [u2.other _ yl, u1.other _ y4]
    refine ⟨Acc.step hk h hp ?_ ?_ hf fun r r4 rl rh => ?_, ?_, by rw [u3.mem, u2.mem, u1.mem]⟩
    · rw [u3.other _ lhk, u2.gpr, u1.gpr, toNat_shr, BitVec.toNat_mul, hNN, e1]; simp
    · rw [u3.gpr, gx, gy, hNN, toNat_imm (by omega_using [hN]), e2]; simp
    · rw [u3.other _ rh, u2.other _ rl, u1.other _ r4]
    · exact (u1.rest (by decide)).trans ((u2.rest lk).trans (u3.rest hk'))
  | false =>
    have v := h.val k hk (hf rfl); have l := h.low k hk (hf rfl); have bb := h.bnd k hk (hf rfl)
    simp only [Bool.false_eq_true, ↓reduceIte] at hn
    simp only [term, Bool.false_eq_true, ↓reduceIte]
    refine wp_mul fun s1 u1 => wp_lsr (by decide) fun s2 u2 => wp_add fun s3 u3 => wp_mulhu fun s4 u4 =>
      wp_add fun s5 u5 => WP.block_nil ?_
    have gx : s3.gpr x = s.gpr x := by rw [u3.other _ xl, u2.other _ x4, u1.other _ x4]
    have gy : s3.gpr y = s.gpr y := by rw [u3.other _ yl, u2.other _ y4, u1.other _ y4]
    have g4 : (s2.gpr .r4).toNat = N / 2 ^ 13 % 2 ^ 51 := by
      rw [u2.gpr, u1.gpr, toNat_shr, BitVec.toNat_mul, hNN, e1]
    have gl : s2.gpr (lo k) = s.gpr (lo k) := by rw [u2.other _ l4, u1.other _ l4]
    have gh : s4.gpr (hi k) = s.gpr (hi k) := by
      rw [u4.other _ h4, u3.other _ (Ne.symm lhk), u2.other _ h4, u1.other _ h4]
    have g4' : (s4.gpr .r4).toNat = N / 2 ^ 13 / 2 ^ 51 := by
      rw [u4.gpr, gx, gy, hNN, toNat_imm (by omega_using [hN]), e2]
    refine ⟨Acc.step hk h hp ?_ ?_ hf fun r r4 rl rh => ?_, ?_,
      by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩
    · rw [u5.other _ lhk, u4.other _ l4, u3.gpr, toNat_add_lt (by rw [gl, g4]; omega_using [l, hn]), gl, g4]
      simp
    · rw [u5.gpr, toNat_add_lt (by rw [gh, g4']; omega_using [v, bb, hn, hp]), gh, g4']; simp
    · rw [u5.other _ rh, u4.other _ r4, u3.other _ rl, u2.other _ r4, u1.other _ r4]
    · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest lk).trans
        ((u4.rest (by decide)).trans (u5.rest hk'))))

theorem accC_congr {s s' : State} : ∀ (ts : List Term) (c : Nat → Nat), (∀ t ∈ ts, pv s' t = pv s t) →
    accC s' ts c = accC s ts c
  | [], _, _ => rfl
  | t :: ts, c, h => by
    rw [accC, accC, h t (List.mem_cons_self ..)]
    exact accC_congr ts _ fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

theorem pv_rest {s s' : State} (hr : Rest accRegs s s') {t : Term} (hx : t.2.1 ∉ accRegs)
    (hy : t.2.2.1 ∉ accRegs) : pv s' t = pv s t := by
  rw [pv, pv, hr.gpr _ hx, hr.gpr _ hy]

/-- The products of a list, by induction. -/
theorem terms_ok : ∀ (ts : List Term) (c n : Nat → Nat) (s : State), wfR ts = true → wfN ts n = true →
    Acc c n s → (∀ t ∈ ts, pv s t < 2 ^ 112) →
    WP isa (.block (terms ts)) s fun s' =>
      Acc (accC s ts c) (accN ts n) s' ∧ Rest accRegs s s' ∧ s'.mem = s.mem
  | [], _, _, s, _, _, h, _ => WP.block_nil ⟨h, Rest.refl _ _, rfl⟩
  | (f, x, y, k) :: ts, c, n, s, hr, hw, h, hp => by
    rw [terms, List.flatMap_cons]
    simp only [wfR, List.all_cons, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hr
    simp only [wfN, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hx, hy⟩, hk⟩, hr'⟩ := hr
    obtain ⟨⟨hf, hn⟩, hw'⟩ := hw
    have hx' : x ∉ accRegs := fun e => by rw [List.contains_iff_mem.mpr e] at hx; exact absurd hx (by decide)
    have hy' : y ∉ accRegs := fun e => by rw [List.contains_iff_mem.mpr e] at hy; exact absurd hy (by decide)
    refine WP.append (term_ok (first := f) hk hx' hy' h (fun e => hf.resolve_left (e ▸ Bool.false_ne_true)) hn
      (hp _ (List.mem_cons_self ..))) fun s1 ⟨h1, r1, m1⟩ => ?_
    have hpv : ∀ t ∈ ts, pv s1 t = pv s t := fun t ht => by
      have := List.all_eq_true.mp hr' t ht
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact pv_rest r1 (fun e => by rw [List.contains_iff_mem.mpr e] at this; exact absurd this.1.1 (by decide))
        (fun e => by rw [List.contains_iff_mem.mpr e] at this; exact absurd this.1.2 (by decide))
    refine WP.mono (terms_ok ts _ _ s1 hr' hw' h1 fun t ht => by
      rw [hpv t ht]; exact hp t (List.mem_cons_of_mem _ ht)) fun s2 ⟨h2, r2, m2⟩ => ⟨?_, r1.trans r2, m2.trans m1⟩
    rw [accC_congr ts _ hpv] at h2
    exact h2

/-! ## The reduction -/

/-- `tail` before its stores. -/
def tailR : List Instr :=
  (List.range 4).map (fun k => .add (lo (k + 1)) (lo (k + 1)) (hi k)) ++ mask51 ++
  [.li .r15 19, .logic .and .r14 .r5 .r4, .lsr .d .r5 .r5 51, .mul .r14 .r14 .r15, .mul .r5 .r5 .r15,
    .add .r7 .r7 .r14, .add .r8 .r8 .r5] ++
  (List.range 5).map (fun k => .lsr .d (cy k) (lo k) 51) ++
  (List.range 5).map (fun k => .logic .and (lo k) (lo k) .r4) ++
  [.mul .r20 .r20 .r15, .add .r7 .r7 .r20] ++
  (List.range 4).map (fun k => .add (lo (k + 1)) (lo (k + 1)) (cy k))

theorem tail_eq (o : Nat) : tail o = tailR ++ stores lo o := rfl

/-- The registers `tail` writes. -/
abbrev tailRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20]

theorem tn_add {x y : BitVec 64} {a c : Nat} (hx : x.toNat = a) (hy : y.toNat = c) (h : a + c < 2 ^ 64) :
    (x + y).toNat = a + c := by
  rw [toNat_add_lt (by rw [hx, hy]; exact h), hx, hy]

theorem tn_mul19 {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (h : a * 19 < 2 ^ 64) :
    (x * BitVec.ofNat 64 19).toNat = 19 * a := by
  rw [toNat_mul_lt (by rw [hx]; exact h), hx]; exact Nat.mul_comm _ _

theorem tn_mask {x m : BitVec 64} {a : Nat} (hx : x.toNat = a) (hm : m.toNat = 2 ^ 51 - 1) :
    (x &&& m).toNat = a % 2 ^ 51 := by
  rw [BitVec.toNat_and, hm, hx]; exact Nat.and_two_pow_sub_one_eq_mod _ 51

theorem tn_shr {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (n : Nat) : (x >>> n).toNat = a / 2 ^ n := by
  rw [toNat_shr, hx]

theorem m51 : (BitVec.ofNat 64 1 <<< 51 - BitVec.ofNat 64 1).toNat = 2 ^ 51 - 1 := by decide

theorem tailR_ok {s : State} {L H : Nat → Nat} (hL : ∀ k < 5, (s.gpr (lo k)).toNat = L k)
    (hH : ∀ k < 5, (s.gpr (hi k)).toNat = H k) (bL : ∀ k < 5, L k < 2 ^ 54)
    (bH : ∀ k < 5, H k < 5 * 2 ^ 61) :
    WP isa (.block tailR) s fun s' => ∃ r0 r1 r2 r3 r4 : Nat, (s'.gpr .r7).toNat = r0 ∧
      (s'.gpr .r8).toNat = r1 ∧ (s'.gpr .r9).toNat = r2 ∧ (s'.gpr .r10).toNat = r3 ∧
      (s'.gpr .r11).toNat = r4 ∧ s'.mem = s.mem ∧
      (val5 (lim r0 r1 r2 r3 r4) % P = val5 (fun k => L k + 2 ^ 51 * H k) % P ∧
      r0 < 2 ^ 51 + 2 ^ 18 ∧ r1 < 2 ^ 51 + 2 ^ 18 ∧ r2 < 2 ^ 51 + 2 ^ 18 ∧ r3 < 2 ^ 51 + 2 ^ 18 ∧
      r4 < 2 ^ 51 + 2 ^ 18) := by
  have l0 := hL 0 (by decide); have l1 := hL 1 (by decide); have l2 := hL 2 (by decide)
  have l3 := hL 3 (by decide); have l4 := hL 4 (by decide)
  have h0 := hH 0 (by decide); have h1 := hH 1 (by decide); have h2 := hH 2 (by decide)
  have h3 := hH 3 (by decide); have h4 := hH 4 (by decide)
  have bl0 := bL 0 (by decide); have bl1 := bL 1 (by decide); have bl2 := bL 2 (by decide)
  have bl3 := bL 3 (by decide); have bl4 := bL 4 (by decide)
  have bh0 := bH 0 (by decide); have bh1 := bH 1 (by decide); have bh2 := bH 2 (by decide)
  have bh3 := bH 3 (by decide); have bh4 := bH 4 (by decide)
  simp only [lo, hi, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at l0 l1 l2 l3 l4 h0 h1 h2 h3 h4
  have w19 := tn_mul19 (tn_mask h4 m51) (by omega_using [bh4])
  have t0 := tn_add l0 w19 (by omega_using [bl0])
  have v19 := tn_mul19 (tn_shr h4 51) (by omega_using [bh4])
  have t1 := tn_add (tn_add l1 h0 (by omega_using [bl1, bh0])) v19 (by omega_using [bl1, bh0, bh4])
  have t2 := tn_add l2 h1 (by omega_using [bl2, bh1])
  have t3 := tn_add l3 h2 (by omega_using [bl3, bh2])
  have t4 := tn_add l4 h3 (by omega_using [bl4, bh3])
  have e0 := tn_add (tn_mask t0 m51) (tn_mul19 (tn_shr t4 51) (by omega_using [bl4, bh3]))
    (by omega_using [bl4, bh3])
  have e1 := tn_add (tn_mask t1 m51) (tn_shr t0 51) (by omega_using [bl0, bh4])
  have e2 := tn_add (tn_mask t2 m51) (tn_shr t1 51) (by omega_using [bl1, bh0, bh4])
  have e3 := tn_add (tn_mask t3 m51) (tn_shr t2 51) (by omega_using [bl2, bh1])
  have e4 := tn_add (tn_mask t4 m51) (tn_shr t3 51) (by omega_using [bl3, bh2])
  crunr [tailR, mask51, lo, hi, cy, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.append_assoc, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil]
  exact ⟨_, _, _, _, _, e0, e1, e2, e3, e4,
    tail_val bl0 bl1 bl2 bl3 bl4 bh0 bh1 bh2 bh3 bh4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- The stores of the limbs in `rs` at `o`. -/
theorem stores_ok (rs : Nat → Reg) {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (stores rs o)) s fun s' =>
      (∀ k < 5, lw s'.mem b o k = (s.gpr (rs k)).toNat) ∧
      Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ Rest [] s s' := by
  simp only [stores, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  refine sd0_ok hc (by omega_using [ho]) (by omega_using [ho4]) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest []) (by decide)
  refine sd0_ok hc1 (by omega_using [ho]) (by omega_using [ho4]) fun s2 u2 => ?_
  have hc2 := hc1.of_rest (u2.rest []) (by decide)
  refine sd0_ok hc2 (by omega_using [ho]) (by omega_using [ho4]) fun s3 u3 => ?_
  have hc3 := hc2.of_rest (u3.rest []) (by decide)
  refine sd0_ok hc3 (by omega_using [ho]) (by omega_using [ho4]) fun s4 u4 => ?_
  have hc4 := hc3.of_rest (u4.rest []) (by decide)
  refine sd0_ok hc4 (by omega_using [ho]) (by omega_using [ho4]) fun s5 u5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have g4 : s4.gpr = s.gpr := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
    have g3 : s3.gpr = s.gpr := by rw [u3.gpr, u2.gpr, u1.gpr]
    have g2 : s2.gpr = s.gpr := by rw [u2.gpr, u1.gpr]
    have g1 : s1.gpr = s.gpr := u1.gpr
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, g4, g3, g2, g1]
    intro k hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    simp only [lw]
    rcases this with rfl | rfl | rfl | rfl | rfl
    · rw [dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]),
        dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_self]
    · rw [dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]),
        dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_self]
    · rw [dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_self]
    · rw [dw_write_other _ _ _ (by omega_using []) (by omega_using [ho]) (by omega_using [ho]), dw_write_self]
    · rw [dw_write_self]
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho]))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho]))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho])) |>.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho]))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho]))
  · exact (u1.rest _).trans ((u2.rest _).trans ((u3.rest _).trans ((u4.rest _).trans (u5.rest _))))

theorem tail_writes : writesOnly tailRegs (.block tailR) = true := by decide +kernel

/-- `tail o`: an element congruent to the columns' number, at `o` and in `lo`. -/
theorem tail_ok {o : Nat} (ho : o + 40 ≤ 4096) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s)
    {c : Nat → Nat} (hv : ∀ k < 5, (s.gpr (lo k)).toNat + 2 ^ 51 * (s.gpr (hi k)).toNat = c k)
    (hl : ∀ k < 5, (s.gpr (lo k)).toNat < 2 ^ 54) (hb : ∀ k < 5, c k < 5 * 2 ^ 112) :
    WP isa (.block (tail o)) s fun s' =>
      Rest tailRegs s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 40⟩] s.mem s'.mem ∧ Tight s'.mem b o ∧
      V5 s'.mem b o % P = val5 c % P ∧ ∀ k < 5, (s'.gpr (lo k)).toNat = lw s'.mem b o k := by
  rw [tail_eq]
  refine WP.append (WP.rest tailRegs (tailR_ok (L := fun k => (s.gpr (lo k)).toNat)
    (H := fun k => (s.gpr (hi k)).toNat) (fun _ _ => rfl) (fun _ _ => rfl) hl fun k hk => by
      have := hv k hk; have := hb k hk; omega_using [this, hv k hk]) tail_writes)
    fun s1 ⟨⟨r0, r1, r2, r3, r4, e0, e1, e2, e3, e4, m1, hval, b0, b1, b2, b3, b4⟩, hr1⟩ => ?_
  have hc1 := hc.of_rest hr1 (by decide)
  refine WP.mono (stores_ok lo ho ho4 hc1) fun s2 ⟨hw, hf, hr2⟩ => ?_
  have hreg : ∀ k < 5, (s1.gpr (lo k)).toNat = lim r0 r1 r2 r3 r4 k := fun k hk => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl
    exacts [e0, e1, e2, e3, e4]
  refine ⟨hr1.trans (hr2.mono (by decide)), by rw [← m1]; exact hf, fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [hw k hk, hreg k hk]
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl
    exacts [b0, b1, b2, b3, b4]
  · rw [V5, val5_congr (g := lim r0 r1 r2 r3 r4) fun k hk => by rw [hw k hk, hreg k hk], hval]
    exact congrArg (· % P) (val5_congr fun k hk => hv k hk)
  · rw [hr2.gpr _ (by simp), hw k hk]

end

end VG.Proof.X25519.PPC64LE.Fe51
