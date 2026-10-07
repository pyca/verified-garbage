import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# ECDSA on AArch64: the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.AArch64.Cfg.sign` needs of a curve (`CfgOk`)
and of its arguments (`Pre`), for any curve of `n` words, and the state
`setup` leaves (`SetupPost`), as on x86-64 (`Proof/Ecdsa/X86_64/Layout.lean`).

The working space is the `8192` bytes at `scratch`: the saved registers in
`[0, 64)`, the slots `c.sl i = 64 + 8 n i` of `n` words for `i < nslots` (but,
for six or nine words, the temporary area `TMP`, at `Mont.moAt n`, where a
call of a Montgomery product's function may write: `sl_tmp`), and
the tables of bits `bitsAt n j` (`64 n` bytes each, `j < 3`), which are
slots `nslots + 8 j` to `nslots + 8 j + 7`. Every offset the scalar's table
(`j = 0`) is read at is below `4096`, as `ldrb` needs.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 10`: the multiplications accumulate in
`x8`–`x15`), `G` is on the curve, `p < 2n` (so `x mod n` is one conditional
subtraction), the Montgomery constants are right, encodings are `len`
bytes in `n` words (`8 (n - 1) < len ≤ 8 n`, at least one word), the bits of
a hash of `len` bytes that are not `e`'s (`c.sh`, 0 unless `n` has fewer
than `8 len` bits) are fewer than 64, `n ≥ 4` words, the inversion
modulo `p` sound (`InvSound`, which `p` prime gives) with its batches and
constants right (`InvOk`), and modulo `n` too or the chain of `n - 2` right
(`fastN`), `n` even or nine (the comb's
selection moves an entry's words in pairs, or by thirds), `a = -3` (the complete formulas are those for it),
and the products modulo `p` are by a function that computes them if they are calls. The group law needs
more (`Weierstrass.Law`, which a prime field and no point of order 2 give:
`Weierstrass.Good.law`), which only the proofs of the results take. -/
structure CfgOk (c : Cfg) : Prop where
  n0 : 0 < c.n
  n10 : c.n < 10
  onG : onCurve c.C (G c.C) = true
  p_odd : c.C.p % 2 = 1
  n_odd : c.C.n % 2 = 1
  p_lt : c.C.p < 2 ^ (64 * c.n)
  n_lt : c.C.n < 2 ^ (64 * c.n)
  p_ge : 3 ≤ c.C.p
  n_ge : 3 ≤ c.C.n
  p_lt_2n : c.C.p < 2 * c.C.n
  minv_p : (c.C.p * (BitVec.ofNat 64 (minv c.C.p)).toNat + 1) % 2 ^ 64 = 0
  minv_n : (c.C.n * (BitVec.ofNat 64 (minv c.C.n)).toNat + 1) % 2 ^ 64 = 0
  red_p : c.MP'.ok c.C.p = true
  red_n : c.MN'.ok c.C.n = true
  n2 : c.n % 2 = 0 ∨ c.n = 9
  len8 : 8 ≤ c.C.len
  len_lo : 8 * c.n < c.C.len + 8
  len_hi : c.C.len ≤ 8 * c.n
  sh : c.sh < 64
  n4 : 4 ≤ c.n
  sound_p : InvSound c.C.p
  inv_p : InvOk c.invP c.C.p
  inv_n : c.fastN = true → InvSound c.C.n ∧ InvOk c.invN c.C.n
  chain_n : c.fastN = false → chainCheck (slide (c.C.n - 2)).1 (slide (c.C.n - 2)).2 (c.C.n - 2) = true
  am3 : AM3 c.C
  /-- If the products modulo `p` are calls of a function (`Mont.callOf`), it
  computes them modulo `p`; those modulo `n` are inline. -/
  call_p : ∀ f m', Mont.callOf c.MP' = some (f, m') → m' = c.C.p ∧
    VG.Proof.Weierstrass.AArch64.Mont.ModOk c.n m'
  call_n : Mont.callOf c.MN' = none

/-- The comb's tables (`Cfg.combWords`) at `T`: readable, held, not
wrapping around, and apart from the working space at `base`. -/
structure TblPre (c : Cfg) (s : State) (T base : Addr) : Prop where
  rd : (⟨T, 8 * c.combWords.length⟩ : Region) ∈ s.rd
  held : ∀ i < c.combWords.length, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = c.combWords.getD i 0
  fit : T.toNat + 8 * c.combWords.length ≤ 2 ^ 64
  sc : Region.Disjoint ⟨T, 8 * c.combWords.length⟩ ⟨base, size⟩

/-- The arguments: `out = x0` (`2 len` bytes), `d = x1`, `digest = x2`,
`k = x3` (`len` bytes each) and `scratch = x4`, and the comb's tables at
the static `c.tsym` (`Artifact.consts`), readable and writable as the
contract says and apart from each other as it says. -/
structure Pre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, c.C.len⟩, ⟨s.gpr .x2, c.C.len⟩, ⟨s.gpr .x3, c.C.len⟩,
    ⟨s.syms c.tsym, 8 * c.combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x0, 2 * c.C.len⟩, ⟨s.gpr .x4, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, 2 * c.C.len⟩ ⟨s.gpr .x4, size⟩
  out_d : Region.Disjoint ⟨s.gpr .x0, 2 * c.C.len⟩ ⟨s.gpr .x1, c.C.len⟩
  out_digest : Region.Disjoint ⟨s.gpr .x0, 2 * c.C.len⟩ ⟨s.gpr .x2, c.C.len⟩
  out_k : Region.Disjoint ⟨s.gpr .x0, 2 * c.C.len⟩ ⟨s.gpr .x3, c.C.len⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x4, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .x2, c.C.len⟩ ⟨s.gpr .x4, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .x3, c.C.len⟩ ⟨s.gpr .x4, size⟩
  out_fit : (s.gpr .x0).toNat + 2 * c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .x4).toNat + size ≤ 2 ^ 64
  tbl : TblPre c s (s.syms c.tsym) (s.gpr .x4)

/-- What `setupWith` needs of its arguments (`Pre` gives it, and so can the
arguments of other functions that run it): the working space `scratch = x4`
writable, and `k = x3`, `d = x1` and `digest = x2` (`len` bytes each)
readable and apart from it. -/
structure SetupPre (c : Cfg) (s : State) : Prop where
  wr : (⟨s.gpr .x4, size⟩ : Region) ∈ s.wr
  k_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 e) 8
  d_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 e) 8
  digest_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 e) 8
  d_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x4, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .x2, c.C.len⟩ ⟨s.gpr .x4, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .x3, c.C.len⟩ ⟨s.gpr .x4, size⟩
  sc_fit : (s.gpr .x4).toNat + size ≤ 2 ^ 64

theorem Pre.setup {c : Cfg} {s : State} (hp : Pre c s) (hc : CfgOk c) : SetupPre c s where
  wr := by rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega)
  digest_in := inRegions_words (by rw [hp.rd]; simp) (by have := hc.len_hi; have := hc.n10; omega)
  d_sc := hp.d_sc
  digest_sc := hp.digest_sc
  k_sc := hp.k_sc
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- Which slot `setupWith` may shift: none, `d`'s (verification reads the
hash there) or the hash's. -/
def ShiftOk (hs : Option Nat) : Prop := hs = none ∨ hs = some D ∨ hs = some E

/-- The bits slot `i` is shifted right by when `setupWith hs` reads it:
`c.sh` for the slot `hs` holding a hash, 0 for the others. -/
abbrev shAt (c : Cfg) (hs : Option Nat) (i : Nat) : Nat := if hs = some i then c.sh else 0

theorem shAt_none (c : Cfg) (i : Nat) : shAt c none i = 0 := rfl
theorem shAt_self (c : Cfg) (i : Nat) : shAt c (some i) i = c.sh := ite_eq_left_of_eq_true _ _ (eq_true rfl)
theorem shAt_E_D (c : Cfg) : shAt c (some E) D = 0 := rfl
theorem shAt_E_K (c : Cfg) : shAt c (some E) K = 0 := rfl
theorem shAt_D_K (c : Cfg) : shAt c (some D) K = 0 := rfl
theorem shAt_D_E (c : Cfg) : shAt c (some D) E = 0 := rfl

theorem shAt_K (c : Cfg) {hs : Option Nat} (h : ShiftOk hs) : shAt c hs K = 0 := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- What `setupWith hs` leaves, from the state `s₀` at entry, with the
working space at `base = x4`: `x0 = base`, `out` in `x20`, `x19`–`x25` in
`[0, 64)`, `k`, `d` and the hash in their slots (the slot `hs` shifted,
`shAt`), the constants in theirs, and the flag all ones; only `x0`, `x1`,
`x2`, `x5`, `x17` and `x20` and the working space changed. -/
structure SetupPost (c : Cfg) (hs : Option Nat) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  x20 : s.gpr .x20 = s₀.gpr .x0
  keep : KeepRegs [.x0, .x1, .x2, .x5, .x17, .x20] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : Spill.Saved base s₀.gpr Cfg.saved s.mem
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x3) c.C.len) >>> shAt c hs K
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len) >>> shAt c hs D
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) c.C.len) >>> shAt c hs E
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64

/-! ## Slots -/

/-- That a slot is not the temporary area, from the context. -/
macro "sl_ne" : tactic =>
  `(tactic| first | decide | with_reducible assumption | (simp only [TMP] at *; omega) | (intro hT; subst hT; simp only [List.mem_cons, List.mem_append, true_or, or_true, not_true_eq_false] at *))

/-- That one of two slots is not the temporary area, or the other is not
where the temporary area is (slot `54` or `82`). -/
macro "sl_or" : tactic =>
  `(tactic| first | decide | exact .inl (by decide) | exact .inr (by decide) | exact .inr ⟨by omega, by omega⟩ | exact .inl (by sl_ne))

theorem sl_eq (c : Cfg) (i : Nat) (h : i ≠ TMP := by sl_ne) : c.sl i = 64 + 8 * c.n * i := by
  rw [Cfg.sl, ite_eq_right (fun h' => h h'.1)]; rfl

/-- For six or nine words, the temporary area is where the Montgomery
products' function stores its modulus. -/
theorem sl_tmp (c : Cfg) (h : c.n = 6 ∨ c.n = 9) : c.sl TMP = Mont.moAt c.n := by
  rw [Cfg.sl, ite_eq_left ⟨rfl, h⟩]

/-- Otherwise every slot is at `64 + 8 n i`. -/
theorem sl_aff (c : Cfg) (hr : ¬(c.n = 6 ∨ c.n = 9)) (i : Nat) : c.sl i = 64 + 8 * c.n * i := by
  rw [Cfg.sl, ite_eq_right (fun h' => hr h'.2)]; rfl

theorem sl_eq4 (c : Cfg) (hn : c.n ≤ 4) (i : Nat) : c.sl i = 64 + 8 * c.n * i :=
  sl_aff c (fun h => by omega) i

theorem sl_ge64 (c : Cfg) (i : Nat) : 64 ≤ c.sl i := by
  rw [Cfg.sl]; split
  · rename_i h; simp only [Mont.moAt]; rcases h.2 with h | h <;> rw [h] <;> decide
  · exact Nat.le_add_right _ _

/-- The temporary area is apart from the scalar's table of bits. -/
theorem tmp_bits0 (c : Cfg) (h7 : c.n < 10) :
    c.sl TMP + 8 * c.n ≤ bitsAt c.n 0 ∨ bitsAt c.n 0 + 64 * c.n ≤ c.sl TMP := by
  unfold bitsAt slot nslots
  by_cases hr : c.n = 6 ∨ c.n = 9
  · rw [sl_tmp c hr]; simp only [Mont.moAt]; right
    rcases hr with h | h <;> rw [h] <;> decide
  · rw [sl_aff c hr]; simp only [TMP]; left
    have : 8 * c.n * 2 + 8 * c.n ≤ 8 * c.n * 45 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by decide)
    omega

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + 64 * c.n * j := rfl

theorem sl_mod8 (c : Cfg) (i : Nat) : c.sl i % 8 = 0 := by
  rw [Cfg.sl]; split
  · simp only [Mont.moAt]; omega
  · show (64 + 8 * c.n * i) % 8 = 0
    rw [Nat.mul_assoc]; omega

theorem bitsAt_mod8 (c : Cfg) (j : Nat) : bitsAt c.n j % 8 = 0 := by
  rw [bitsAt_eq, Nat.mul_assoc 8, Nat.mul_assoc 64]; omega

/-- Slots `i < j` are apart. -/
theorem sl_lt (c : Cfg) {i j : Nat} (h : i < j) (hi : i ≠ TMP := by sl_ne) (hj : j ≠ TMP := by sl_ne) :
    c.sl i + 8 * c.n ≤ c.sl j := by
  rw [sl_eq c i hi, sl_eq c j hj]
  have := Nat.mul_le_mul_left (8 * c.n) h
  rw [Nat.mul_succ] at this
  omega

/-- The temporary area is apart from every other slot but the one at its
place. -/
theorem sl_apart_tmp (c : Cfg) {j : Nat} (hj : j ≠ TMP) (h54 : j ≠ 54 ∧ j ≠ 82) :
    c.sl TMP + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl TMP := by
  rw [sl_eq c j hj]
  by_cases hr : c.n = 6 ∨ c.n = 9
  · rw [sl_tmp c hr]
    simp only [Mont.moAt]
    rcases hr with h | h <;> rw [h] <;> omega
  · rw [sl_aff c hr]
    simp only [TMP] at hj ⊢
    rcases Nat.lt_or_gt_of_ne hj with h | h
    · have := Nat.mul_le_mul_left (8 * c.n) (show j + 1 ≤ 2 from h)
      rw [Nat.mul_add] at this; omega
    · have := Nat.mul_le_mul_left (8 * c.n) (show 3 ≤ j from h)
      omega

/-- Slots `i ≠ j` are apart, but the temporary area and the slot at its
place. -/
theorem sl_apart (c : Cfg) {i j : Nat} (h : i ≠ j) (hi : i ≠ TMP ∨ (j ≠ 54 ∧ j ≠ 82) := by sl_or)
    (hj : j ≠ TMP ∨ (i ≠ 54 ∧ i ≠ 82) := by sl_or) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := by
  by_cases hiT : i = TMP
  · subst hiT
    exact sl_apart_tmp c (Ne.symm h) (hi.resolve_left (fun h' => h' rfl))
  by_cases hjT : j = TMP
  · subst hjT
    exact (sl_apart_tmp c hiT (hj.resolve_left (fun h' => h' rfl))).symm
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inl (sl_lt c h hiT hjT)
  · exact Or.inr (sl_lt c h hjT hiT)

/-- For four words (or fewer), slots `i ≠ j` are apart. -/
theorem sl_apart4 (c : Cfg) (hn : c.n ≤ 4) {i j : Nat} (h : i ≠ j) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := by
  rw [sl_eq4 c hn, sl_eq4 c hn]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := Nat.mul_le_mul_left (8 * c.n) h
    rw [Nat.mul_succ] at this; omega
  · have := Nat.mul_le_mul_left (8 * c.n) h
    rw [Nat.mul_succ] at this; omega

theorem sl_inj (c : Cfg) (hn : 0 < c.n) {i j : Nat} (h : c.sl i = c.sl j)
    (hi : i ≠ TMP ∨ (j ≠ 54 ∧ j ≠ 82) := by sl_or) (hj : j ≠ TMP ∨ (i ≠ 54 ∧ i ≠ 82) := by sl_or) :
    i = j := by
  by_contra hij
  have := sl_apart c hij hi hj
  omega

/-- Every slot is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  by_cases hiT : i = TMP
  · subst hiT
    rw [Cfg.sl]; split
    · simp only [Mont.moAt]; show _ ≤ 8192; omega
    · simp only [slot, TMP]; show _ ≤ 8192; omega
  rw [sl_eq c i hiT]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- A slot below `45` is apart from the scalar's table of bits and the
`64` bytes past it (the temporary area for six or nine words above them, the
others below). -/
theorem sl_bits0 (c : Cfg) {i : Nat} (hi : i < 45) {L : Nat} (hL : L ≤ 64 * c.n + 64) :
    bitsAt c.n 0 + L ≤ c.sl i ∨ c.sl i + 8 * c.n ≤ bitsAt c.n 0 := by
  rw [bitsAt_eq]
  by_cases hT : i = TMP ∧ (c.n = 6 ∨ c.n = 9)
  · obtain ⟨rfl, hr⟩ := hT
    rw [sl_tmp c hr]; simp only [Mont.moAt]; left
    rcases hr with h | h <;> rw [h] at hL ⊢ <;> omega
  · rw [Cfg.sl, ite_eq_right hT]; right
    show 64 + 8 * c.n * i + 8 * c.n ≤ _
    have := Nat.mul_le_mul_left (8 * c.n) (show i + 1 ≤ 45 from hi)
    rw [Nat.mul_succ] at this
    omega

/-- The temporary area is apart from the window method's table of bits
(`64 (n + 1)` bytes at slot `55`). -/
theorem tmp_wb (c : Cfg) (h7 : c.n < 10) :
    c.sl 55 + 4 * (16 * c.n + 1) ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ c.sl 55 := by
  rw [sl_eq c 55]
  by_cases hr : c.n = 6 ∨ c.n = 9
  · rw [sl_tmp c hr]; simp only [Mont.moAt]
    rcases hr with h | h <;> rw [h] <;> omega
  · rw [sl_aff c hr]; simp only [TMP]; right
    have : 8 * c.n * 2 + 8 * c.n ≤ 8 * c.n * 55 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by decide)
    omega

/-- A slot below `45` but the temporary area is below the Montgomery
products' functions' own working space, as their offsets must be. -/
theorem sl_own (c : Cfg) (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hT : i ≠ TMP := by sl_ne) :
    c.sl i + 8 * c.n ≤ VG.Proof.Weierstrass.AArch64.Mont.own c.n := by
  have e := VG.Proof.Weierstrass.AArch64.Mont.own_eq (n := c.n) (by omega)
  rw [sl_eq c i hT]
  have := Nat.mul_le_mul_left (8 * c.n) (show i + 1 ≤ 45 from hi)
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 + 64 * c.n ≤ 4032 := by
    have : 8 * c.n * 45 + 64 * c.n = 424 * c.n := by omega
    omega
  omega

/-- Every table is in the working space. -/
theorem bitsAt_le (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  rw [bitsAt_eq]
  have := Nat.mul_le_mul_left (64 * c.n) hj
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  have : 64 * c.n * 3 ≤ 64 * 9 * 3 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- The table of the scalar's bits, and a word past it, are in the first
`4096` bytes of the working space, where `ldrb` reaches. -/
theorem bitsAt0_le (c : Cfg) (hn : c.n < 10) : bitsAt c.n 0 + 64 * c.n + 64 ≤ 4096 := by
  rw [bitsAt_eq]
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  omega

end VG.Proof.Ecdsa.AArch64
