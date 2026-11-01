module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall

/-!
# ECDSA on PPC64LE: the curve, the arguments and the working space

What the proofs of the code built on `Impl.Ecdsa.PPC64LE.Cfg` need of a curve
(`CfgOk`) and of the arguments of its setup (`SetupPre`), for any curve of
`n` 64-bit words, and the state the setup leaves (`SetupPost`), as on
32-bit ARM (`Proof/Ecdsa/Arm/Layout.lean`).

The working space is the `8192` bytes at `scratch` (every offset in it is a
displacement of `ld` and `std`): the saved registers in `[0, 24)`, the
slots `c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, the field
arithmetic's own working space at `own n = 4096 - 64 n`, and the tables of
bits `bitsAt n j` (`64 n` bytes each, `j < 3`) past it. The constants, in
the slots below `12` but the temporary's, are only read once the setup has
written them (`Fixed`); what each later phase writes misses them
(`FixedOk`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 10`, so that the slots and the functions' own
working space fit below byte 4096 and the tables after it), `G` is on the
curve, `p < 2n` (so `x mod n` is one conditional subtraction), the functions
of `p` and `n` compute modulo them (`ModOk`), encodings are `len` bytes in
`n` words (`8 (n - 1) < len ≤ 8 n`, at least one word), and the bits of a
hash of `len` bytes that are not `e`'s (`c.sh`) are fewer than 64. -/
structure CfgOk (c : Cfg) : Prop where
  n0 : 0 < c.n
  n10 : c.n < 10
  onG : onCurve c.C (G c.C) = true
  p_odd : c.C.p % 2 = 1
  n_odd : c.C.n % 2 = 1
  p_lt : c.C.p < 2 ^ (64 * c.n)
  n_lt : c.C.n < 2 ^ (64 * c.n)
  n_enc : c.C.n < 2 ^ (8 * c.C.len)
  p_ge : 3 ≤ c.C.p
  n_ge : 3 ≤ c.C.n
  p_lt_2n : c.C.p < 2 * c.C.n
  len8 : 8 ≤ c.C.len
  len_lo : 8 * c.n < c.C.len + 8
  len_hi : c.C.len ≤ 8 * c.n
  sh : c.sh < 64
  fp : ModOk c.SP.k c.SP.m
  fpk : c.SP.k = c.n
  fpm : c.SP.m = c.C.p
  fn : ModOk c.SN.k c.SN.m
  fnk : c.SN.k = c.n
  fnm : c.SN.m = c.C.n
  /-- `vg_<curve>_mul`, if the curve has it, has no frames, as calls need. -/
  mulNf : ∀ C, c.mul = some C → c.mulFn.noFrames = true

/-- The registers `setupWith` writes. -/
abbrev setupClob : List Reg := [.r0, .r3, .r4, .r8, .r9, .r11, .r14]

/-- Which slot `setupWith` may shift: none, `d`'s (verification reads the
hash there) or the hash's. -/
def ShiftOk (hs : Option Nat) : Prop := hs = none ∨ hs = some D ∨ hs = some E

/-- What `setupWith A` needs of its arguments: the registers `A` names none
that the saves or the loads write, the slot `A.hs` one it may shift,
`scratch`'s `8192` bytes writable, and `k`, `d` and the hash (`len` bytes
each) readable and apart from it, nothing wrapping around `2⁶⁴`. -/
structure SetupPre (c : Cfg) (A : Args) (s : State) : Prop where
  shift : ShiftOk A.hs
  k_reg : A.k ∉ [.r0, .r3, .r8, .r9, .r14]
  d_reg : A.d ∉ [.r0, .r3, .r8, .r9, .r14]
  e_reg : A.e ∉ [.r0, .r3, .r8, .r9, .r14]
  sc_reg : A.sc ∉ [.r0, .r3, .r14]
  wr : (⟨s.gpr A.sc, size⟩ : Region) ∈ s.wr
  sc_fit : (s.gpr A.sc).toNat + size ≤ 2 ^ 64
  k_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr A.k + BitVec.ofNat 64 e) 8
  d_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr A.d + BitVec.ofNat 64 e) 8
  e_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr A.e + BitVec.ofNat 64 e) 8
  k_sc : Region.Disjoint ⟨s.gpr A.k, c.C.len⟩ ⟨s.gpr A.sc, size⟩
  d_sc : Region.Disjoint ⟨s.gpr A.d, c.C.len⟩ ⟨s.gpr A.sc, size⟩
  e_sc : Region.Disjoint ⟨s.gpr A.e, c.C.len⟩ ⟨s.gpr A.sc, size⟩
  k_fit : (s.gpr A.k).toNat + c.C.len ≤ 2 ^ 64
  d_fit : (s.gpr A.d).toNat + c.C.len ≤ 2 ^ 64
  e_fit : (s.gpr A.e).toNat + c.C.len ≤ 2 ^ 64

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 8 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 8 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- The flag word. -/
abbrev flagW (c : Cfg) (base : Addr) (s : State) : BitVec 64 := word s.mem base (c.sl FLAG)

/-- A mask: all ones if `p`, else zero. -/
abbrev mask64 (p : Prop) [Decidable p] : BitVec 64 := if p then BitVec.allOnes 64 else 0

theorem mask64_and (p q : Prop) [Decidable p] [Decidable q] : mask64 p &&& mask64 q = mask64 (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [mask64, hp, hq]

/-- The bits slot `i` is shifted right by when `setupWith` reads it, if `hs`
is `A.hs`: `c.sh` for the slot `hs` holding a hash, 0 for the others. -/
abbrev shAt (c : Cfg) (hs : Option Nat) (i : Nat) : Nat := if hs = some i then c.sh else 0

theorem shAt_none (c : Cfg) (i : Nat) : shAt c none i = 0 := rfl
theorem shAt_self (c : Cfg) (i : Nat) : shAt c (some i) i = c.sh := ite_eq_left_of_eq_true _ _ (eq_true rfl)
theorem shAt_E_D (c : Cfg) : shAt c (some E) D = 0 := rfl
theorem shAt_E_K (c : Cfg) : shAt c (some E) K = 0 := rfl
theorem shAt_D_K (c : Cfg) : shAt c (some D) K = 0 := rfl
theorem shAt_D_E (c : Cfg) : shAt c (some D) E = 0 := rfl

/-- What `setupWith A` leaves, from the state `s₀` at entry, with the working
space at `base`: `r3 = base`, `r14`, `r31` and `lr` in `[0, 24)`,
`r14 = out`, `k`, `d` and the hash in their slots (the slot `A.hs` shifted,
`shAt`), the constants in theirs, and the flag all ones; only `setupClob`
and the working space below byte 4096 changed. -/
structure SetupPost (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop where
  ws : WsReg s base
  keep : Kp setupClob s₀ s
  unch : Unch base [(0, 4096)] s₀.mem s.mem
  saved : ∀ rd ∈ Cfg.saved, word s.mem base rd.2 = s₀.gpr rd.1
  savedLr : word s.mem base Cfg.lrAt = s₀.lr
  r14 : s.gpr .r14 = s₀.gpr .r3
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.k) c.C.len) >>> shAt c A.hs K
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.d) c.C.len) >>> shAt c A.hs D
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr A.e) c.C.len) >>> shAt c A.hs E
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : flagW c base s = BitVec.allOnes 64

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem own_eq (n : Nat) : own n = 4096 - 64 * n := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 4096 + 64 * c.n * j := rfl

/-- Slots `i < j` are apart. -/
theorem sl_lt (c : Cfg) {i j : Nat} (h : i < j) : c.sl i + 8 * c.n ≤ c.sl j := by
  rw [sl_eq, sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) h
  rw [Nat.mul_succ] at this
  omega

theorem sl_apart (c : Cfg) {i j : Nat} (h : i ≠ j) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inl (sl_lt c h)
  · exact Or.inr (sl_lt c h)

/-- A slot is at a multiple of 4. -/
theorem sl_al (c : Cfg) (i : Nat) : c.sl i % 4 = 0 := by
  rw [sl_eq, Nat.mul_assoc 8]; omega

/-- A slot is below the functions' own working space. -/
theorem sl_below_own (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ own c.n := by
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  rw [own_eq]
  omega

/-- The functions' own working space is below the tables. -/
theorem own_below_bits (c : Cfg) (hn : c.n < 10) (j : Nat) : own c.n + 64 * c.n ≤ bitsAt c.n j := by
  rw [own_eq, bitsAt_eq]
  omega

/-- A slot is below the tables. -/
theorem sl_below_bits (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) (j t : Nat) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  have := sl_below_own c hn hi
  have := own_below_bits c hn j
  omega

/-- Every slot is below byte 4096. -/
theorem sl_le (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ 4096 := by
  have := sl_below_own c hn hi
  rw [own_eq] at this
  omega

/-- Every table is in the working space. -/
theorem bitsAt_le (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  rw [bitsAt_eq]
  have : 64 * c.n * j ≤ 64 * c.n * 2 := Nat.mul_le_mul_left _ (by omega)
  show _ ≤ 8192
  omega

/-- Table `j` of the bits of slot `i`. -/
theorem tbl_bits_ok {c : Cfg} (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base)
    {i j : Nat} (hi : i < 45) (hj : j < 3) :
    WP isa (bits (c.sl i) (bitsAt c.n j) (8 * c.n)) s fun s' =>
      (∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n j + t)) =
        if (wordsVal s.mem base (c.sl i) c.n).testBit t then 1 else 0) ∧
      Kp bitsClob s s' ∧ Outside base (bitsAt c.n j) (64 * c.n) s.mem s'.mem := by
  have hb := bitsAt_le c hc.n10 hj
  have := sl_le c hc.n10 hi
  exact bits_ok hw.ws hw.at3 hc.n0 (by omega) hb (Or.inl (sl_below_bits c hc.n10 hi j 0))

/-! ## What every phase keeps -/

/-- The constants, and the saved registers `g` and link register `lr`. -/
structure Fixed (c : Cfg) (base : Addr) (g : Reg → BitVec 64) (lr : BitVec 64) (m : Mem) : Prop where
  mp : wordsVal m base (c.sl MP) c.n = c.C.p
  mn : wordsVal m base (c.sl MN) c.n = c.C.n
  zero : wordsVal m base (c.sl ZERO) c.n = 0
  one : wordsVal m base (c.sl ONE) c.n = 1
  onep : wordsVal m base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p
  ap : wordsVal m base (c.sl AP) c.n = c.mont c.C.a
  b3p : wordsVal m base (c.sl B3P) c.n = c.mont (3 * c.C.b)
  gx : wordsVal m base (c.sl GX) c.n = c.mont c.C.gx
  gy : wordsVal m base (c.sl GY) c.n = c.mont c.C.gy
  r2n : wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n
  onen : wordsVal m base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n
  saved : ∀ rd ∈ Cfg.saved, word m base rd.2 = g rd.1
  savedLr : word m base Cfg.lrAt = lr

/-- What a phase writes misses the constants and the saved registers. -/
def FixedOk (c : Cfg) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 = c.sl TMP ∧ w.2 = 8 * c.n) ∨ c.sl 12 ≤ w.1

/-- The ranges of numbered slots. -/
abbrev slW (c : Cfg) (l : List Nat) : List (Nat × Nat) := l.map fun i => (c.sl i, 8 * c.n)

variable {c : Cfg}

theorem FixedOk.append {W W' : List (Nat × Nat)} (h : FixedOk c W) (h' : FixedOk c W') :
    FixedOk c (W ++ W') := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

theorem fixedOk_slW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) : FixedOk c (slW c l) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · exact Or.inl ⟨by rw [h], rfl⟩
  · refine Or.inr ?_
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact Nat.le_trans (Nat.le_add_right _ _) (sl_lt c h)

theorem fixedOk_tbl (h7 : c.n < 10) (j : Nat) : FixedOk c [(bitsAt c.n j, 64 * c.n)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c h7 (by decide) j 0))

theorem fixedOk_flag : FixedOk c [(c.sl FLAG, 8)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide)))

theorem fixedOk_own (h7 : c.n < 10) : FixedOk c [(own c.n, 64 * c.n)] := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide)))

/-- A constant's slot is apart from what a phase writes. -/
theorem fixed_apart {W : List (Nat × Nat)} (hW : FixedOk c W) {i : Nat} (hi : i < 12) (hit : i ≠ TMP) :
    ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases hW w hw with ⟨h1, h2⟩ | h
  · rw [h1, h2]; exact sl_apart c hit
  · exact Or.inl (Nat.le_trans (sl_lt c hi) h)

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 8 ≤ 24 := by decide

theorem Fixed.unch {base : Addr} {g : Reg → BitVec 64} {lr : BitVec 64} {m m' : Mem}
    (h : Fixed c base g lr m) (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {W : List (Nat × Nat)}
    (hW : FixedOk c W) (hu : Unch base W m m') : Fixed c base g lr m' := by
  have := hn
  have e : ∀ i, i < 12 → i ≠ TMP → wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
    fun i hi hit => hu.wordsVal (fixed_apart hW hi hit) (by have := sl_le c h7 (i := i) (by omega); omega)
  have hlow : ∀ d, d + 8 ≤ 24 → word m' base d = word m base d := fun d hd =>
    hu.word (fun w hw => Or.inl (by rcases hW w hw with ⟨h1, -⟩ | h <;> [rw [h1, sl_eq]; rw [sl_eq] at h] <;>
      omega)) (by omega)
  refine ⟨(e MP (by decide) (by decide)).trans h.mp, (e MN (by decide) (by decide)).trans h.mn,
    (e ZERO (by decide) (by decide)).trans h.zero, (e ONE (by decide) (by decide)).trans h.one,
    (e ONEP (by decide) (by decide)).trans h.onep, (e AP (by decide) (by decide)).trans h.ap,
    (e B3P (by decide) (by decide)).trans h.b3p, (e GX (by decide) (by decide)).trans h.gx,
    (e GY (by decide) (by decide)).trans h.gy, (e R2N (by decide) (by decide)).trans h.r2n,
    (e ONEN (by decide) (by decide)).trans h.onen, fun p hp => ?_,
    (hlow _ (by decide)).trans h.savedLr⟩
  exact (hlow p.2 (saved_lt p hp)).trans (h.saved p hp)

/-- A slot apart from the ranges of other numbered slots. -/
theorem apart_slW {l : List Nat} {i : Nat} (hi : i ∉ l) :
    ∀ w ∈ slW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  exact sl_apart c fun h => hi (h ▸ hj)

theorem apart_tbl (h7 : c.n < 10) {i : Nat} (hi : i < 45) (j : Nat) :
    ∀ w ∈ [(bitsAt c.n j, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (by have := sl_below_bits c h7 hi j 0; omega)

theorem apart_own (h7 : c.n < 10) {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(own c.n, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_own c h7 hi)

theorem apart_flag (h0 : 0 < c.n) {i : Nat} (hi : i ≠ FLAG) :
    ∀ w ∈ [(c.sl FLAG, 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_apart c hi
  dsimp only
  omega

theorem apart_append {W W' : List (Nat × Nat)} {x k : Nat}
    (h : ∀ w ∈ W, x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) (h' : ∀ w ∈ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    ∀ w ∈ W ++ W', x + k ≤ w.1 ∨ w.1 + w.2 ≤ x :=
  fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- A number in a slot apart from what changed. -/
theorem sv_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45)
    (hW : ∀ w ∈ W, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  hu.wordsVal hW (by have := sl_le c h7 hi; have := hn; omega)

/-- A byte of table `j` apart from what changed. -/
theorem tbl_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hW : ∀ w ∈ W, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t) :
    m' (off base (bitsAt c.n j + t)) = m (off base (bitsAt c.n j + t)) :=
  hu.byte hW (by have := bitsAt_le c h7 hj; simp only [size] at this; omega)

theorem tbl_apart_slW (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) (j t : Nat) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact Or.inr (sl_below_bits c h7 (hl i hi) j t)

theorem tbl_apart_own (h7 : c.n < 10) (j t : Nat) :
    ∀ w ∈ [(own c.n, 64 * c.n)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := own_below_bits c h7 j
  exact Or.inr (by dsimp only; omega)

theorem tbl_apart_flag (h7 : c.n < 10) (h0 : 0 < c.n) (j t : Nat) :
    ∀ w ∈ [(c.sl FLAG, 8)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_below_bits c h7 (i := FLAG) (by decide) j t
  exact Or.inr (by dsimp only; omega)

/-- Tables `j ≠ j'` are apart. -/
theorem tbl_apart_tbl {j j' t : Nat} (hjj : j ≠ j') (ht : t < 64 * c.n) :
    ∀ w ∈ [(bitsAt c.n j', 64 * c.n)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases Nat.lt_or_gt_of_ne hjj with h | h
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega
  · have := Nat.mul_le_mul_left (64 * c.n) h
    rw [Nat.mul_succ] at this
    omega

end VG.Proof.Ecdsa.PPC64LE
