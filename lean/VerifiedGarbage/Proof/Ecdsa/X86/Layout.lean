import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
import VerifiedGarbage.TCB.X86.Target

/-!
# ECDSA on x86 (32-bit): the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.X86.Cfg.sign` needs of a curve (`CfgOk`) and
of its arguments (`Pre`), for any curve of `n` 64-bit words, and the state
`setup` leaves (`SetupPost`), as on AArch64 (`Proof/Ecdsa/AArch64/Layout.lean`).

The arguments are on the stack (cdecl): `out`, `d`, `digest`, `k` and
`scratch` at `[esp + 4]` to `[esp + 20]` (`ptr s i`). The working space is
the `8192` bytes at `scratch`: the saved registers in `[0, 16)`, the slots
`c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, the tables of bits
`bitsAt n j` (`64 n` bytes each, `j < 3`), and the multiplications'
accumulator at `c.wk = bitsAt n 3`.
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- Argument `i`, a pointer, as an address. -/
abbrev ptr (s : State) (i : Nat) : Addr := (arg s i).setWidth 64

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 10`, so that the slots, the tables and the
accumulator fit in the working space), `G` is on the curve, `p < 2n` (so
`x mod n` is one conditional subtraction), the Montgomery constants are
right, encodings are `len` bytes in `n` words (`8 (n - 1) < len ≤ 8 n`, at
least one word), and the bits of a hash of `len` bytes that are not `e`'s
(`c.sh`, 0 unless `n` has fewer than `8 len` bits) are fewer than 32. -/
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
  len8 : 8 ≤ c.C.len
  len_lo : 8 * c.n < c.C.len + 8
  len_hi : c.C.len ≤ 8 * c.n
  sh : c.sh < 32

section
variable (c : Cfg) (s : State)
/-- The regions of the arguments, on entry. -/
abbrev outR : Region := ⟨ptr s 0, 2 * c.C.len⟩
abbrev dR : Region := ⟨ptr s 1, c.C.len⟩
abbrev digestR : Region := ⟨ptr s 2, c.C.len⟩
abbrev kR : Region := ⟨ptr s 3, c.C.len⟩
abbrev scR : Region := ⟨ptr s 4, size⟩
abbrev argsR : Region := ⟨argAddr s 0, 20⟩
abbrev retR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
end

/-- The arguments, readable and writable as the contract says and apart from
each other as it says. -/
structure Pre (c : Cfg) (s : State) (extra : List Region := []) : Prop where
  rd : s.rd = [dR c s, digestR c s, kR c s, argsR s] ++ extra
  wr : s.wr = [outR c s, scR s]
  out_sc : (outR c s).Disjoint (scR s)
  out_d : (outR c s).Disjoint (dR c s)
  out_digest : (outR c s).Disjoint (digestR c s)
  out_k : (outR c s).Disjoint (kR c s)
  d_sc : (dR c s).Disjoint (scR s)
  digest_sc : (digestR c s).Disjoint (scR s)
  k_sc : (kR c s).Disjoint (scR s)
  args_out : (argsR s).Disjoint (outR c s)
  args_sc : (argsR s).Disjoint (scR s)
  ret_out : (retR s).Disjoint (outR c s)
  ret_sc : (retR s).Disjoint (scR s)
  out_fit : (arg s 0).toNat + 2 * c.C.len ≤ 2 ^ 32
  d_fit : (arg s 1).toNat + c.C.len ≤ 2 ^ 32
  digest_fit : (arg s 2).toNat + c.C.len ≤ 2 ^ 32
  k_fit : (arg s 3).toNat + c.C.len ≤ 2 ^ 32
  sc_fit : (arg s 4).toNat + size ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 5) : (argsR s).Contains (argAddr s i) 4 := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [argAddr_eq, addr_eq (by omega)]
  have ei : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * i) := by
    rw [argAddr_eq, addr_eq (by omega), Offset.add_add]
  show Region.Contains ⟨argAddr s 0, 20⟩ (argAddr s i) 4
  rw [e0, ei]
  exact Offset.contains_base _ (show 4 * i + 4 ≤ 20 by omega) (by omega)

/-- The arguments `A` names. -/
def _root_.VG.Impl.Ecdsa.X86.Args.idx (A : Args) : List Nat := [A.sc, A.k, A.d, A.e]

/-- An argument slot's address, in the argument region. -/
theorem arg_sub {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 5) : Region.Sub ⟨argAddr s i, 4⟩ (argsR s) := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [argAddr_eq, addr_eq (by omega)]
  have ei : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * i) := by
    rw [argAddr_eq, addr_eq (by omega), Offset.add_add]
  show Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 20⟩
  rw [e0, ei]
  exact Offset.sub_base _ (show 4 * i + 4 ≤ 20 by omega)

/-- Argument `i` of `k`'s slot is in the slots of the `k` arguments. -/
theorem arg_subN {s : State} {k i : Nat} (hfit : (s.gpr .esp).toNat + 4 + 4 * k ≤ 2 ^ 32) (hi : i < k) :
    Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 4 * k⟩ := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [argAddr_eq, addr_eq (by omega)]
  have ei : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * i) := by
    rw [argAddr_eq, addr_eq (by omega), Offset.add_add]
  rw [e0, ei]
  exact Offset.sub_base _ (show 4 * i + 4 ≤ 4 * k by omega)

theorem arg_containsN {s : State} {k i : Nat} (hfit : (s.gpr .esp).toNat + 4 + 4 * k ≤ 2 ^ 32) (hi : i < k) :
    Region.Contains ⟨argAddr s 0, 4 * k⟩ (argAddr s i) 4 := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [argAddr_eq, addr_eq (by omega)]
  have ei : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * i) := by
    rw [argAddr_eq, addr_eq (by omega), Offset.add_add]
  rw [e0, ei]
  exact Offset.contains_base _ (show 4 * i + 4 ≤ 4 * k by omega) (by omega)

/-- Which slot `setupWith` may shift: none, `d`'s (verification reads the
hash there) or the hash's. -/
def ShiftOk (hs : Option Nat) : Prop := hs = none ∨ hs = some D ∨ hs = some E

/-- What `setupWith A` needs of its arguments: the slot `A.hs` one it may
shift, the working space writable, the slots of the arguments `A` names and `k`, `d` and the hash (`len` bytes
each) readable, apart from it, and nothing wrapping around `2³²`. -/
structure SetupPre (c : Cfg) (A : Args) (s : State) : Prop where
  shift : ShiftOk A.hs
  wr : (⟨ptr s A.sc, size⟩ : Region) ∈ s.wr
  arg_in : ∀ i ∈ A.idx, InRegions (s.rd ++ s.wr) (argAddr s i) 4
  arg_sc : ∀ i ∈ A.idx, Region.Disjoint ⟨argAddr s i, 4⟩ ⟨ptr s A.sc, size⟩
  sp_fit : ∀ i ∈ A.idx, (s.gpr .esp).toNat + 8 + 4 * i ≤ 2 ^ 32
  k_in : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s A.k + BitVec.ofNat 64 e) 4
  d_in : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s A.d + BitVec.ofNat 64 e) 4
  e_in : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s A.e + BitVec.ofNat 64 e) 4
  k_sc : Region.Disjoint ⟨ptr s A.k, c.C.len⟩ ⟨ptr s A.sc, size⟩
  d_sc : Region.Disjoint ⟨ptr s A.d, c.C.len⟩ ⟨ptr s A.sc, size⟩
  e_sc : Region.Disjoint ⟨ptr s A.e, c.C.len⟩ ⟨ptr s A.sc, size⟩
  k_fit : (arg s A.k).toNat + c.C.len ≤ 2 ^ 32
  d_fit : (arg s A.d).toNat + c.C.len ≤ 2 ^ 32
  e_fit : (arg s A.e).toNat + c.C.len ≤ 2 ^ 32
  sc_fit : (arg s A.sc).toNat + size ≤ 2 ^ 32

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 4 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 4 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

theorem idx_sign {i : Nat} (hi : i ∈ Args.sign.idx) : i < 5 := by
  simp only [Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem Pre.setup {c : Cfg} {s : State} {extra : List Region} (hp : Pre c s extra) : SetupPre c .sign s where
  shift := .inr (.inr rfl)
  wr := by rw [hp.wr]; simp
  arg_in := fun i hi => ⟨argsR s, by rw [hp.rd]; simp, arg_contains hp.sp_fit (idx_sign hi)⟩
  arg_sc := fun i hi => hp.args_sc.sub_left (arg_sub hp.sp_fit (idx_sign hi))
  sp_fit := fun i hi => by have := idx_sign hi; have := hp.sp_fit; omega
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.k_fit; omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.digest_fit; omega)
  k_sc := hp.k_sc
  d_sc := hp.d_sc
  e_sc := hp.digest_sc
  k_fit := hp.k_fit
  d_fit := hp.d_fit
  e_fit := hp.digest_fit
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- The bits slot `i` is shifted right by when `setupWith` reads it, if `hs`
is `A.hs`: `c.sh` for the slot `hs` holding a hash, 0 for the others. -/
abbrev shAt (c : Cfg) (hs : Option Nat) (i : Nat) : Nat := if hs = some i then c.sh else 0

theorem shAt_none (c : Cfg) (i : Nat) : shAt c none i = 0 := rfl
theorem shAt_self (c : Cfg) (i : Nat) : shAt c (some i) i = c.sh := ite_eq_left_of_eq_true _ _ (eq_true rfl)
theorem shAt_E_D (c : Cfg) : shAt c (some E) D = 0 := rfl
theorem shAt_E_K (c : Cfg) : shAt c (some E) K = 0 := rfl
theorem shAt_D_K (c : Cfg) : shAt c (some D) K = 0 := rfl
theorem shAt_D_E (c : Cfg) : shAt c (some D) E = 0 := rfl

/-- What `setupWith A` leaves, from the state `s₀` at entry, with the
working space at `base`, the argument `A.sc`: `edi = base`, `ebx`, `esi`,
`edi` and `ebp` in `[0, 16)`, `k`, `d` and the hash in their slots (the slot
`A.hs` shifted, `shAt`), the constants in theirs, and the flag all ones; only
`eax`, `ebx`, `edx` and `edi` and the working space changed. -/
structure SetupPost (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  keep : Keeps [.eax, .ebx, .edx, .edi] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = s₀.gpr rd.1
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.k) c.C.len) >>> shAt c A.hs K
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.d) c.C.len) >>> shAt c A.hs D
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.e) c.C.len) >>> shAt c A.hs E
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : flagW c base s = BitVec.allOnes 32
  table : c.comb.isSome = true → s.mem.readW (off base Cfg.combPtr) 32 = s₀.gpr .eax

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + (64 * c.n + 4) * j := rfl

theorem wk_eq (c : Cfg) : c.wk = 64 + 8 * c.n * 45 + (64 * c.n + 4) * 3 := rfl

theorem accLen_eq (M : Mod) : accLen M = 16 * M.n + 4 := by
  simp only [accLen, words]; omega

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

theorem sl_inj (c : Cfg) (hn : 0 < c.n) {i j : Nat} (h : c.sl i = c.sl j) : i = j := by
  by_contra hij
  have := sl_apart c hij
  omega

/-- A slot is below the tables. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  rw [bitsAt_eq]
  omega

/-- A slot is below the accumulator. -/
theorem sl_below_wk (c : Cfg) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ c.wk := by
  have := sl_below_bits c hi 3 0
  rw [wk_eq]; rw [bitsAt_eq] at this; omega

/-- The tables are below the accumulator. -/
theorem bitsAt_below_wk (c : Cfg) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ c.wk := by
  rw [bitsAt_eq, wk_eq]
  have := Nat.mul_le_mul_left (64 * c.n + 4) hj
  rw [Nat.mul_succ] at this
  omega

/-- The accumulator is in the working space. -/
theorem wk_le (c : Cfg) (hn : c.n < 10) {M : Mod} (hM : M.n = c.n) : c.wk + accLen M ≤ size := by
  rw [wk_eq, accLen_eq, hM]
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  have : 64 * c.n * 3 ≤ 64 * 9 * 3 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- Every slot is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  have := sl_below_wk c hi
  have := wk_le c hn (M := c.MP') rfl
  omega

/-- Every table is in the working space. -/
theorem bitsAt_le (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  have := bitsAt_below_wk c hj
  have := wk_le c hn (M := c.MP') rfl
  omega

end VG.Proof.Ecdsa.X86
