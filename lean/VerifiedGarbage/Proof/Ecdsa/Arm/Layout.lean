import VerifiedGarbage.Proof.Ecdsa.Arm.Flags
import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
import VerifiedGarbage.TCB.Arm.Target

/-!
# ECDSA on 32-bit ARM: the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.Arm.Cfg.sign` needs of a curve (`CfgOk`) and
of its arguments (`Pre`), for any curve of `n` 64-bit words, and the state
`setup` leaves (`SetupPost`), as on x86 (`Proof/Ecdsa/X86/Layout.lean`).

The arguments are `out`, `d`, `digest` and `k` in `r0`–`r3` and `scratch`
on the stack (AAPCS). The working space is the first `4096` bytes of the
`8192` at `scratch` (every offset in it is an immediate offset of `ldr` and
`str`): the saved registers in `[0, 36)`, the slots
`c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, the tables of bits
`bitsAt n j` (`64 n` bytes each, `j < 3`), and the multiplications'
accumulator at `c.wk = bitsAt n 3`.
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 4096

/-- The register `r`, a pointer, as an address. -/
abbrev ptr (s : State) (r : Reg) : Addr := State.addr (s.gpr r)

/-- `scratch`, the stack argument, as an address. -/
abbrev scPtr (s : State) : Addr := State.addr (stackArg s 0)

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 7`), `G` is on the curve, `p < 2n` (so `x mod n`
is one conditional subtraction), the Montgomery constants are right,
encodings are `8 n` bytes, and a hash of `8 n` bytes is not truncated. -/
structure CfgOk (c : Cfg) : Prop where
  n0 : 0 < c.n
  n7 : c.n < 7
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
  len : c.C.len = 8 * c.n
  hash : 64 * c.n ≤ Spec.Ecdsa.nBits c.C

section
variable (c : Cfg) (s : State)
/-- The regions of the arguments, on entry. -/
abbrev outR : Region := ⟨ptr s .r0, 16 * c.n⟩
abbrev dR : Region := ⟨ptr s .r1, 8 * c.n⟩
abbrev digestR : Region := ⟨ptr s .r2, 8 * c.n⟩
abbrev kR : Region := ⟨ptr s .r3, 8 * c.n⟩
abbrev scR : Region := ⟨scPtr s, 8192⟩
abbrev argsR : Region := ⟨State.addr s.sp, 4⟩
end

/-- The arguments, readable and writable as the contract says and apart from
each other as it says. -/
structure Pre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [dR c s, digestR c s, kR c s, argsR s]
  wr : s.wr = [outR c s, scR s]
  out_sc : (outR c s).Disjoint (scR s)
  d_sc : (dR c s).Disjoint (scR s)
  digest_sc : (digestR c s).Disjoint (scR s)
  k_sc : (kR c s).Disjoint (scR s)
  out_args : (outR c s).Disjoint (argsR s)
  sc_args : (scR s).Disjoint (argsR s)
  out_fit : (s.gpr .r0).toNat + 16 * c.n ≤ 2 ^ 32
  d_fit : (s.gpr .r1).toNat + 8 * c.n ≤ 2 ^ 32
  digest_fit : (s.gpr .r2).toNat + 8 * c.n ≤ 2 ^ 32
  k_fit : (s.gpr .r3).toNat + 8 * c.n ≤ 2 ^ 32
  sc_fit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  sp_fit : s.sp.toNat + 4 ≤ 2 ^ 32

/-- The working space's base, from where `A` says. -/
def scVal (A : Args) (s : State) : BitVec 32 :=
  match A.sc with
  | none => stackArg s 0
  | some r => s.gpr r

theorem scVal_sign (s : State) : scVal .sign s = stackArg s 0 := rfl

/-- The working space's base, as an address. -/
abbrev scBase (A : Args) (s : State) : Addr := State.addr (scVal A s)

/-- The registers `A` names hold none of the working registers of the setup. -/
def argsOk (A : Args) : Prop := A.k ∉ [.r4, .r12, .lr] ∧ A.d ∉ [.r4, .r12, .lr] ∧ A.e ∉ [.r4, .r12, .lr]

/-- What `setupWith A` needs of its arguments: `scratch` readable (if on
the stack) and its `8192` bytes writable, `k`, `d` and the hash readable and
apart from the working space, and nothing wrapping around `2³²`. -/
structure SetupPre (c : Cfg) (A : Args) (s : State) : Prop where
  args : argsOk A
  sc_in : A.sc = none → InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4
  wr : (⟨scBase A s, 8192⟩ : Region) ∈ s.wr
  k_in : ∀ e, e + 4 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (ptr s A.k + BitVec.ofNat 64 e) 4
  d_in : ∀ e, e + 4 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (ptr s A.d + BitVec.ofNat 64 e) 4
  e_in : ∀ e, e + 4 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (ptr s A.e + BitVec.ofNat 64 e) 4
  k_sc : Region.Disjoint ⟨ptr s A.k, 8 * c.n⟩ ⟨scBase A s, size⟩
  d_sc : Region.Disjoint ⟨ptr s A.d, 8 * c.n⟩ ⟨scBase A s, size⟩
  e_sc : Region.Disjoint ⟨ptr s A.e, 8 * c.n⟩ ⟨scBase A s, size⟩
  k_fit : (s.gpr A.k).toNat + 8 * c.n ≤ 2 ^ 32
  d_fit : (s.gpr A.d).toNat + 8 * c.n ≤ 2 ^ 32
  e_fit : (s.gpr A.e).toNat + 8 * c.n ≤ 2 ^ 32
  sc_fit : (scVal A s).toNat + 8192 ≤ 2 ^ 32

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 4 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 4 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega)⟩

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The working space, the first `size` bytes of `scratch`. -/
theorem sc_sub (s : State) : Region.Sub ⟨scPtr s, size⟩ (scR s) := Region.sub_prefix (by decide)

theorem Pre.setup {c : Cfg} {s : State} (hp : Pre c s) (h7 : c.n < 7) : SetupPre c .sign s where
  args := by unfold argsOk; decide
  sc_in := fun _ => by rw [stackArgAddr0]; exact ⟨argsR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩
  wr := by show (⟨scPtr s, 8192⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  k_sc := hp.k_sc.sub_right (sc_sub s)
  d_sc := hp.d_sc.sub_right (sc_sub s)
  e_sc := hp.digest_sc.sub_right (sc_sub s)
  k_fit := hp.k_fit
  d_fit := hp.d_fit
  e_fit := hp.digest_fit
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- What `setupWith A` leaves, from the state `s₀` at entry, with the working
space at `base`: `r12 = base`, `r4`–`r11` and `lr` in `[0, 36)`, `lr = out`,
`k`, `d` and the hash in their slots, the constants in theirs, and the flag
all ones; only `r4`, `r12`, `lr` and the working space changed. -/
structure SetupPost (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  keep : VG.Proof.X25519.Arm.Rest [.r4, .r12, .lr] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = s₀.gpr rd.1
  lr : s.gpr .lr = s₀.gpr .r0
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.k) (8 * c.n))
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.d) (8 * c.n))
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ A.e) (8 * c.n))
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : flagW c base s = BitVec.allOnes 32

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + 64 * c.n * j := rfl

theorem wk_eq (c : Cfg) : c.wk = 64 + 8 * c.n * 45 + 64 * c.n * 3 := rfl

theorem accLen_eq (M : Mod) : accLen M = 32 * M.n + 8 := by
  simp only [accLen, digits]; omega

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
  have := Nat.mul_le_mul_left (64 * c.n) hj
  rw [Nat.mul_succ] at this
  omega

/-- The accumulator is in the working space. -/
theorem wk_le (c : Cfg) (hn : c.n < 7) {M : Mod} (hM : M.n = c.n) : c.wk + accLen M ≤ size := by
  rw [wk_eq, accLen_eq, hM]
  have : 8 * c.n * 45 ≤ 8 * 6 * 45 := Nat.mul_le_mul_right _ (by omega)
  have : 64 * c.n * 3 ≤ 64 * 6 * 3 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 4096
  omega

/-- Every slot is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 7) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  have := sl_below_wk c hi
  have := wk_le c hn (M := c.MP') rfl
  omega

/-- Every table is in the working space. -/
theorem bitsAt_le (c : Cfg) (hn : c.n < 7) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  have := bitsAt_below_wk c hj
  have := wk_le c hn (M := c.MP') rfl
  omega

end VG.Proof.Ecdsa.Arm
