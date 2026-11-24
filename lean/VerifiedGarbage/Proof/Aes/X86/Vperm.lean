module

public import VerifiedGarbage.Impl.Aes.X86.Vperm
public import VerifiedGarbage.Proof.Aes.Vperm
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES by vector permutations (SSSE3) on x86 (32-bit)

What both directions of `Impl/Aes/X86/Vperm.lean` need, for the functions of
whole blocks and counter mode (`Proof/Variants/AesBlocks/X86/Ssse3.lean`,
`AesCtr32/X86/Ssse3.lean`):

* `pshufb` by an index below 16 or with its high bit set is the tables'
  lookup (`pshufb_eq`), and every index of the code is one;
* straight-line SSE code is run by a function of the XMM registers (`xvals`,
  `wp_x`), and the general-purpose code between keeps them (`wp_g`);
* a direction's SSE code computes the values of `Proof/Aes/Vperm.lean`
  (`DirOk`), so that its rounds (`core_ok`) over the slots are the cipher
  (`Enc.cipher_ok`, `Dec.cipher_ok`);
* the setup stores the tables and the saved registers (`setup_ok`), `prep`
  the slots (`Enc.prep_ok`, `Dec.prep_ok`), and `restore` restores the
  registers (`restore_ok`): together, `CryptOk`.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Vperm

open VG VG.X86
open VG.Impl.Aes.X86.Vperm
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Impl.Aes.Vperm
open VG.Proof.Aes.Vperm
open VG.VectorCrypto (vbyte ofVBytes)
open VG.Proof.Aes.Vector (ext_vbyte vbyte_xor st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aesmc_st)
open VG.Spec.Aes (roundKey cipher invCipher)

/-! ## `pshufb` is the tables' lookup -/

/-- An index `pshufb` and a lookup agree on: below 16, or with its high bit set. -/
def okB (i : BitVec 8) : Bool := i.msb || decide (i.toNat < 16)

/-- Every index of a vector is one. -/
def OkV (v : BitVec 128) : Prop := ∀ e < 16, okB (vbyte v e) = true

theorem pshufb_eq (T : BitVec 128) {v : BitVec 128} (h : OkV v) : XBinOp.eval .pshufb T v = tblV T v := by
  apply ext_vbyte
  intro e he
  rw [vbyte_tblV _ _ he]
  refine (ByteMap.byte_pshufb T v he).trans ?_
  obtain hb := h e he
  change (if (vbyte v e).msb then 0#8 else vbyte T ((vbyte v e).extractLsb' 0 4).toNat) = nib T (vbyte v e)
  revert hb
  generalize vbyte v e = b
  intro hb
  by_cases hm : b.msb = true
  · obtain h128 := BitVec.msb_eq_decide b
    rw [hm] at h128
    obtain h128 := of_decide_eq_true h128.symm
    rw [ite_eq_left hm, nib, ite_eq_right (by omega_using [h128])]; rfl
  · rw [ite_eq_right hm, nib]
    have hlt : b.toNat < 16 := by simpa [okB, hm] using hb
    rw [ite_eq_left hlt]
    refine congrArg _ ?_
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt hlt]

theorem okB_and : ∀ x : BitVec 8, okB (x &&& 0x0f) = true := by decide +kernel
theorem okB_shr : ∀ x : BitVec 8, okB (x >>> 4) = true := by decide +kernel
theorem okB_j : ∀ x : BitVec 8, okB ((x &&& 0x0f) ^^^ x >>> 4) = true := by decide +kernel
theorem okB_iak : ∀ x : BitVec 8, okB (nib inv (x >>> 4) ^^^ nib inva (x &&& 0x0f)) = true := by decide +kernel
theorem okB_jak : ∀ x : BitVec 8,
    okB (nib inv ((x &&& 0x0f) ^^^ x >>> 4) ^^^ nib inva (x &&& 0x0f)) = true := by decide +kernel
theorem okB_io : ∀ x : BitVec 8, okB (ioB x) = true := by decide +kernel
theorem okB_jo : ∀ x : BitVec 8, okB (joB x) = true := by decide +kernel

theorem ok_and (x : BitVec 128) : OkV (x &&& mask) := fun e he => by
  rw [vbyte_and, vbyte_mask e he]; exact okB_and _
theorem ok_shr (x : BitVec 128) : OkV (ushr4 x) := fun e he => by
  rw [vbyte_ushr4 _ he]; exact okB_shr _
theorem ok_j (x : BitVec 128) : OkV ((x &&& mask) ^^^ ushr4 x) := fun e he => by
  rw [vbyte_xor, vbyte_and, vbyte_mask e he, vbyte_ushr4 _ he]; exact okB_j _
theorem ok_iak (x : BitVec 128) : OkV (tblV inv (ushr4 x) ^^^ tblV inva (x &&& mask)) := fun e he => by
  rw [vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_and, vbyte_mask e he, vbyte_ushr4 _ he]
  exact okB_iak _
theorem ok_jak (x : BitVec 128) : OkV (tblV inv ((x &&& mask) ^^^ ushr4 x) ^^^ tblV inva (x &&& mask)) :=
  fun e he => by
    rw [vbyte_xor, vbyte_tblV _ _ he, vbyte_tblV _ _ he, vbyte_xor, vbyte_and, vbyte_mask e he, vbyte_ushr4 _ he]
    exact okB_jak _
theorem ok_io (x : BitVec 128) : OkV (ioV x) := fun e he => by rw [vbyte_ioV _ he]; exact okB_io _
theorem ok_jo (x : BitVec 128) : OkV (joV x) := fun e he => by rw [vbyte_joV _ he]; exact okB_jo _

theorem ok_lit {v : BitVec 128} (h : (List.range 16).all (fun e => okB (vbyte v e)) = true) : OkV v :=
  fun e he => List.all_eq_true.mp h e (List.mem_range.mpr he)

/-- The high nibbles, as `nibbles` computes them. -/
theorem hi4_eq (x : BitVec 128) : XShiftOp.eval .psrld x 4 &&& mask = ushr4 x := by
  apply ext_vbyte
  intro e he
  rw [vbyte_ushr4 _ he]
  exact ByteMap.byte_hi4 x mask he (vbyte_mask e he)

/-! ## Straight-line SSE code -/

/-- Instructions that write only an XMM register, from XMM registers or 16 bytes of memory. -/
def isX : Instr → Bool
  | .movdquLoad _ _ | .xop (.bin ..) | .xop (.shift ..) => true
  | _ => false

/-- The register such an instruction writes. -/
def xdst : Instr → Option XReg
  | .movdquLoad d _ | .xop (.bin _ d _) | .xop (.shift _ d _) => some d
  | _ => none

/-- Where it loads from. -/
def xmemOp : Instr → Option MemOp
  | .movdquLoad _ m => some m
  | _ => none

abbrev XRegs := XReg → BitVec 128

def put (f : XRegs) (d : XReg) (v : BitVec 128) : XRegs := fun r => if r = d then v else f r

theorem put_apply (f : XRegs) (d : XReg) (v : BitVec 128) (r : XReg) :
    put f d v r = if r = d then v else f r := rfl

/-- The XMM registers after an instruction, loading `ld m` at `m`. -/
def xval (ld : MemOp → BitVec 128) (f : XRegs) : Instr → XRegs
  | .movdquLoad d m => put f d (ld m)
  | .xop (.bin op d s) => put f d (op.eval (f d) (f s))
  | .xop (.shift op d n) => put f d (op.eval (f d) n)
  | _ => f

/-- And after a list of them. -/
def xvals (ld : MemOp → BitVec 128) : XRegs → List Instr → XRegs
  | f, [] => f
  | f, i :: is => xvals ld (xval ld f i) is

theorem xvals_load (ld : MemOp → BitVec 128) (f : XRegs) (d : XReg) (m : MemOp) (is : List Instr) :
    xvals ld f (.movdquLoad d m :: is) = xvals ld (put f d (ld m)) is := rfl

theorem xvals_append (ld : MemOp → BitVec 128) (f : XRegs) (a b : List Instr) :
    xvals ld f (a ++ b) = xvals ld (xvals ld f a) b := by
  induction a generalizing f with
  | nil => rfl
  | cons i a ih => exact ih _

theorem xval_keep (ld : MemOp → BitVec 128) (f : XRegs) (i : Instr) (r : XReg) (h : xdst i ≠ some r) :
    xval ld f i r = f r := by
  unfold xval
  split
  all_goals try (rename_i d _; exact ite_eq_right fun (e : r = d) => h (congrArg some e.symm))
  all_goals try (rename_i d _ _; exact ite_eq_right fun (e : r = d) => h (congrArg some e.symm))
  · rfl

theorem xvals_keep (ld : MemOp → BitVec 128) (r : XReg) : ∀ (is : List Instr) (f : XRegs),
    is.all (fun i => xdst i != some r) = true → xvals ld f is r = f r
  | [], _, _ => rfl
  | i :: is, f, h => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact (xvals_keep ld r is _ (by simpa using h.2)).trans (xval_keep ld f i r h.1)

/-- `s` with other XMM registers. -/
def setX (s : State) (f : XRegs) : State := { s with xmm := f }

theorem setX_xmm (s : State) (f : XRegs) : (setX s f).xmm = f := rfl

theorem xval_exec {s : State} {f : XRegs} {i : Instr} (hi : isX i = true)
    (hl : ∀ m, xmemOp i = some m → InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    exec i (setX s f) = some (setX s (xval (fun m => s.mem.readW (s.ea m) 128) f i)) := by
  unfold isX at hi
  split at hi
  · rename_i d m
    obtain h := hl m rfl
    show ((setX s f).load128 ((setX s f).ea m)).map _ = _
    have : (setX s f).load128 ((setX s f).ea m) = some (s.mem.readW (s.ea m) 128) := ite_eq_left h
    rw [this]; rfl
  · rfl
  · rfl
  · cases hi

/-- Straight-line SSE code, and the code after it. -/
theorem wp_x {is rest : List Instr} {s : State} {Q : State → Prop} (hx : is.all isX = true)
    (hl : ∀ m ∈ is.filterMap xmemOp, InRegions (s.rd ++ s.wr) (s.ea m) 16)
    (k : WP isa (.block rest) (setX s (xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is)) Q) :
    WP isa (.block (is ++ rest)) s Q := by
  suffices h : ∀ (is : List Instr) (f : XRegs), is.all isX = true →
      (∀ m ∈ is.filterMap xmemOp, InRegions (s.rd ++ s.wr) (s.ea m) 16) →
      WP isa (.block rest) (setX s (xvals (fun m => s.mem.readW (s.ea m) 128) f is)) Q →
      WP isa (.block (is ++ rest)) (setX s f) Q from h is s.xmm hx hl k
  intro is
  induction is with
  | nil => exact fun _ _ _ k => k
  | cons i is ih =>
    intro f hx hl k
    simp only [List.all_cons, Bool.and_eq_true] at hx
    refine WP.block_cons_iff.mpr ⟨_, xval_exec hx.1 fun m hm => hl m ?_, ih _ hx.2 (fun m hm => hl m ?_) k⟩
    · rw [List.filterMap_cons, hm]; exact List.mem_cons_self
    · rw [List.filterMap_cons]; split
      · exact hm
      · exact List.mem_cons_of_mem _ hm

/-! ### The other instructions keep the XMM registers -/

/-- Instructions of the general-purpose registers and memory. -/
def isG : Instr → Bool
  | .mov .. | .store .. | .alu .. | .bswap _ => true
  | _ => false

theorem xmm_exec {s s' : State} {i : Instr} (hi : isG i = true) (h : exec i s = some s') : s'.xmm = s.xmm := by
  unfold isG at hi
  split at hi
  · simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h; rfl
  · simp only [reduceExec, State.store32] at h
    split at h
    · cases h; rfl
    · cases h
  · rename_i op d src
    simp only [reduceExec, execAlu, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    cases op <;> simp only [Option.map_eq_some_iff, Option.some.injEq] at h
    all_goals first
      | (subst h; rfl)
      | (obtain ⟨c, -, rfl⟩ := h; rfl)
  · simp only [reduceExec, Option.some.injEq] at h
    subst h; rfl
  · cases hi

theorem wp_g {is : List Instr} {s : State} {Q : State → Prop} (hg : is.all isG = true)
    (h : WP isa (.block is) s Q) : WP isa (.block is) s fun s' => Q s' ∧ s'.xmm = s.xmm := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨WP.block_nil_iff.mp h, rfl⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hg
    obtain ⟨s₁, h₁, h₂⟩ := WP.block_cons_iff.mp h
    refine WP.block_cons_iff.mpr ⟨s₁, h₁, WP.mono (ih hg.2 h₂) fun s' ⟨q, e⟩ => ⟨q, ?_⟩⟩
    rw [e]; exact xmm_exec hg.1 h₁

/-! ## The inversion -/

section
variable {ld : MemOp → BitVec 128} {f : XRegs}

theorem put_self (f : XRegs) (d : XReg) (v : BitVec 128) : put f d v d = v := ite_eq_left rfl

theorem put_ne (f : XRegs) {d r : XReg} (v : BitVec 128) (h : r ≠ d) : put f d v r = f r := ite_eq_right h

theorem nibbles_val (h7 : f .xmm7 = mask) {d t : XReg} (hdt : d ≠ t) (ht : t ≠ .xmm7) :
    xvals ld f (nibbles d t) = put (put f t (ushr4 (f d))) d (f d &&& mask) := by
  funext r
  simp only [nibbles, mv, xvals, xval, put_apply, hdt, ht.symm, XBinOp.eval, ite_true,
    ite_false, h7, hi4_eq]
  by_cases e1 : r = d <;> by_cases e2 : r = t <;> simp only [e1, e2, hdt, hdt.symm, ite_true, ite_false]

/-- What `invert` leaves in the registers it does not name in its result. -/
theorem invert_val {a : Nat} (ha : ld (at_ .edi (16 * a)) = inva) (h6 : f .xmm6 = inv) (h7 : f .xmm7 = mask) :
    xvals ld f (invert a) .xmm2 = ioV (f .xmm0) ∧ xvals ld f (invert a) .xmm5 = joV (f .xmm0) := by
  rw [invert, xvals_append, nibbles_val h7 (by decide) (by decide)]
  generalize hx : f .xmm0 = x
  have e : ∀ T, XBinOp.eval .pshufb T (x &&& mask) = tblV T (x &&& mask) := fun T => pshufb_eq T (ok_and x)
  have e' : ∀ T, XBinOp.eval .pshufb T (ushr4 x) = tblV T (ushr4 x) := fun T => pshufb_eq T (ok_shr x)
  have ej : ∀ T, XBinOp.eval .pshufb T ((x &&& mask) ^^^ ushr4 x) = tblV T ((x &&& mask) ^^^ ushr4 x) :=
    fun T => pshufb_eq T (ok_j x)
  have ei : ∀ T, XBinOp.eval .pshufb T (tblV inv (ushr4 x) ^^^ tblV inva (x &&& mask)) = _ :=
    fun T => pshufb_eq T (ok_iak x)
  have ek : ∀ T, XBinOp.eval .pshufb T (tblV inv ((x &&& mask) ^^^ ushr4 x) ^^^ tblV inva (x &&& mask)) = _ :=
    fun T => pshufb_eq T (ok_jak x)
  have mvE : ∀ a b : BitVec 128, XBinOp.eval .movdqa a b = b := fun _ _ => rfl
  have pxE : ∀ a b : BitVec 128, XBinOp.eval .pxor a b = a ^^^ b := fun _ _ => rfl
  constructor <;>
    simp only [tl, sb, px, mv, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, ha, h6, mvE, pxE, e, e', ej,
      ei, ek, ioV, joV]

end

/-! ## The shuffles' values -/

theorem mvE (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl
theorem pxE (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem sb_io (T x : BitVec 128) : XBinOp.eval .pshufb T (ioV x) = tblV T (ioV x) := pshufb_eq T (ok_io x)
theorem sb_jo (T x : BitVec 128) : XBinOp.eval .pshufb T (joV x) = tblV T (joV x) := pshufb_eq T (ok_jo x)
theorem sb_lo (T x : BitVec 128) : XBinOp.eval .pshufb T (x &&& mask) = tblV T (x &&& mask) :=
  pshufb_eq T (ok_and x)
theorem sb_hi (T x : BitVec 128) : XBinOp.eval .pshufb T (ushr4 x) = tblV T (ushr4 x) := pshufb_eq T (ok_shr x)
theorem sb_sr (T : BitVec 128) : XBinOp.eval .pshufb T sr = tblV T sr := pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_rsr (T : BitVec 128) : XBinOp.eval .pshufb T rsr = tblV T rsr :=
  pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_r3sr (T : BitVec 128) : XBinOp.eval .pshufb T r3sr = tblV T r3sr :=
  pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_rot (T : BitVec 128) : XBinOp.eval .pshufb T rot = tblV T rot :=
  pshufb_eq T (ok_lit (by decide +kernel))

/-! ## A direction's rounds -/

/-- The code is straight-line SSE code that keeps `xmm6` and `xmm7`, and loads
from the scratch buffer's first `N` bytes at `edi`, or (`k`) 16 bytes at `ebx`. -/
def codeOk (N : Nat) (k : Bool) (is : List Instr) : Bool :=
  is.all isX && (is.filterMap xmemOp).all (fun m =>
    (m.base == .edi && decide (m.disp + 16 ≤ N)) || (k && decide (m = at_ .ebx 0))) &&
  is.all (fun i => xdst i != some .xmm6) && is.all (fun i => xdst i != some .xmm7)

/-- What a direction's code computes: `f0` the state from a block and its
first slot, `fr` from a state and a slot the next state, and `fl` from a state
and a slot the block. -/
structure DirOk (d : Dir) (all : List (BitVec 128)) (f0 fr fl : BitVec 128 → BitVec 128 → BitVec 128) : Prop where
  slots : d.slots = 16 * all.length
  le : d.slots ≤ 464
  first : ∀ (ld : MemOp → BitVec 128) (f : XRegs), (∀ k < all.length, ld (at_ .edi (16 * k)) = all.getD k 0) →
    f .xmm7 = mask → xvals ld f d.first .xmm0 = f0 (f .xmm0) (ld (at_ .edi d.slots))
  round : ∀ (ld : MemOp → BitVec 128) (f : XRegs), (∀ k < all.length, ld (at_ .edi (16 * k)) = all.getD k 0) →
    f .xmm6 = inv → f .xmm7 = mask →
    xvals ld f (invert d.inva ++ d.mix) .xmm0 = fr (f .xmm0) (ld (at_ .ebx 0))
  last : ∀ (ld : MemOp → BitVec 128) (f : XRegs), (∀ k < all.length, ld (at_ .edi (16 * k)) = all.getD k 0) →
    f .xmm6 = inv → f .xmm7 = mask →
    xvals ld f (invert d.inva ++ d.last) .xmm0 = fl (f .xmm0) (ld (at_ .ebx 0))
  firstOk : codeOk (d.slots + 16) false d.first = true
  roundOk : codeOk d.slots true (invert d.inva ++ d.mix) = true
  lastOk : codeOk d.slots true (invert d.inva ++ d.last) = true

/-- The state after the first slot and `j` full rounds. -/
def rs (f0 fr : BitVec 128 → BitVec 128 → BitVec 128) (key : Nat → BitVec 128) (x : BitVec 128) : Nat → BitVec 128
  | 0 => f0 x (key 0)
  | j + 1 => fr (rs f0 fr key x j) (key (j + 1))

/-- Where the rounds run: the scratch buffer, of `N` bytes, at `edi`, with the
tables and the slots, and `rounds` the stack's argument 1. -/
structure CoreIn (d : Dir) (all : List (BitVec 128)) (N : Nat) (B : BitVec 32) (R : Nat) (key : Nat → BitVec 128)
    (s : State) : Prop where
  edi : s.gpr .edi = B
  fit : B.toNat + N ≤ 2 ^ 32
  room : d.slots + 240 ≤ N
  scr : reg32 B N ∈ s.wr
  tab : ∀ k < all.length, s.mem.readW (addr B (16 * k)) 128 = all.getD k 0
  slot : ∀ j ≤ R, s.mem.readW (addr B (d.slots + 16 * j)) 128 = key j
  x6 : s.xmm .xmm6 = inv
  x7 : s.xmm .xmm7 = mask
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4
  arg : s.mem.readW (addr (s.gpr .esp) 8) 32 = BitVec.ofNat 32 R

/-- What the rounds keep. -/
structure Kept (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  gpr : ∀ r, r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r
  x6 : s'.xmm .xmm6 = s.xmm .xmm6
  x7 : s'.xmm .xmm7 = s.xmm .xmm7

theorem Kept.refl (s : State) : Kept s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, rfl, rfl⟩

theorem Kept.trans {a b c : State} (h : Kept a b) (h' : Kept b c) : Kept a c :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r h1 h2 => (h'.gpr r h1 h2).trans (h.gpr r h1 h2), h'.x6.trans h.x6, h'.x7.trans h.x7⟩

section
variable {d : Dir} {all : List (BitVec 128)} {f0 fr fl : BitVec 128 → BitVec 128 → BitVec 128}
  {N : Nat} {B : BitVec 32} {R : Nat} {key : Nat → BitVec 128}

theorem CoreIn.of_kept {s s' : State} (h : CoreIn d all N B R key s) (k : Kept s s') :
    CoreIn d all N B R key s' where
  edi := by rw [k.gpr _ (by decide) (by decide), h.edi]
  fit := h.fit
  room := h.room
  scr := by rw [k.wr]; exact h.scr
  tab := by rw [k.mem]; exact h.tab
  slot := by rw [k.mem]; exact h.slot
  x6 := k.x6.trans h.x6
  x7 := k.x7.trans h.x7
  rounds := h.rounds
  argIn := by rw [k.rd, k.wr, k.gpr _ (by decide) (by decide)]; exact h.argIn
  arg := by rw [k.mem, k.gpr _ (by decide) (by decide)]; exact h.arg

theorem CoreIn.le {s : State} (h : CoreIn d all N B R key s) : 10 ≤ R ∧ R ≤ 14 := by
  rcases h.rounds with h | h | h <;> omega_using [h]

/-- Code that `codeOk` checks, run: it changes only `xmm0` to `xmm5`. -/
theorem CoreIn.run {is rest : List Instr} {s : State} {Q : State → Prop} (h : CoreIn d all N B R key s)
    {n : Nat} {k : Bool} (hn : n ≤ N) (hk : k = true → InRegions (s.rd ++ s.wr) (s.ea (at_ .ebx 0)) 16)
    (hc : codeOk n k is = true)
    (q : ∀ s', s' = setX s (xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is) → Kept s s' →
      WP isa (.block rest) s' Q) : WP isa (.block (is ++ rest)) s Q := by
  simp only [codeOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine wp_x h1 (fun m hm => ?_) (q _ rfl ⟨rfl, rfl, rfl, fun _ _ _ => rfl, xvals_keep _ _ _ _ h3,
    xvals_keep _ _ _ _ h4⟩)
  obtain c := List.all_eq_true.mp h2 m hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  rcases c with ⟨e, l⟩ | ⟨e, rfl⟩
  · obtain ⟨b, o⟩ := m
    simp only at e l
    subst e
    rw [ea_mk, h.edi]
    exact in_rd (in_reg h.scr h.fit (by omega_using [l, hn]) (by decide))
  · exact hk e

/-- The tables, as the code loads them. -/
theorem CoreIn.tabs {s : State} (h : CoreIn d all N B R key s) : ∀ k < all.length,
    s.mem.readW (s.ea (at_ .edi (16 * k))) 128 = all.getD k 0 := fun k hk => by
  rw [at_, ea_mk, h.edi]; exact h.tab k hk

/-- A slot at `ebx`. -/
theorem CoreIn.at_ebx {s : State} (h : CoreIn d all N B R key s) {j : Nat} (hj : j ≤ R)
    (hb : s.gpr .ebx = B + BitVec.ofNat 32 (d.slots + 16 * j)) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .ebx 0)) 16 ∧ s.mem.readW (s.ea (at_ .ebx 0)) 128 = key j := by
  have hR := h.le
  have hr := h.room
  rw [at_, ea_mk, hb, addr_add, Nat.add_zero]
  exact ⟨in_rd (in_reg h.scr h.fit (by omega_using [hj, hR, hr]) (by decide)), h.slot j hj⟩

/-- After `j` full rounds. -/
structure RoundAt (d : Dir) (f0 fr : BitVec 128 → BitVec 128 → BitVec 128) (B : BitVec 32) (R : Nat)
    (key : Nat → BitVec 128) (x : BitVec 128) (j : Nat) (s : State) : Prop where
  le : j < R
  ebx : s.gpr .ebx = B + BitVec.ofNat 32 (d.slots + 16 * (j + 1))
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R - 1 - j)
  x0 : s.xmm .xmm0 = rs f0 fr key x j

theorem first_ok (hd : DirOk d all f0 fr fl) {s : State} (h : CoreIn d all N B R key s) :
    WP isa (.block (d.first ++ d.start)) s fun s' => Kept s s' ∧ RoundAt d f0 fr B R key (s.xmm .xmm0) 0 s' := by
  have hR := h.le
  refine h.run (n := d.slots + 16) (k := false) (by have := h.room; omega_using [this]) (fun e => nomatch e) hd.firstOk
    fun s₁ e₁ k₁ => ?_
  have x₁ : s₁.xmm .xmm0 = f0 (s.xmm .xmm0) (key 0) := by
    rw [e₁, setX_xmm, hd.first _ _ h.tabs h.x7]
    refine congrArg _ ?_
    rw [at_, ea_mk, h.edi]
    exact h.slot 0 (Nat.zero_le _)
  have h₁ := h.of_kept k₁
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, r ≠ .ebx → r ≠ .ecx → s'.gpr r = s₁.gpr r) ∧
      s'.gpr .ebx = B + BitVec.ofNat 32 (d.slots + 16) ∧ s'.gpr .ecx = BitVec.ofNat 32 (R - 1)) rfl ?_) fun s' hs => ?_
  · refine Wp.wp_mov fun s₂ u₂ => Wp.wp_addi fun s₃ u₃ => ?_
    refine Wp.wp_ldm (B := s₁.gpr .esp) (by rw [u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact h₁.argIn) fun s₄ u₄ => ?_
    refine Wp.wp_subi fun s₅ u₅ _ _ => WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]
    · rw [u₅.other r h2, u₄.other r h2, u₃.other r h1, u₂.other r h1]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁.edi]
    · rw [u₅.gpr, u₄.gpr, u₃.mem, u₂.mem, h₁.arg]
      exact Wp.ofNat_pred (by omega_using [hR])
  · obtain ⟨⟨m, rd, wr, g, b, c⟩, x⟩ := hs
    refine ⟨k₁.trans ⟨m, rd, wr, g, congrFun x _, congrFun x _⟩, by omega_using [hR], b, c, ?_⟩
    rw [x, x₁]; rfl

/-- A full round, the code after its SSE code. -/
theorem round_ok (hd : DirOk d all f0 fr fl) {x : BitVec 128} {j : Nat} {s : State} (h : CoreIn d all N B R key s)
    (hj : RoundAt d f0 fr B R key x j s) (hlt : j + 1 < R) :
    WP isa (.block d.round) s fun s' => Kept s s' ∧ RoundAt d f0 fr B R key x (j + 1) s' ∧
      s'.zf = some (decide (j + 2 = R)) := by
  have hR := h.le
  obtain ⟨hin, hkey⟩ := h.at_ebx (j := j + 1) (by omega_using [hlt]) hj.ebx
  rw [Dir.round, ← List.append_assoc]
  refine h.run (n := d.slots) (k := true) (by have := h.room; omega_using [this]) (fun _ => hin) hd.roundOk
    fun s₁ e₁ k₁ => ?_
  have x₁ : s₁.xmm .xmm0 = rs f0 fr key x (j + 1) := by
    rw [e₁, setX_xmm, hd.round _ _ h.tabs h.x6 h.x7, hj.x0, hkey]; rfl
  have b₁ : s₁.gpr .ebx = s.gpr .ebx := by rw [e₁]; rfl
  have c₁ : s₁.gpr .ecx = s.gpr .ecx := by rw [e₁]; rfl
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, r ≠ .ebx → r ≠ .ecx → s'.gpr r = s₁.gpr r) ∧
      s'.gpr .ebx = s.gpr .ebx + 16 ∧ s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0)) rfl ?_)
      fun s' hs => ?_
  · refine Wp.wp_addi fun s₂ u₂ => Wp.wp_subi fun s₃ u₃ _ z => WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₃.mem, u₂.mem]
    · rw [u₃.rd, u₂.rd]
    · rw [u₃.wr, u₂.wr]
    · rw [u₃.other r h2, u₂.other r h1]
    · rw [u₃.other _ (by decide), u₂.gpr, b₁]
    · rw [u₃.gpr, u₂.other _ (by decide), c₁]
    · rw [z, u₂.other _ (by decide), c₁]
  · obtain ⟨⟨m, rd, wr, g, b, c, z⟩, xx⟩ := hs
    have ec : s.gpr .ecx - 1 = BitVec.ofNat 32 (R - 1 - (j + 1)) := by
      rw [hj.ecx, Wp.ofNat_pred (by omega_using [hlt])]; congr 1
    refine ⟨k₁.trans ⟨m, rd, wr, g, congrFun xx _, congrFun xx _⟩, ⟨hlt, ?_, by rw [c, ec], by rw [xx, x₁]⟩, ?_⟩
    · rw [b, hj.ebx, BitVec.add_assoc]
      refine congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ ?_))
      omega_using []
    · rw [z, ec, Wp.ofNat_beq_zero (by omega_using [hR])]
      refine congrArg some (decide_eq_decide.mpr ?_)
      omega_using [hlt]

/-- A block through the cipher's rounds. -/
theorem core_ok (hd : DirOk d all f0 fr fl) {s : State} (h : CoreIn d all N B R key s) :
    WP isa d.core s fun s' => Kept s s' ∧
      s'.xmm .xmm0 = fl (rs f0 fr key (s.xmm .xmm0) (R - 1)) (key R) := by
  have hR := h.le
  refine WP.seq (WP.mono (first_ok hd h) fun s₁ ⟨k₁, r₁⟩ => ?_)
  generalize hx : s.xmm .xmm0 = x at r₁ ⊢
  refine WP.seq (WP.mono (Q := fun s' => Kept s s' ∧ RoundAt d f0 fr B R key x (R - 1) s') ?_ fun s₂ ⟨k₂, r₂⟩ => ?_)
  · refine WP.loop (M := isa) (fun n s' => ∃ j, n = R - 1 - j ∧ j + 1 < R ∧ Kept s s' ∧ RoundAt d f0 fr B R key x j s')
      (fun n s' ⟨j, hn, hlt, k, r⟩ => ?_) (R - 1) s₁ ⟨0, rfl, by omega_using [hR], k₁, r₁⟩
    refine WP.mono (round_ok hd (h.of_kept k) r hlt) fun s'' ⟨k', r', z⟩ => ?_
    by_cases he : j + 2 = R
    · exact .inl ⟨by simp [eval, z, he], k.trans k', by rw [show R - 1 = j + 1 by omega_using [he]]; exact r'⟩
    · exact .inr ⟨by simp [eval, z, he], R - 1 - (j + 1), by omega_using [hn, hlt, he], j + 1, rfl,
        by omega_using [hlt, he], k.trans k', r'⟩
  · have h₂ := h.of_kept k₂
    obtain ⟨hin, hkey⟩ := h₂.at_ebx (j := R) (Nat.le_refl _)
      (by rw [r₂.ebx, show R - 1 + 1 = R by omega_using [hR]])
    rw [← List.append_nil (invert d.inva ++ d.last)]
    refine h₂.run (n := d.slots) (k := true) (by have := h.room; omega_using [this]) (fun _ => hin) hd.lastOk
      fun s₃ e₃ k₃ => WP.block_nil ⟨k₂.trans k₃, ?_⟩
    rw [e₃, setX_xmm, hd.last _ _ h₂.tabs h₂.x6 h₂.x7, r₂.x0, hkey]

end

/-! ## Encryption: the registers -/

namespace Enc

open VG.Impl.Aes.X86.Vperm.Enc

/-- Every table, as the scratch buffer holds them. -/
def all : List (BitVec 128) := tabs ++ [rsr, r3sr]

variable {ld : MemOp → BitVec 128} {f : XRegs}

/-- The lookups of a vector whose indices are in range, as `pshufb` gives them. -/
theorem mix_val (hT : ∀ k < 14, ld (at_ .edi (16 * k)) = all.getD k 0) {x : BitVec 128}
    (h2 : f .xmm2 = ioV x) (h5 : f .xmm5 = joV x) :
    xvals ld f mix .xmm0 = mixV (ioV x) (joV x) (ld (at_ .ebx 0)) := by
  have t4 : ld (at_ .edi (16 * 4)) = sr := hT 4 (by decide)
  have t5 : ld (at_ .edi (16 * 5)) = rot := hT 5 (by decide)
  have t6 : ld (at_ .edi (16 * 6)) = sb1u := hT 6 (by decide)
  have t7 : ld (at_ .edi (16 * 7)) = sb1t := hT 7 (by decide)
  have t8 : ld (at_ .edi (16 * 8)) = sb2u := hT 8 (by decide)
  have t9 : ld (at_ .edi (16 * 9)) = sb2t := hT 9 (by decide)
  have t12 : ld (at_ .edi (16 * 12)) = rsr := hT 12 (by decide)
  have t13 : ld (at_ .edi (16 * 13)) = r3sr := hT 13 (by decide)
  simp only [mix, tl, sb, px, mv, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t4, t5, t6, t7, t8, t9,
    t12, t13, h2, h5, mvE, pxE, sb_io, sb_jo, sb_sr, sb_rsr, sb_r3sr, sb_rot, mixV, mixX, sA, sA2]

theorem last_val (hT : ∀ k < 14, ld (at_ .edi (16 * k)) = all.getD k 0) {x : BitVec 128}
    (h2 : f .xmm2 = ioV x) (h5 : f .xmm5 = joV x) :
    xvals ld f last .xmm0 = tblV (tblV sbou (ioV x) ^^^ tblV sbot (joV x)) sr ^^^ ld (at_ .ebx 0) := by
  have t4 : ld (at_ .edi (16 * 4)) = sr := hT 4 (by decide)
  have t10 : ld (at_ .edi (16 * 10)) = sbou := hT 10 (by decide)
  have t11 : ld (at_ .edi (16 * 11)) = sbot := hT 11 (by decide)
  simp only [last, tl, sb, px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t4, t10, t11, h2, h5, pxE,
    sb_io, sb_jo, sb_sr]

theorem keyx_val (hT : ∀ k < 14, ld (at_ .edi (16 * k)) = all.getD k 0) (h7 : f .xmm7 = mask) :
    xvals ld f keyx .xmm0 = LcV (f .xmm0) := by
  have t0 : ld (at_ .edi (16 * 0)) = keyLo := hT 0 (by decide)
  have t1 : ld (at_ .edi (16 * 1)) = keyHi := hT 1 (by decide)
  rw [keyx, xvals_append, nibbles_val h7 (by decide) (by decide)]
  simp only [tl, sb, px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t0, t1, pxE, sb_lo, sb_hi, LcV]

theorem first_val (hT : ∀ k < 14, ld (at_ .edi (16 * k)) = all.getD k 0) (h7 : f .xmm7 = mask) :
    xvals ld f first .xmm0 = LcV (f .xmm0) ^^^ ld (at_ .edi slots) := by
  rw [first, xvals_append]
  simp only [px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, pxE, keyx_val hT h7]

/-- What `first`, a round and the last round compute. -/
def f0 (x k : BitVec 128) : BitVec 128 := LcV x ^^^ k
def fr (y k : BitVec 128) : BitVec 128 := mixV (ioV y) (joV y) k
def fl (y k : BitVec 128) : BitVec 128 := tblV (tblV sbou (ioV y) ^^^ tblV sbot (joV y)) sr ^^^ k

theorem dirOk : DirOk enc all f0 fr fl where
  slots := rfl
  le := by decide
  first := fun _ _ hT h7 => first_val hT h7
  round := fun ld f hT h6 h7 => by
    obtain ⟨a, b⟩ := invert_val (ld := ld) (f := f) (a := 3) (hT 3 (by decide)) h6 h7
    rw [xvals_append]
    exact mix_val hT a b
  last := fun ld f hT h6 h7 => by
    obtain ⟨a, b⟩ := invert_val (ld := ld) (f := f) (a := 3) (hT 3 (by decide)) h6 h7
    rw [xvals_append]
    exact last_val hT a b
  firstOk := by decide +kernel
  roundOk := by decide +kernel
  lastOk := by decide +kernel

/-- The slots of round keys `k`, for `R` rounds. -/
def slotKey (R : Nat) (k : Nat → BitVec 128) (j : Nat) : BitVec 128 := if j < R then LcV (k j) else k j ^^^ c63

theorem rs_ok {R : Nat} {w : List Byte} {k : Nat → BitVec 128} (hk : ∀ j ≤ R, KeyIs (k j) (roundKey w j))
    (x : BitVec 128) : ∀ j < R, ∃ X, rs f0 fr (slotKey R k) x j = Lv X ∧ st X = rnds w (st x) j
  | 0, h0 => ⟨x ^^^ k 0, by rw [rs, f0, slotKey, ite_eq_left h0, first_eq], by rw [rnds_zero, eor_st (hk 0 (Nat.zero_le _))]⟩
  | j + 1, hj => by
    obtain ⟨X, e, hX⟩ := rs_ok hk x j (by omega_using [hj])
    refine ⟨_, by rw [rs, e, fr, slotKey, ite_eq_left hj, mixV_eq], ?_⟩
    rw [eor_st (hk _ (by omega_using [hj])), aesmc_st, shiftSub_st, hX, rnds_succ]

/-- The rounds over the slots are the cipher. -/
theorem cipher_ok {R : Nat} (hR : 1 ≤ R) {w : List Byte} {k : Nat → BitVec 128}
    (hk : ∀ j ≤ R, KeyIs (k j) (roundKey w j)) (x : BitVec 128) :
    st (fl (rs f0 fr (slotKey R k) x (R - 1)) (slotKey R k R)) = cipher R w (st x) := by
  obtain ⟨X, e, hX⟩ := rs_ok hk x (R - 1) (by omega_using [hR])
  rw [e, fl, slotKey, ite_eq_right (Nat.lt_irrefl R)]
  refine (congrArg st (lastV_eq X (k R))).trans ?_
  rw [eor_st (hk R (Nat.le_refl R)), shiftSub_st, hX, cipher_eq]

end Enc

/-! ## Decryption: the registers -/

namespace Dec

open VG.Impl.Aes.X86.Vperm.Dec VG.Impl.Aes.Vperm.Dec VG.Proof.Aes.Vperm.Dec

/-- Every table, as the scratch buffer holds them. -/
def all : List (BitVec 128) := tabs ++ [rot2, rot3, p1, p2, p3]

theorem sb_p0 (T : BitVec 128) : XBinOp.eval .pshufb T p0 = tblV T p0 := pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_p1 (T : BitVec 128) : XBinOp.eval .pshufb T p1 = tblV T p1 := pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_p2 (T : BitVec 128) : XBinOp.eval .pshufb T p2 = tblV T p2 := pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_p3 (T : BitVec 128) : XBinOp.eval .pshufb T p3 = tblV T p3 := pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_rot2 (T : BitVec 128) : XBinOp.eval .pshufb T rot2 = tblV T rot2 :=
  pshufb_eq T (ok_lit (by decide +kernel))
theorem sb_rot3 (T : BitVec 128) : XBinOp.eval .pshufb T rot3 = tblV T rot3 :=
  pshufb_eq T (ok_lit (by decide +kernel))

variable {ld : MemOp → BitVec 128} {f : XRegs}

/-- A term of `mix` or `last`. -/
theorem term_val {d e : XReg} {u t p : Nat} {U T P x : BitVec 128} (hu : ld (at_ .edi (16 * u)) = U)
    (ht : ld (at_ .edi (16 * t)) = T) (hp : ld (at_ .edi (16 * p)) = P)
    (hP : ∀ T, XBinOp.eval .pshufb T P = tblV T P) (h2 : f .xmm2 = ioV x) (h5 : f .xmm5 = joV x)
    (hde : d ≠ e) (hd2 : d ≠ .xmm2) (hd5 : d ≠ .xmm5) (he5 : e ≠ .xmm5) :
    xvals ld f (term d e u t p) = put (put f e P) d (xV U T P (ioV x) (joV x)) := by
  funext r
  simp only [term, tl, sb, px, xvals, xval, put_apply, hde, hde.symm, hd2.symm, hd5.symm, he5.symm,
    ite_true, ite_false, hu, ht, hp, h2, h5, pxE, sb_io, sb_jo, hP, xV]
  by_cases e1 : r = d <;> by_cases e2 : r = e <;> simp only [e1, e2, hde, hde.symm, ite_true, ite_false]

theorem mix_val (hT : ∀ k < 29, ld (at_ .edi (16 * k)) = all.getD k 0) {x : BitVec 128}
    (h2 : f .xmm2 = ioV x) (h5 : f .xmm5 = joV x) :
    xvals ld f mix .xmm0 = Dec.mixV (ioV x) (joV x) (ld (at_ .ebx 0)) := by
  rw [mix, xvals_append, xvals_append, xvals_append, xvals_append, xvals_append,
    term_val (hT 11 (by decide)) (hT 12 (by decide)) (hT 19 (by decide)) sb_p0 h2 h5 (by decide) (by decide)
      (by decide) (by decide),
    term_val (x := x) (hT 13 (by decide)) (hT 14 (by decide)) (hT 26 (by decide)) sb_p1
      (by simp only [put_apply, reduceCtorEq, ite_false, h2]) (by simp only [put_apply, reduceCtorEq, ite_false, h5])
      (by decide) (by decide) (by decide) (by decide)]
  simp only [px, xvals, xval]
  rw [term_val (x := x) (hT 15 (by decide)) (hT 16 (by decide)) (hT 27 (by decide)) sb_p2
      (by simp only [put_apply, reduceCtorEq, ite_false, h2]) (by simp only [put_apply, reduceCtorEq, ite_false, h5])
      (by decide) (by decide) (by decide) (by decide),
    term_val (x := x) (hT 17 (by decide)) (hT 18 (by decide)) (hT 28 (by decide)) sb_p3
      (by simp only [put_apply, reduceCtorEq, ite_false, h2]) (by simp only [put_apply, reduceCtorEq, ite_false, h5])
      (by decide) (by decide) (by decide) (by decide)]
  simp only [put_apply, reduceCtorEq, ite_true, ite_false, pxE, Dec.mixV]
  rfl

theorem last_val (hT : ∀ k < 29, ld (at_ .edi (16 * k)) = all.getD k 0) {x : BitVec 128}
    (h2 : f .xmm2 = ioV x) (h5 : f .xmm5 = joV x) :
    xvals ld f last .xmm0 = Dec.lastV (ioV x) (joV x) (ld (at_ .ebx 0)) := by
  rw [last, xvals_append,
    term_val (hT 22 (by decide)) (hT 23 (by decide)) (hT 19 (by decide)) sb_p0 h2 h5 (by decide) (by decide)
      (by decide) (by decide)]
  simp only [px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, pxE, Dec.lastV]
  rfl

theorem first_val (hT : ∀ k < 29, ld (at_ .edi (16 * k)) = all.getD k 0) (h7 : f .xmm7 = mask) :
    xvals ld f first .xmm0 = firstV (f .xmm0 ^^^ ld (at_ .edi slots)) := by
  have t20 : ld (at_ .edi (16 * 20)) = dl := hT 20 (by decide)
  have t21 : ld (at_ .edi (16 * 21)) = dh := hT 21 (by decide)
  rw [first, xvals_append, xvals_append]
  simp only [px, xvals, xval]
  rw [nibbles_val (by simp only [put_apply, reduceCtorEq, ite_false, h7]) (by decide) (by decide)]
  simp only [tl, sb, put_apply, reduceCtorEq, ite_true, ite_false, t20, t21, pxE, sb_lo, sb_hi, firstV]

/-- The products of a key by a constant. -/
theorem keyTerm_val {d : XReg} {l h : Nat} {A H x : BitVec 128} (hl : ld (at_ .edi (16 * l)) = A)
    (hh : ld (at_ .edi (16 * h)) = H) (h0 : f .xmm0 = x &&& mask) (h1 : f .xmm1 = ushr4 x)
    (hd : d = .xmm2 ∨ d = .xmm4) :
    xvals ld f (keyTerm d l h) = put (put f .xmm3 (tblV H (ushr4 x))) d (Yv A H x) := by
  funext r
  rcases hd with rfl | rfl <;>
    (simp only [keyTerm, tl, sb, px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, hl, hh, h0, h1, pxE,
      sb_lo, sb_hi, Yv]
     cases r <;> simp only [reduceCtorEq, ite_true, ite_false])

theorem keyRot_val {l h r : Nat} {A H P x : BitVec 128} (hl : ld (at_ .edi (16 * l)) = A)
    (hh : ld (at_ .edi (16 * h)) = H) (hr : ld (at_ .edi (16 * r)) = P)
    (hP : ∀ T, XBinOp.eval .pshufb T P = tblV T P) (h0 : f .xmm0 = x &&& mask) (h1 : f .xmm1 = ushr4 x) :
    xvals ld f (keyRot l h r) .xmm0 = x &&& mask ∧ xvals ld f (keyRot l h r) .xmm1 = ushr4 x ∧
      xvals ld f (keyRot l h r) .xmm2 = f .xmm2 ^^^ tblV (Yv A H x) P := by
  rw [keyRot, xvals_append, keyTerm_val hl hh h0 h1 (.inr rfl)]
  simp only [tl, sb, px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, hr, hP, h0, h1, pxE, and_self]

theorem key_val (hT : ∀ k < 29, ld (at_ .edi (16 * k)) = all.getD k 0) (h7 : f .xmm7 = mask) :
    xvals ld f key .xmm2 = keyV (f .xmm0) := by
  rw [key, xvals_append, xvals_append, xvals_append, xvals_append,
    nibbles_val h7 (by decide) (by decide),
    keyTerm_val (x := f .xmm0) (hT 2 (by decide)) (hT 3 (by decide))
      (by simp only [put_apply, ite_true]) (by simp only [put_apply, reduceCtorEq, ite_true, ite_false]) (.inl rfl)]
  obtain ⟨a0, a1, a2⟩ := keyRot_val (ld := ld) (x := f .xmm0)
    (f := put (put (put (put f .xmm1 (ushr4 (f .xmm0))) .xmm0 (f .xmm0 &&& mask)) .xmm3
      (tblV (all.getD 3 0) (ushr4 (f .xmm0)))) .xmm2 (Yv (all.getD 2 0) (all.getD 3 0) (f .xmm0)))
    (hT 4 (by decide)) (hT 5 (by decide)) (hT 10 (by decide)) sb_rot
    (by simp only [put_apply, reduceCtorEq, ite_true, ite_false])
    (by simp only [put_apply, reduceCtorEq, ite_true, ite_false])
  obtain ⟨b0, b1, b2⟩ := keyRot_val (ld := ld) (hT 6 (by decide)) (hT 7 (by decide)) (hT 24 (by decide)) sb_rot2 a0 a1
  obtain ⟨-, -, c2⟩ := keyRot_val (ld := ld) (hT 8 (by decide)) (hT 9 (by decide)) (hT 25 (by decide)) sb_rot3 b0 b1
  rw [c2, b2, a2]
  rfl

open VG.Proof.Aes (invMid invMid_succ invCipher_eq irnd)
open VG.Proof.Aes.Vector (st_aesimc st_invSub)

/-- What `first`, a round and the last round compute. -/
def f0 (x k : BitVec 128) : BitVec 128 := firstV (x ^^^ k)
def fr (y k : BitVec 128) : BitVec 128 := Dec.mixV (ioV y) (joV y) k
def fl (y k : BitVec 128) : BitVec 128 := Dec.lastV (ioV y) (joV y) k

theorem dirOk : DirOk dec all f0 fr fl where
  slots := rfl
  le := by decide
  first := fun _ _ hT h7 => first_val hT h7
  round := fun ld f hT h6 h7 => by
    obtain ⟨a, b⟩ := invert_val (ld := ld) (f := f) (a := 1) (hT 1 (by decide)) h6 h7
    rw [xvals_append]
    exact mix_val hT a b
  last := fun ld f hT h6 h7 => by
    obtain ⟨a, b⟩ := invert_val (ld := ld) (f := f) (a := 1) (hT 1 (by decide)) h6 h7
    rw [xvals_append]
    exact last_val hT a b
  firstOk := by decide +kernel
  roundOk := by decide +kernel
  lastOk := by decide +kernel

/-- The slots of round keys `k`, for `R` rounds. -/
def slotKey (R : Nat) (k : Nat → BitVec 128) (j : Nat) : BitVec 128 :=
  if j = 0 ∨ j = R then k (R - j) else keyV (k (R - j))

theorem rs_ok {R : Nat} {w : List Byte} {k : Nat → BitVec 128} (hk : ∀ j ≤ R, KeyIs (k j) (roundKey w j))
    (x : BitVec 128) : ∀ j < R, ∃ X, rs f0 fr (slotKey R k) x j = Dv X ∧
      st X = invMid R w j (Spec.Aes.addRoundKey (st x) (roundKey w R))
  | 0, _ => ⟨x ^^^ k R, by rw [rs, f0, slotKey, ite_eq_left (.inl rfl), firstV_eq, Nat.sub_zero],
      by rw [eor_st (hk R (Nat.le_refl R))]; rfl⟩
  | j + 1, hj => by
    obtain ⟨X, e, hX⟩ := rs_ok hk x j (by omega_using [hj])
    refine ⟨_, by rw [rs, e, fr, slotKey, ite_eq_right (by omega_using [hj]), Dec.mixV_eq], ?_⟩
    rw [invMid_succ, st_aesimc, eor_st (hk _ (by omega_using [])), st_invSub, hX, irnd,
      show R - (j + 1) = R - 1 - j by omega_using []]

/-- The rounds over the slots are the inverse cipher. -/
theorem cipher_ok {R : Nat} (hR : 1 ≤ R) {w : List Byte} {k : Nat → BitVec 128}
    (hk : ∀ j ≤ R, KeyIs (k j) (roundKey w j)) (x : BitVec 128) :
    st (fl (rs f0 fr (slotKey R k) x (R - 1)) (slotKey R k R)) = invCipher R w (st x) := by
  obtain ⟨X, e, hX⟩ := rs_ok hk x (R - 1) (by omega_using [hR])
  rw [e, fl, slotKey, ite_eq_left (.inr rfl), Nat.sub_self, Dec.lastV_eq, eor_st (hk 0 (Nat.zero_le _)), st_invSub, hX,
    invCipher_eq]

end Dec

/-! ## The tables and the saved registers -/

/-- What the code needs of its arguments: argument `k` the scratch buffer, of `N` bytes. -/
structure Args (k N : Nat) (B : BitVec 32) (s₀ : State) : Prop where
  fit : B.toNat + N ≤ 2 ^ 32
  scr : reg32 B N ∈ s₀.wr
  argIn : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * k)) 4
  arg : s₀.mem.readW (addr (s₀.gpr .esp) (4 + 4 * k)) 32 = B

/-- The setup, with the first `n` tables stored. -/
structure TabSt (d : Dir) (all : List (BitVec 128)) (B : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  edi : s.gpr .edi = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [reg32 B (d.saved + 16)] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr B) s₀.gpr d.savedRegs
  tab : ∀ k < n, s.mem.readW (addr B (16 * k)) 128 = all.getD k 0

section
variable {d : Dir} {all : List (BitVec 128)} {N : Nat} {B : BitVec 32} {k : Nat} {s₀ : State}

/-- A store to the tables' bytes keeps what is stored there, and the saved registers. -/
theorem TabSt.store {s s' : State} {n o w : Nat} (h : TabSt d all B s₀ n s) (hfit : B.toNat + (d.saved + 16) ≤ 2 ^ 32)
    (ho : 16 * n ≤ o) (hw : o + w / 8 ≤ d.saved) (hw0 : 0 < w / 8) (v : BitVec w)
    (hm : s'.mem = s.mem.writeW (addr B o) v)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    TabSt d all B s₀ n s' where
  edi := hedi.trans h.edi
  esp := hesp.trans h.esp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  frame := by
    rw [hm]
    exact h.frame.writeW List.mem_cons_self _ (reg_contains hfit (by omega_using [hw]) hw0)
  saved := by
    rw [hm]
    refine h.saved.of_readW fun p hp => ?_
    have hp' : d.saved ≤ p.2 ∧ p.2 + 4 ≤ d.saved + 16 := by
      simp only [Dir.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by omega_using [], by omega_using []⟩
    exact Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨addr B p.2, 4⟩) (r₂ := ⟨addr B o, w / 8⟩)
      (part_disj hfit hp'.2 (by omega_using [hw]) (.inr (by omega_using [hw, hp'])))
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
  tab := fun j hj => by
    rw [hm, ← h.tab j hj]
    exact Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨addr B (16 * j), 16⟩) (r₂ := ⟨addr B o, w / 8⟩)
      (part_disj hfit (by omega_using [hj, ho, hw]) (by omega_using [hw]) (.inl (by omega_using [hj, ho])))
      (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The four stores of a vector leave it. -/
theorem readW_vec (m : Mem) {B : BitVec 32} {o : Nat} (hfit : B.toNat + (o + 16) ≤ 2 ^ 32) (v : BitVec 128)
    (h : ∀ i < 4, m.readW (addr B (o + 4 * i)) 32 = v.extractLsb' (32 * i) 32) :
    m.readW (addr B o) 128 = v := by
  have e : ∀ i < 4, dword (m.readW (addr B o) 128) i = dword v i := fun i hi => by
    rw [dword_readW _ _ hi, addr_add64 (by omega_using [hfit, hi]), h i hi]; rfl
  exact ext_dword (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (e 3 (by decide))

theorem words_cons (v : BitVec 128) (l : List (BitVec 128)) : words (v :: l) =
    v.extractLsb' (32 * 0) 32 :: v.extractLsb' (32 * 1) 32 :: v.extractLsb' (32 * 2) 32 ::
      v.extractLsb' (32 * 3) 32 :: words l := rfl

/-- Table `n` stored. -/
theorem storeVec_ok {rest : List Instr} {s : State} {Q : State → Prop} {n : Nat} (hfit : B.toNat + (d.saved + 16) ≤ 2 ^ 32)
    (hscr : ∀ o, o + 4 ≤ d.saved + 16 → InRegions s.wr (addr B o) 4) (h : TabSt d all B s₀ n s)
    (hn : 16 * n + 16 ≤ d.saved) (q : ∀ s', TabSt d all B s₀ (n + 1) s' → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov .eax (.imm ((all.getD n 0).extractLsb' (32 * 0) 32)) :: .store (at_ .edi (16 * n)) .eax ::
      .mov .eax (.imm ((all.getD n 0).extractLsb' (32 * 1) 32)) :: .store (at_ .edi (16 * n + 4)) .eax ::
      .mov .eax (.imm ((all.getD n 0).extractLsb' (32 * 2) 32)) :: .store (at_ .edi (16 * n + 4 + 4)) .eax ::
      .mov .eax (.imm ((all.getD n 0).extractLsb' (32 * 3) 32)) :: .store (at_ .edi (16 * n + 4 + 4 + 4)) .eax :: rest)) s Q := by
  -- One word.
  have step : ∀ {is : List Instr} {s : State} {o : Nat} {v : BitVec 32}, TabSt d all B s₀ n s →
      (∀ o, o + 4 ≤ d.saved + 16 → InRegions s.wr (addr B o) 4) → 16 * n ≤ o → o + 4 ≤ d.saved →
      (∀ s', TabSt d all B s₀ n s' → s'.wr = s.wr → s'.mem = s.mem.writeW (addr B o) v → WP isa (.block is) s' Q) →
      WP isa (.block (.mov .eax (.imm v) :: .store (at_ .edi o) .eax :: is)) s Q := by
    intro is s o v h hs ho hw q
    refine Wp.wp_movi fun s₁ u₁ => Wp.wp_stm (B := B) ((u₁.other _ (by decide)).trans h.edi)
      (by rw [u₁.wr]; exact hs o (by omega_using [hw])) fun s₂ u₂ => ?_
    have hm : s₂.mem = s.mem.writeW (addr B o) v := by rw [u₂.mem, u₁.mem, u₁.gpr]
    exact q s₂ (h.store hfit ho hw (by decide) v hm (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.gpr, u₁.other _ (by decide)])
      (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr)) (u₂.wr.trans u₁.wr) hm
  refine step h hscr (Nat.le_refl _) (by omega_using [hn]) fun s₁ h₁ w₁ m₁ => ?_
  refine step h₁ (by rw [w₁]; exact hscr) (by omega_using []) (by omega_using [hn]) fun s₂ h₂ w₂ m₂ => ?_
  refine step h₂ (by rw [w₂, w₁]; exact hscr) (by omega_using []) (by omega_using [hn]) fun s₃ h₃ w₃ m₃ => ?_
  refine step h₃ (by rw [w₃, w₂, w₁]; exact hscr) (by omega_using []) (by omega_using [hn]) fun s₄ h₄ w₄ m₄ =>
    q s₄ { h₄ with tab := fun j hj => ?_ } (by rw [w₄, w₃, w₂, w₁])
  by_cases e : j = n
  · subst e
    refine readW_vec _ (by omega_using [hfit, hn]) _ fun i hi => ?_
    have sep : ∀ {m : Mem} {a b : Nat} {v : BitVec 32}, a + 4 ≤ d.saved → b + 4 ≤ d.saved → a + 4 ≤ b →
        (m.writeW (addr B b) v).readW (addr B a) 32 = m.readW (addr B a) 32 := fun ha hb hab =>
      Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨addr B _, 4⟩) (r₂ := ⟨addr B _, 4⟩)
        (part_disj hfit (by omega_using [ha]) (by omega_using [hb]) (.inl hab))
        (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    · rw [m₄, sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₃,
        sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₂,
        sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₁]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [m₄, sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₃,
        sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₂]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [m₄, sep (by omega_using [hn]) (by omega_using [hn]) (by omega_using []), m₃]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [m₄]
      exact Mem.readW_writeW_self32 _ _ _
  · exact h₄.tab j (by omega_using [hj, e])

/-- The tables stored. -/
theorem storeWords_ok {rest : List Instr} {Q : State → Prop} (hfit : B.toNat + (d.saved + 16) ≤ 2 ^ 32) :
    ∀ (l : List (BitVec 128)) {n : Nat} {s : State}, (∀ j < l.length, l.getD j 0 = all.getD (n + j) 0) →
    (∀ o, o + 4 ≤ d.saved + 16 → InRegions s.wr (addr B o) 4) → TabSt d all B s₀ n s →
    16 * (n + l.length) ≤ d.saved → (∀ s', TabSt d all B s₀ (n + l.length) s' → WP isa (.block rest) s' Q) →
    WP isa (.block (storeWords (16 * n) (words l) ++ rest)) s Q
  | [], n, s, _, _, h, _, q => q s h
  | v :: l, n, s, hl, hs, h, hn, q => by
    have e : v = all.getD n 0 := hl 0 (by simp)
    simp only [List.length_cons] at hn
    rw [words_cons, e]
    refine storeVec_ok hfit hs h (by omega_using [hn]) fun s' h' w' => ?_
    refine storeWords_ok hfit l (n := n + 1) (fun j hj => ?_) (by rw [w']; exact hs) h' (by omega_using [hn])
      fun s'' h'' => q s'' (by rw [List.length_cons, show n + (l.length + 1) = n + 1 + l.length by omega_using []]; exact h'')
    rw [show n + 1 + j = n + (j + 1) by omega_using []]
    exact hl (j + 1) (by simp only [List.length_cons]; omega_using [hj])

/-- `splat`. -/
theorem wp_splat {rest : List Instr} {r : XReg} {v : BitVec 32} {s : State} {Q : State → Prop}
    (q : ∀ s', Wp.Upd s s' .eax v → s'.xmm = put s.xmm r (shufDwords ((0 : BitVec 96) ++ v) 0) → WP isa (.block rest) s' Q) :
    WP isa (.block (splat r v ++ rest)) s Q := by
  let a := s.setReg .eax v
  let b := a.setXmm r ((0 : BitVec 96) ++ a.gpr .eax)
  let c := b.setXmm r (shufDwords (b.xmm r) 0)
  have ea : a.gpr .eax = v := RegUpd.gpr_setReg_self _ _ _
  have eb : b.xmm r = (0 : BitVec 96) ++ v := (RegUpd.xmm_setXmm_self _ _ _).trans (congrArg (fun x => (0 : BitVec 96) ++ x) ea)
  refine WP.block_cons_iff.mpr ⟨a, rfl, WP.block_cons_iff.mpr ⟨b, rfl, WP.block_cons_iff.mpr ⟨c, rfl, q c ?_ ?_⟩⟩⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Wp.Upd.setReg s .eax v
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · funext x
    show (if x = r then shufDwords (b.xmm r) 0 else if x = r then _ else s.xmm x) = if x = r then _ else s.xmm x
    rw [eb]
    by_cases hx : x = r
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]

theorem splat_mask : shufDwords ((0 : BitVec 96) ++ (0x0f0f0f0f : BitVec 32)) 0 = mask := by decide +kernel
theorem splat_c63 : shufDwords ((0 : BitVec 96) ++ (0x63636363 : BitVec 32)) 0 = c63 := by decide +kernel

/-- The tables, as the code loads them. -/
theorem TabSt.ld {s : State} {n : Nat} (h : TabSt d all B s₀ n s) : ∀ k < n,
    s.mem.readW (s.ea (at_ .edi (16 * k))) 128 = all.getD k 0 := fun k hk => by
  rw [at_, ea_mk, h.edi]; exact h.tab k hk

/-- The setup, when only XMM registers change. -/
theorem TabSt.setX {s : State} {n : Nat} (h : TabSt d all B s₀ n s) (f : XRegs) : TabSt d all B s₀ n (setX s f) :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame, h.saved, h.tab⟩

/-- SSE code that loads the scratch buffer's first `n` bytes. -/
def loadOk (n : Nat) (is : List Instr) : Bool :=
  is.all isX && (is.filterMap xmemOp).all fun m => m.base == .edi && decide (m.disp + 16 ≤ n)

/-- Such code, of the first `n` tables. -/
theorem TabSt.run {is rest : List Instr} {s : State} {Q : State → Prop} {n : Nat} (h : TabSt d all B s₀ n s)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hscr : reg32 B N ∈ s.wr) (hn : 16 * n ≤ N)
    (hc : loadOk (16 * n) is = true)
    (q : WP isa (.block rest) (Vperm.setX s (xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is)) Q) :
    WP isa (.block (is ++ rest)) s Q := by
  simp only [loadOk, Bool.and_eq_true] at hc
  obtain ⟨h1, h2⟩ := hc
  refine wp_x h1 (fun m hm => ?_) q
  obtain c := List.all_eq_true.mp h2 m hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  obtain ⟨b, o⟩ := m
  obtain ⟨e, l⟩ := c
  simp only at e l
  subst e
  rw [ea_mk, h.edi]
  exact in_rd (in_reg hscr hfit (by omega_using [l, hn]) (by decide))

/-- A table computed from the ones stored. -/
theorem seg_ok {is rest : List Instr} {s : State} {Q : State → Prop} {n : Nat} (h : TabSt d all B s₀ n s)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hN : d.saved + 16 ≤ N) (hscr : reg32 B N ∈ s.wr) (hn : 16 * n + 16 ≤ d.saved)
    (hc : loadOk (16 * n) is = true)
    (hv : xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is .xmm0 = all.getD n 0)
    (q : ∀ s', TabSt d all B s₀ (n + 1) s' → s'.wr = s.wr →
      s'.xmm = xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is → WP isa (.block rest) s' Q) :
    WP isa (.block (is ++ .movdquStore (at_ .edi (16 * n)) .xmm0 :: rest)) s Q := by
  refine h.run hfit hscr (by omega_using [hn, hN]) hc ?_
  generalize hf : xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is = f at hv q ⊢
  have hin : InRegions (Vperm.setX s f).wr (addr B (16 * n)) 16 :=
    in_reg hscr hfit (by omega_using [hn, hN]) (by decide)
  refine WP.block_cons_iff.mpr ⟨{ Vperm.setX s f with mem := s.mem.writeW (addr B (16 * n)) (all.getD n 0) }, ?_, ?_⟩
  · show (Vperm.setX s f).store128 ((Vperm.setX s f).ea ⟨.edi, 16 * n⟩) (f .xmm0) = _
    rw [ea_mk, hv, show (Vperm.setX s f).gpr .edi = B from h.edi]
    exact ite_eq_left hin
  · have h' : TabSt d all B s₀ n { Vperm.setX s f with mem := s.mem.writeW (addr B (16 * n)) (all.getD n 0) } :=
      h.store (w := 128) (by omega_using [hfit, hN]) (Nat.le_refl _) (by omega_using [hn]) (by decide) (all.getD n 0) rfl rfl rfl rfl rfl
    refine q _ { h' with tab := fun j hj => ?_ } rfl rfl
    by_cases e : j = n
    · subst e
      exact Mem.readW_writeW_self _ _ 16 _ (by decide)
    · exact h'.tab j (by omega_using [hj, e])

end

theorem Enc.derive_ok {N : Nat} {B : BitVec 32} {s₀ s : State} (h : TabSt enc Enc.all B s₀ 12 s)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hN : 480 ≤ N) (hscr : reg32 B N ∈ s.wr) :
    WP isa (.block enc.derive) s fun s' => TabSt enc Enc.all B s₀ 14 s' ∧ s'.xmm .xmm6 = inv ∧ s'.xmm .xmm7 = mask := by
  show WP isa (.block (splat .xmm7 0x0f0f0f0f ++ ([tl .xmm0 4, tl .xmm1 5, sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 12)) .xmm0 :: ([sb .xmm0 .xmm1, sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 13)) .xmm0 :: ([tl .xmm6 2] ++ []))))) s _
  refine wp_splat fun s₁ u₁ x₁ => ?_
  have h₁ : TabSt enc Enc.all B s₀ 12 s₁ :=
    ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
      u₁.rd.trans h.rd, u₁.wr.trans h.wr, by rw [u₁.mem]; exact h.frame, by rw [u₁.mem]; exact h.saved,
      by rw [u₁.mem]; exact h.tab⟩
  have t4 : s₁.mem.readW (s₁.ea (at_ .edi (16 * 4))) 128 = sr := h₁.ld 4 (by decide)
  have t5 : s₁.mem.readW (s₁.ea (at_ .edi (16 * 5))) 128 = rot := h₁.ld 5 (by decide)
  refine seg_ok h₁ hfit hN (by rw [u₁.wr]; exact hscr) (by decide) (by decide +kernel) ?_ fun s₂ h₂ w₂ x₂ => ?_
  · simp only [tl, sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t4, t5, sb_rot]
    decide +kernel
  have x₂0 : s₂.xmm .xmm0 = rsr := by
    rw [x₂]
    simp only [tl, sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t4, t5, sb_rot]
    decide +kernel
  have x₂1 : s₂.xmm .xmm1 = rot := by
    rw [x₂]
    simp only [tl, sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t5]
  have x₂7 : s₂.xmm .xmm7 = mask := by
    rw [x₂, xvals_keep _ _ _ _ (by decide), x₁, put_self, splat_mask]
  refine seg_ok h₂ hfit hN (by rw [w₂, u₁.wr]; exact hscr) (by decide) (by decide +kernel) ?_ fun s₃ h₃ w₃ x₃ => ?_
  · simp only [sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, x₂0, x₂1, sb_rot]
    decide +kernel
  refine h₃.run hfit (by rw [w₃, w₂, u₁.wr]; exact hscr) (by omega_using [hN]) (by decide +kernel)
    (WP.block_nil ⟨h₃.setX _, h₃.ld 2 (by decide), ?_⟩)
  show xvals _ _ _ _ = _
  rw [xvals_keep _ _ _ _ (by decide), x₃, xvals_keep _ _ _ _ (by decide), x₂7]

theorem Dec.derive_ok {N : Nat} {B : BitVec 32} {s₀ s : State} (h : TabSt dec Dec.all B s₀ 24 s)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hN : 720 ≤ N) (hscr : reg32 B N ∈ s.wr) :
    WP isa (.block dec.derive) s fun s' => TabSt dec Dec.all B s₀ 29 s' ∧ s'.xmm .xmm6 = inv ∧ s'.xmm .xmm7 = mask := by
  show WP isa (.block (splat .xmm7 0x0f0f0f0f ++ ([tl .xmm1 10, mv .xmm0 .xmm1, sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 24)) .xmm0 :: ([sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 25)) .xmm0 :: ([tl .xmm0 19, sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 26)) .xmm0 :: ([sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 27)) .xmm0 :: ([sb .xmm0 .xmm1] ++
    .movdquStore (at_ .edi (16 * 28)) .xmm0 :: ([tl .xmm6 0] ++ [])))))))) s _
  refine wp_splat fun s₁ u₁ x₁ => ?_
  have h₁ : TabSt dec Dec.all B s₀ 24 s₁ :=
    ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
      u₁.rd.trans h.rd, u₁.wr.trans h.wr, by rw [u₁.mem]; exact h.frame, by rw [u₁.mem]; exact h.saved,
      by rw [u₁.mem]; exact h.tab⟩
  have w₁ : reg32 B N ∈ s₁.wr := by rw [u₁.wr]; exact hscr
  have x₁7 : s₁.xmm .xmm7 = mask := by rw [x₁, put_self, splat_mask]
  -- What each segment keeps: the rotation in `xmm1` and the mask.
  have keep : ∀ {t t' : State} {is : List Instr}, t'.xmm = xvals (fun m => t.mem.readW (t.ea m) 128) t.xmm is →
      is.all (fun i => xdst i != some .xmm7) = true → is.all (fun i => xdst i != some .xmm1) = true →
      t.xmm .xmm7 = mask → t.xmm .xmm1 = rot → t'.xmm .xmm7 = mask ∧ t'.xmm .xmm1 = rot := fun e a b c c' => by
    rw [e, xvals_keep _ _ _ _ a, xvals_keep _ _ _ _ b]; exact ⟨c, c'⟩
  have t10 : s₁.mem.readW (s₁.ea (at_ .edi (16 * 10))) 128 = rot := h₁.ld 10 (by decide)
  refine seg_ok h₁ hfit hN w₁ (by decide) (by decide +kernel) ?_ fun s₂ h₂ w₂ x₂ => ?_
  · simp only [tl, sb, mv, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t10, mvE, sb_rot]
    decide +kernel
  have x₂0 : s₂.xmm .xmm0 = Impl.Aes.Vperm.Dec.rot2 := by
    rw [x₂]
    simp only [tl, sb, mv, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t10, mvE, sb_rot]
    decide +kernel
  have x₂1 : s₂.xmm .xmm1 = rot := by
    rw [x₂]
    simp only [tl, sb, mv, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t10]
  have x₂7 : s₂.xmm .xmm7 = mask := by rw [x₂, xvals_keep _ _ _ _ (by decide), x₁7]
  have w₂' : reg32 B N ∈ s₂.wr := by rw [w₂]; exact w₁
  refine seg_ok h₂ hfit hN w₂' (by decide) (by decide +kernel) ?_ fun s₃ h₃ w₃ x₃ => ?_
  · simp only [sb, xvals, xval, put_apply, ite_true, x₂0, x₂1, sb_rot]
    decide +kernel
  obtain ⟨x₃7, x₃1⟩ := keep x₃ (by decide) (by decide) x₂7 x₂1
  have w₃' : reg32 B N ∈ s₃.wr := by rw [w₃]; exact w₂'
  have t19 : s₃.mem.readW (s₃.ea (at_ .edi (16 * 19))) 128 = Impl.Aes.Vperm.Dec.p0 := h₃.ld 19 (by decide)
  refine seg_ok h₃ hfit hN w₃' (by decide) (by decide +kernel) ?_ fun s₄ h₄ w₄ x₄ => ?_
  · simp only [tl, sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t19, x₃1, sb_rot]
    decide +kernel
  have x₄0 : s₄.xmm .xmm0 = Impl.Aes.Vperm.Dec.p1 := by
    rw [x₄]
    simp only [tl, sb, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, t19, x₃1, sb_rot]
    decide +kernel
  obtain ⟨x₄7, x₄1⟩ := keep x₄ (by decide) (by decide) x₃7 x₃1
  have w₄' : reg32 B N ∈ s₄.wr := by rw [w₄]; exact w₃'
  refine seg_ok h₄ hfit hN w₄' (by decide) (by decide +kernel) ?_ fun s₅ h₅ w₅ x₅ => ?_
  · simp only [sb, xvals, xval, put_apply, ite_true, x₄0, x₄1, sb_rot]
    decide +kernel
  have x₅0 : s₅.xmm .xmm0 = Impl.Aes.Vperm.Dec.p2 := by
    rw [x₅]
    simp only [sb, xvals, xval, put_apply, ite_true, x₄0, x₄1, sb_rot]
    decide +kernel
  obtain ⟨x₅7, x₅1⟩ := keep x₅ (by decide) (by decide) x₄7 x₄1
  have w₅' : reg32 B N ∈ s₅.wr := by rw [w₅]; exact w₄'
  refine seg_ok h₅ hfit hN w₅' (by decide) (by decide +kernel) ?_ fun s₆ h₆ w₆ x₆ => ?_
  · simp only [sb, xvals, xval, put_apply, ite_true, x₅0, x₅1, sb_rot]
    decide +kernel
  obtain ⟨x₆7, -⟩ := keep x₆ (by decide) (by decide) x₅7 x₅1
  refine h₆.run hfit (by rw [w₆]; exact w₅') (by omega_using [hN]) (by decide +kernel)
    (WP.block_nil ⟨h₆.setX _, h₆.ld 0 (by decide), ?_⟩)
  show xvals _ _ _ _ = _
  rw [xvals_keep _ _ _ _ (by decide), x₆7]

/-- What the setup leaves, for a direction with tables `all`. -/
structure SetupOk (d : Dir) (all : List (BitVec 128)) : Prop where
  len : d.slots = 16 * all.length
  le : d.slots ≤ 464
  tabs : ∀ j < d.tabs.length, d.tabs.getD j 0 = all.getD j 0
  tabsLe : d.tabs.length ≤ all.length
  derive : ∀ {N : Nat} {B : BitVec 32} {s₀ s : State}, TabSt d all B s₀ d.tabs.length s → B.toNat + N ≤ 2 ^ 32 →
    d.saved + 16 ≤ N → reg32 B N ∈ s.wr → WP isa (.block d.derive) s fun s' =>
      TabSt d all B s₀ all.length s' ∧ s'.xmm .xmm6 = inv ∧ s'.xmm .xmm7 = mask

theorem Enc.setupOk : SetupOk enc Enc.all where
  len := rfl
  le := by decide
  tabs := by decide +kernel
  tabsLe := by decide
  derive := Enc.derive_ok

theorem Dec.setupOk : SetupOk dec Dec.all where
  len := rfl
  le := by decide
  tabs := by decide +kernel
  tabsLe := by decide
  derive := Dec.derive_ok

/-- The setup. -/
theorem setup_ok {d : Dir} {all : List (BitVec 128)} (hd : SetupOk d all) {k N : Nat} {B : BitVec 32} {s₀ : State}
    (ha : Args k N B s₀) (hN : d.saved + 16 ≤ N) :
    WP isa (.block (d.setup k)) s₀ fun s => TabSt d all B s₀ all.length s ∧ s.xmm .xmm6 = inv ∧ s.xmm .xmm7 = mask := by
  have hfit := ha.fit
  rw [show d.setup k = .mov .eax (.mem ⟨.esp, 4 + 4 * k⟩) :: (Spill.saveCode .eax d.savedRegs ++
    (.mov .edi (.reg .eax) :: (storeWords (16 * 0) (words d.tabs) ++ d.derive))) by
      simp only [Dir.setup, List.append_assoc]; rfl]
  refine Wp.wp_ldm (B := s₀.gpr .esp) rfl ha.argIn fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := u₁.gpr.trans ha.arg
  have hfits : Spill.Fits (d.saved + 16) d.savedRegs := by
    refine ⟨fun p hp => ?_, ?_⟩
    · simp only [Dir.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> omega_using []
    · simp only [Dir.savedRegs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true, false_imp_iff, implies_true]
      omega_using []
  have hfit' : B.toNat + (d.saved + 16) ≤ 2 ^ 32 := by omega_using [hfit, hN]
  refine Spill.save_ok d.savedRegs (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [e₁, u₁.wr]
    exact in_reg ha.scr hfit (by have := hfits.1 p hp; omega_using [this, hN]) (by decide)
  rw [e₁] at u₂
  refine Wp.wp_mov fun s₃ u₃ => ?_
  have hm : s₃.mem = Spill.saveMem s₀.mem (addr B) s₀.gpr d.savedRegs := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    refine Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp => u₁.other _ ?_
    simp only [Dir.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact Reg.noConfusion
  have h₃ : TabSt d all B s₀ 0 s₃ :=
    { edi := by rw [u₃.gpr, u₂.gpr, e₁]
      esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
      rd := by rw [u₃.rd, u₂.rd, u₁.rd]
      wr := by rw [u₃.wr, u₂.wr, u₁.wr]
      frame := by
        rw [hm]
        exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ (Spill.contains_of_fits hfit' hfits)
      saved := by rw [hm]; exact Spill.saveMem_saved_addr _ _ hfits hfit'
      tab := fun j hj => absurd hj (Nat.not_lt_zero j) }
  have hl := hd.len
  have ht := hd.tabsLe
  refine storeWords_ok (Q := fun s => TabSt d all B s₀ all.length s ∧ s.xmm .xmm6 = inv ∧ s.xmm .xmm7 = mask) hfit'
    d.tabs (fun j hj => by rw [Nat.zero_add]; exact hd.tabs j hj)
    (fun o ho => by rw [h₃.wr]; exact in_reg ha.scr hfit (by omega_using [ho, hN]) (by decide)) h₃
    (by rw [Dir.saved]; omega_using [hl, ht]) fun s₄ h₄ => ?_
  rw [Nat.zero_add] at h₄
  exact hd.derive h₄ hfit hN (by rw [h₄.wr]; exact ha.scr)

/-! ## The slots -/

/-- The schedule's pointer `S` and the rounds `R`: arguments 0 and 1. -/
structure Sched (N : Nat) (B S : BitVec 32) (R : Nat) (w : List Byte) (s₀ : State) : Prop where
  fit : S.toNat + 240 ≤ 2 ^ 32
  sch : reg32 S 240 ∈ s₀.rd ++ s₀.wr
  sep : (reg32 S 240).Disjoint (reg32 B N)
  argIn : ∀ i < 2, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4
  argSep : ∀ i < 2, Region.Disjoint ⟨addr (s₀.gpr .esp) (4 + 4 * i), 4⟩ (reg32 B N)
  arg0 : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = S
  arg1 : s₀.mem.readW (addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  key : ∀ j ≤ R, KeyIs (s₀.mem.readW (addr S (16 * j)) 128) (roundKey w j)

theorem Sched.le {N : Nat} {B S : BitVec 32} {R : Nat} {w : List Byte} {s₀ : State} (h : Sched N B S R w s₀) :
    10 ≤ R ∧ R ≤ 14 := by
  rcases h.rounds with h | h | h <;> omega_using [h]

/-- The slots, the first `j` written, with `esi` at `p` and `ebx` at slot `q`. -/
structure SlotSt (d : Dir) (all : List (BitVec 128)) (B : BitVec 32) (slotKey : Nat → BitVec 128) (s₀ : State)
    (j : Nat) (p : BitVec 32) (q c : Nat) (s : State) : Prop where
  tab : TabSt d all B s₀ all.length s
  x6 : s.xmm .xmm6 = inv
  x7 : s.xmm .xmm7 = mask
  slot : ∀ i < j, s.mem.readW (addr B (d.slots + 16 * i)) 128 = slotKey i
  esi : s.gpr .esi = p
  ebx : s.gpr .ebx = B + BitVec.ofNat 32 (d.slots + 16 * q)
  ecx : s.gpr .ecx = BitVec.ofNat 32 c

section
variable {d : Dir} {all : List (BitVec 128)} {N : Nat} {B S : BitVec 32} {k R : Nat} {w : List Byte} {s₀ : State}
  {slotKey : Nat → BitVec 128}

theorem TabSt.sub {s : State} {n : Nat} (h : TabSt d all B s₀ n s) (hN : d.saved + 16 ≤ N) : Frame [reg32 B N] s₀.mem s.mem :=
  h.frame.sub fun r hr => ⟨reg32 B N, List.mem_cons_self, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix hN⟩

/-- Argument `i`, in any state of the setup. -/
theorem TabSt.arg {s : State} {n i : Nat} (h : TabSt d all B s₀ n s) (hN : d.saved + 16 ≤ N) (hs : Sched N B S R w s₀) (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = s₀.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 := by
  rw [h.rd, h.wr, h.esp]
  refine ⟨hs.argIn i hi, (h.sub hN).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.argSep i hi

/-- Round key `j`, in any state of the setup. -/
theorem TabSt.key {s : State} {n j : Nat} (h : TabSt d all B s₀ n s) (hN : d.saved + 16 ≤ N) (hs : Sched N B S R w s₀) (hj : j ≤ 14) :
    InRegions (s.rd ++ s.wr) (addr S (16 * j)) 16 ∧
      s.mem.readW (addr S (16 * j)) 128 = s₀.mem.readW (addr S (16 * j)) 128 := by
  rw [h.rd, h.wr]
  refine ⟨in_reg hs.sch hs.fit (by omega_using [hj]) (by decide),
    (h.sub hN).readW (reg_contains hs.fit (by omega_using [hj]) (by decide)) (fun r hr => ?_) (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.sep

/-- A store of slot `j`, where `ebx` points: a step of `prep`. -/
theorem SlotSt.store {s : State} {j c : Nat} {p : BitVec 32} {x : XReg} (hd : SetupOk d all)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hN : d.saved + 16 ≤ N) (hscr : reg32 B N ∈ s.wr)
    (h : SlotSt d all B slotKey s₀ j p j c s) (hj : j ≤ 14) (hx : s.xmm x = slotKey j) {rest : List Instr}
    {Q : State → Prop}
    (q : ∀ s', SlotSt d all B slotKey s₀ (j + 1) p j c s' → s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (.movdquStore (at_ .ebx 0) x :: rest)) s Q := by
  have hl := hd.len
  have hsv : d.saved = d.slots + 240 := rfl
  have he : addr (s.gpr .ebx) 0 = addr B (d.slots + 16 * j) := by rw [h.ebx, addr_add, Nat.add_zero]
  refine WP.block_cons_iff.mpr ⟨{ s with mem := s.mem.writeW (addr B (d.slots + 16 * j)) (slotKey j) }, ?_, ?_⟩
  · show s.store128 (s.ea ⟨.ebx, 0⟩) (s.xmm x) = _
    rw [ea_mk, he, hx]
    exact ite_eq_left (in_reg hscr hfit (by omega_using [hj, hN, hsv]) (by decide))
  · have h' : TabSt d all B s₀ all.length { s with mem := s.mem.writeW (addr B (d.slots + 16 * j)) (slotKey j) } :=
      h.tab.store (w := 128) (by omega_using [hfit, hN]) (by omega_using [hl]) (by omega_using [hj, hsv]) (by decide)
        (slotKey j) rfl rfl rfl rfl rfl
    refine q _ ⟨h', h.x6, h.x7, fun i hi => ?_, h.esi, h.ebx, h.ecx⟩ rfl
    show (s.mem.writeW (addr B (d.slots + 16 * j)) (slotKey j)).readW (addr B (d.slots + 16 * i)) 128 = _
    by_cases e : i = j
    · subst e
      exact Mem.readW_writeW_self _ _ 16 _ (by decide)
    · rw [← h.slot i (by omega_using [hi, e])]
      refine Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨addr B (d.slots + 16 * i), 16⟩)
        (r₂ := ⟨addr B (d.slots + 16 * j), 16⟩) (part_disj (N := N) hfit (by omega_using [hi, hj, hN, hsv])
        (by omega_using [hj, hN, hsv]) (.inl (by omega_using [hi, e]))) (Region.contains_self _ _)
        (Region.contains_self _ _)) (by decide)

/-- Where `prep` ends. -/
theorem SlotSt.coreIn {s : State} {p : BitVec 32} {q c : Nat} (hfit : B.toNat + N ≤ 2 ^ 32) (hN : d.saved + 16 ≤ N)
    (hscr : reg32 B N ∈ s₀.wr) (hs : Sched N B S R w s₀)
    (h : SlotSt d all B slotKey s₀ (R + 1) p q c s) : CoreIn d all N B R slotKey s where
  edi := h.tab.edi
  fit := hfit
  room := by have e : d.saved = d.slots + 240 := rfl; omega_using [hN, e]
  scr := by rw [h.tab.wr]; exact hscr
  tab := h.tab.tab
  slot := fun j hj => h.slot j (by omega_using [hj])
  x6 := h.x6
  x7 := h.x7
  rounds := hs.rounds
  argIn := (h.tab.arg hN hs (i := 1) (by decide)).1
  arg := (h.tab.arg hN hs (i := 1) (by decide)).2.trans hs.arg1

/-- Other general-purpose registers. -/
theorem SlotSt.gpr {s s' : State} {j : Nat} {p p' : BitVec 32} {q q' c c' : Nat}
    (h : SlotSt d all B slotKey s₀ j p q c s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hx : s'.xmm = s.xmm) (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp)
    (hesi : s'.gpr .esi = p') (hebx : s'.gpr .ebx = B + BitVec.ofNat 32 (d.slots + 16 * q'))
    (hecx : s'.gpr .ecx = BitVec.ofNat 32 c') : SlotSt d all B slotKey s₀ j p' q' c' s' where
  tab := ⟨hedi.trans h.tab.edi, hesp.trans h.tab.esp, hrd.trans h.tab.rd, hwr.trans h.tab.wr,
    by rw [hm]; exact h.tab.frame, by rw [hm]; exact h.tab.saved, by rw [hm]; exact h.tab.tab⟩
  x6 := by rw [hx]; exact h.x6
  x7 := by rw [hx]; exact h.x7
  slot := by rw [hm]; exact h.slot
  esi := hesi
  ebx := hebx
  ecx := hecx

/-- SSE code that loads 16 bytes at `esi` and the first `n` bytes of the
scratch buffer, and keeps `xmm6` and `xmm7`. -/
def prepOk (n : Nat) (is : List Instr) : Bool :=
  is.all isX && (is.filterMap xmemOp).all (fun m =>
    decide (m = at_ .esi 0) || (m.base == .edi && decide (m.disp + 16 ≤ n))) &&
  is.all (fun i => xdst i != some .xmm6) && is.all (fun i => xdst i != some .xmm7)

theorem SlotSt.run {is rest : List Instr} {s : State} {Q : State → Prop} {j : Nat} {p : BitVec 32} {q c : Nat}
    (h : SlotSt d all B slotKey s₀ j p q c s) (hfit : B.toNat + N ≤ 2 ^ 32) (hscr : reg32 B N ∈ s.wr) {n : Nat}
    (hn : n ≤ N) (hin : InRegions (s.rd ++ s.wr) (addr p 0) 16) (hc : prepOk n is = true)
    (k : ∀ s', SlotSt d all B slotKey s₀ j p q c s' → s'.wr = s.wr →
      s'.xmm = xvals (fun m => s.mem.readW (s.ea m) 128) s.xmm is → WP isa (.block rest) s' Q) :
    WP isa (.block (is ++ rest)) s Q := by
  simp only [prepOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine wp_x h1 (fun m hm => ?_) (k _ ⟨h.tab.setX _, (xvals_keep _ _ _ _ h3).trans h.x6,
    (xvals_keep _ _ _ _ h4).trans h.x7, h.slot, h.esi, h.ebx, h.ecx⟩ rfl rfl)
  obtain c := List.all_eq_true.mp h2 m hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  rcases c with rfl | ⟨e, l⟩
  · rw [at_, ea_mk, h.esi]; exact hin
  · obtain ⟨b, o⟩ := m
    simp only at e l
    subst e
    rw [ea_mk, h.tab.edi]
    exact in_rd (in_reg hscr hfit (by omega_using [l, hn]) (by decide))

end

/-- The round keys, as the schedule has them. -/
abbrev keyAt (S : BitVec 32) (s₀ : State) (j : Nat) : BitVec 128 := s₀.mem.readW (addr S (16 * j)) 128

/-! ### Encryption -/

namespace Enc

open VG.Impl.Aes.X86.Vperm.Enc

variable {N : Nat} {B S : BitVec 32} {R : Nat} {w : List Byte} {s₀ : State}

theorem prepHead_ok (hN : enc.saved + 16 ≤ N) (hs : Sched N B S R w s₀) {s : State}
    (h : TabSt enc all B s₀ all.length s) (h6 : s.xmm .xmm6 = inv) (h7 : s.xmm .xmm7 = mask)
    {sk : Nat → BitVec 128} :
    WP isa (.block prepHead) s (SlotSt enc all B sk s₀ 0 (S + BitVec.ofNat 32 (16 * 0)) 0 R) := by
  obtain ⟨i0, a0⟩ := h.arg hN hs (i := 0) (by decide)
  obtain ⟨i1, a1⟩ := h.arg hN hs (i := 1) (by decide)
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .edi = s.gpr .edi ∧
    s'.gpr .esp = s.gpr .esp ∧ s'.gpr .esi = S ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
    s'.gpr .ebx = B + BitVec.ofNat 32 slots) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_ldm (B := s.gpr .esp) (o := 4) rfl i0 fun s₁ u₁ => ?_
    refine Wp.wp_ldm (B := s.gpr .esp) (o := 8) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact i1) fun s₂ u₂ => ?_
    refine Wp.wp_mov fun s₃ u₃ => Wp.wp_addi fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      exact a0.trans hs.arg0
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact a1.trans hs.arg1
    · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  · obtain ⟨⟨m, rd, wr, e, p, si, cx, bx⟩, x⟩ := hh
    exact ⟨⟨e.trans h.edi, p.trans h.esp, rd.trans h.rd, wr.trans h.wr, by rw [m]; exact h.frame,
      by rw [m]; exact h.saved, by rw [m]; exact h.tab⟩, by rw [x]; exact h6, by rw [x]; exact h7,
      fun i hi => absurd hi (Nat.not_lt_zero i), by rw [si]; exact (BitVec.add_zero S).symm, bx, cx⟩

/-- A round key's slot. -/
theorem prepBody_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : enc.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {j : Nat} (hj : j < R) {s : State}
    (h : SlotSt enc all B (slotKey R (keyAt S s₀)) s₀ j (S + BitVec.ofNat 32 (16 * j)) j (R - j) s) :
    WP isa (.block prepBody) s fun s' =>
      SlotSt enc all B (slotKey R (keyAt S s₀)) s₀ (j + 1) (S + BitVec.ofNat 32 (16 * (j + 1))) (j + 1) (R - (j + 1)) s' ∧
        s'.zf = some (decide (R = j + 1)) := by
  have hR := hs.le
  obtain ⟨ki, ke⟩ := h.tab.key hN hs (j := j) (by omega_using [hj, hR])
  have he : addr (S + BitVec.ofNat 32 (16 * j)) 0 = addr S (16 * j) := by rw [addr_add, Nat.add_zero]
  rw [prepBody, show ([.movdquLoad .xmm0 (at_ .esi 0)] : List Instr) ++ keyx ++ _ = (.movdquLoad .xmm0 (at_ .esi 0) :: keyx) ++
    ([.movdquStore (at_ .ebx 0) .xmm0, .alu .add .esi (.imm 16), .alu .add .ebx (.imm 16),
      .alu .sub .ecx (.imm 1)] : List Instr) from rfl]
  refine h.run hfit (by rw [h.tab.wr]; exact hscr) (n := 224) (by omega_using [hN, show enc.saved = 464 from rfl])
    (by rw [he]; exact ki) (by decide +kernel) fun s₁ h₁ w₁ x₁ => ?_
  refine h₁.store setupOk hfit hN (by rw [w₁, h.tab.wr]; exact hscr) (by omega_using [hj, hR]) ?_ fun s₂ h₂ w₂ => ?_
  · rw [x₁, slotKey, ite_eq_left hj, xvals_load, keyx_val (fun k hk => h.tab.ld k hk)
      ((put_ne _ _ (by decide)).trans h.x7), put_self, at_, ea_mk, h.esi, he, ke]
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₂.mem ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr ∧ s'.gpr .edi = s₂.gpr .edi ∧
    s'.gpr .esp = s₂.gpr .esp ∧ s'.gpr .esi = s₂.gpr .esi + 16 ∧ s'.gpr .ebx = s₂.gpr .ebx + 16 ∧
    s'.gpr .ecx = s₂.gpr .ecx - 1 ∧ s'.zf = some (s₂.gpr .ecx - 1 == 0)) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_addi fun s₃ u₃ => Wp.wp_addi fun s₄ u₄ => Wp.wp_subi fun s₅ u₅ _ z =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.mem, u₄.mem, u₃.mem]
    · rw [u₅.rd, u₄.rd, u₃.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide)]
    · rw [z, u₄.other _ (by decide), u₃.other _ (by decide)]
  · obtain ⟨⟨m, rd, wr, e, p, si, bx, cx, z⟩, x⟩ := hh
    have ec : s₂.gpr .ecx - 1 = BitVec.ofNat 32 (R - (j + 1)) := by
      rw [h₂.ecx, Wp.ofNat_pred (by omega_using [hj])]; congr 1
    refine ⟨h₂.gpr m rd wr x e p ?_ ?_ (cx.trans ec), ?_⟩
    · rw [si, h₂.esi, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
    · rw [bx, h₂.ebx, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
    · rw [z, ec, Wp.ofNat_beq_zero (by omega_using [hR])]
      exact congrArg some (decide_eq_decide.mpr (by omega_using [hj]))

/-- The slots written. -/
theorem prep_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : enc.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {s : State} (h : TabSt enc all B s₀ all.length s) (h6 : s.xmm .xmm6 = inv)
    (h7 : s.xmm .xmm7 = mask) :
    WP isa enc.prep s fun s' => TabSt enc all B s₀ all.length s' ∧
      CoreIn enc all N B R (slotKey R (keyAt S s₀)) s' := by
  have hR := hs.le
  refine WP.seq (WP.mono (prepHead_ok hN hs h h6 h7 (sk := slotKey R (keyAt S s₀))) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := SlotSt enc all B (slotKey R (keyAt S s₀)) s₀ R (S + BitVec.ofNat 32 (16 * R)) R 0) ?_
    fun s₂ h₂ => ?_)
  · refine WP.loop (M := isa) (fun n s' => ∃ j, n = R - j ∧ j < R ∧
      SlotSt enc all B (slotKey R (keyAt S s₀)) s₀ j (S + BitVec.ofNat 32 (16 * j)) j (R - j) s')
      (fun n s' ⟨j, hn, hj, i⟩ => ?_) R s₁ ⟨0, rfl, by omega_using [hR], h₁⟩
    refine WP.mono (prepBody_ok hfit hN hscr hs hj i) fun s'' ⟨i', z⟩ => ?_
    by_cases e : R = j + 1
    · refine .inl ⟨by simp [eval, z, e], ?_⟩
      have i'' := i'
      rw [← e, Nat.sub_self] at i''
      exact i''
    · exact .inr ⟨by simp [eval, z, e], R - (j + 1), by omega_using [hn, hj, e], j + 1, rfl, by omega_using [hj, e], i'⟩
  · obtain ⟨ki, ke⟩ := h₂.tab.key hN hs (j := R) (by omega_using [hR])
    have he : addr (S + BitVec.ofNat 32 (16 * R)) 0 = addr S (16 * R) := by rw [addr_add, Nat.add_zero]
    rw [show prepTail = splat .xmm1 0x63636363 ++ ([.movdquLoad .xmm0 (at_ .esi 0), px .xmm0 .xmm1] ++
      [.movdquStore (at_ .ebx 0) .xmm0]) from rfl]
    refine wp_splat fun s₃ u₃ x₃ => ?_
    have h₃ : SlotSt enc all B (slotKey R (keyAt S s₀)) s₀ R (S + BitVec.ofNat 32 (16 * R)) R 0 s₃ :=
      ⟨⟨by rw [u₃.other _ (by decide)]; exact h₂.tab.edi, by rw [u₃.other _ (by decide)]; exact h₂.tab.esp,
        u₃.rd.trans h₂.tab.rd, u₃.wr.trans h₂.tab.wr, by rw [u₃.mem]; exact h₂.tab.frame,
        by rw [u₃.mem]; exact h₂.tab.saved, by rw [u₃.mem]; exact h₂.tab.tab⟩,
        by rw [x₃, put_ne _ _ (by decide)]; exact h₂.x6, by rw [x₃, put_ne _ _ (by decide)]; exact h₂.x7,
        by rw [u₃.mem]; exact h₂.slot, by rw [u₃.other _ (by decide)]; exact h₂.esi,
        by rw [u₃.other _ (by decide)]; exact h₂.ebx, by rw [u₃.other _ (by decide)]; exact h₂.ecx⟩
    refine h₃.run hfit (by rw [h₃.tab.wr]; exact hscr) (n := 0) (Nat.zero_le _)
      (by rw [he, h₃.tab.rd, h₃.tab.wr, ← h₂.tab.rd, ← h₂.tab.wr]; exact ki) (by decide +kernel) fun s₄ h₄ w₄ x₄ => ?_
    refine h₄.store setupOk hfit hN (by rw [w₄, h₃.tab.wr]; exact hscr) (by omega_using [hR]) ?_ fun s₅ h₅ _ =>
      WP.block_nil ⟨h₅.tab, h₅.coreIn hfit hN hscr hs⟩
    rw [x₄]
    simp only [px, xvals, xval, put_apply, reduceCtorEq, ite_true, ite_false, pxE, x₃, splat_c63]
    rw [slotKey, ite_eq_right (Nat.lt_irrefl R), at_, ea_mk, h₃.esi, he, u₃.mem, ke]

end Enc

/-! ### Decryption -/

namespace Dec

open VG.Impl.Aes.X86.Vperm.Dec VG.Impl.Aes.Vperm.Dec VG.Proof.Aes.Vperm.Dec

variable {N : Nat} {B S : BitVec 32} {R : Nat} {w : List Byte} {s₀ : State}

theorem dbl4 : ∀ {r : Nat}, BitVec.ofNat 32 r + BitVec.ofNat 32 r + (BitVec.ofNat 32 r + BitVec.ofNat 32 r) +
    (BitVec.ofNat 32 r + BitVec.ofNat 32 r + (BitVec.ofNat 32 r + BitVec.ofNat 32 r)) +
    (BitVec.ofNat 32 r + BitVec.ofNat 32 r + (BitVec.ofNat 32 r + BitVec.ofNat 32 r) +
    (BitVec.ofNat 32 r + BitVec.ofNat 32 r + (BitVec.ofNat 32 r + BitVec.ofNat 32 r))) = BitVec.ofNat 32 (16 * r) := by
  intro r
  simp only [← BitVec.ofNat_add]
  exact congrArg _ (by omega_using [])

/-- A round key copied to its slot. -/
theorem copyKey_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : dec.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {j c : Nat} (hj : j ≤ R) (hjR : j = 0 ∨ j = R) {s : State}
    (h : SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ j (S + BitVec.ofNat 32 (16 * (R - j))) j c s) :
    WP isa (.block copyKey) s
      (SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ (j + 1) (S + BitVec.ofNat 32 (16 * (R - j))) j c) := by
  have hR := hs.le
  obtain ⟨ki, ke⟩ := h.tab.key hN hs (j := R - j) (by omega_using [hR])
  have he : addr (S + BitVec.ofNat 32 (16 * (R - j))) 0 = addr S (16 * (R - j)) := by rw [addr_add, Nat.add_zero]
  rw [show copyKey = ([.movdquLoad .xmm0 (at_ .esi 0)] : List Instr) ++ [.movdquStore (at_ .ebx 0) .xmm0] from rfl]
  refine h.run hfit (by rw [h.tab.wr]; exact hscr) (n := 0) (Nat.zero_le _) (by rw [he]; exact ki) (by decide +kernel)
    fun s₁ h₁ w₁ x₁ => ?_
  refine h₁.store setupOk hfit hN (by rw [w₁, h.tab.wr]; exact hscr) (by omega_using [hj, hR]) ?_ fun s₂ h₂ _ =>
    WP.block_nil h₂
  rw [x₁, xvals_load, xvals, put_self, slotKey, ite_eq_left hjR, at_, ea_mk, h.esi, he, ke]

theorem prepHead_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : dec.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {s : State}
    (h : TabSt dec all B s₀ all.length s) (h6 : s.xmm .xmm6 = inv) (h7 : s.xmm .xmm7 = mask) :
    WP isa (.block prepHead) s
      (SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ 1 (S + BitVec.ofNat 32 (16 * R)) 0 (R - 1)) := by
  have hR := hs.le
  obtain ⟨i0, a0⟩ := h.arg hN hs (i := 0) (by decide)
  obtain ⟨i1, a1⟩ := h.arg hN hs (i := 1) (by decide)
  rw [show prepHead = ([.mov .esi (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .eax (.reg .ecx),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .esi (.reg .eax), .mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 slots)),
      .alu .sub .ecx (.imm 1)] : List Instr) ++ copyKey from rfl, WP.block_append_iff]
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .edi = s.gpr .edi ∧
    s'.gpr .esp = s.gpr .esp ∧ s'.gpr .esi = S + BitVec.ofNat 32 (16 * R) ∧ s'.gpr .ecx = BitVec.ofNat 32 (R - 1) ∧
    s'.gpr .ebx = B + BitVec.ofNat 32 slots) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_ldm (B := s.gpr .esp) (o := 4) rfl i0 fun s₁ u₁ => ?_
    refine Wp.wp_ldm (B := s.gpr .esp) (o := 8) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact i1) fun s₂ u₂ => ?_
    refine Wp.wp_mov fun s₃ u₃ => Wp.wp_add fun s₄ u₄ _ => Wp.wp_add fun s₅ u₅ _ => Wp.wp_add fun s₆ u₆ _ =>
      Wp.wp_add fun s₇ u₇ _ => Wp.wp_add fun s₈ u₈ _ => Wp.wp_mov fun s₉ u₉ => Wp.wp_addi fun t₁ v₁ =>
      Wp.wp_subi fun t₂ v₂ _ _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v₂.mem, v₁.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [v₂.rd, v₁.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [v₂.wr, v₁.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · have e : s₇.gpr .eax = BitVec.ofNat 32 (16 * R) := by
        rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, a1, hs.arg1]
        exact dbl4
      rw [v₂.other _ (by decide), v₁.other _ (by decide), u₉.other _ (by decide), u₈.gpr, e,
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      exact congrArg (· + _) (a0.trans hs.arg0)
    · rw [v₂.gpr, v₁.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, a1, hs.arg1]
      exact Wp.ofNat_pred (by omega_using [hR])
    · rw [v₂.other _ (by decide), v₁.gpr, u₉.gpr, u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  · obtain ⟨⟨m, rd, wr, e, p, si, cx, bx⟩, x⟩ := hh
    exact copyKey_ok hfit hN hscr hs (j := 0) (Nat.zero_le _) (.inl rfl)
      ⟨⟨e.trans h.edi, p.trans h.esp, rd.trans h.rd, wr.trans h.wr, by rw [m]; exact h.frame,
        by rw [m]; exact h.saved, by rw [m]; exact h.tab⟩, by rw [x]; exact h6, by rw [x]; exact h7,
        fun i hi => absurd hi (Nat.not_lt_zero i), si, bx, cx⟩

/-- To the round key before, and the next slot. -/
theorem prepStep_ok {rest : List Instr} {Q : State → Prop} {sk : Nat → BitVec 128} {j c : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ R) {s : State} (h : SlotSt dec all B sk s₀ j (S + BitVec.ofNat 32 (16 * (R - (j - 1)))) (j - 1) c s)
    (q : ∀ s', SlotSt dec all B sk s₀ j (S + BitVec.ofNat 32 (16 * (R - j))) j c s' → WP isa (.block rest) s' Q) :
    WP isa (.block (prepStep ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .edi = s.gpr .edi ∧
    s'.gpr .esp = s.gpr .esp ∧ s'.gpr .esi = s.gpr .esi - 16 ∧ s'.gpr .ebx = s.gpr .ebx + 16 ∧
    s'.gpr .ecx = s.gpr .ecx) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_subi fun s₁ u₁ _ _ => Wp.wp_addi fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₂.mem, u₁.mem]
    · rw [u₂.rd, u₁.rd]
    · rw [u₂.wr, u₁.wr]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₂.other _ (by decide), u₁.gpr]
    · rw [u₂.gpr, u₁.other _ (by decide)]
    · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨⟨m, rd, wr, e, p, si, bx, cx⟩, x⟩ := hh
    refine q s' (h.gpr m rd wr x e p ?_ ?_ (cx.trans h.ecx))
    · rw [si, h.esi, show 16 * (R - (j - 1)) = 16 * (R - j) + 16 by omega_using [hj1, hj], BitVec.ofNat_add,
        ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _
    · rw [bx, h.ebx, BitVec.add_assoc]
      exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [hj1])))

/-- A middle round key's slot. -/
theorem prepBody_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : dec.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {j : Nat} (hj1 : 1 ≤ j) (hj : j < R) {s : State}
    (h : SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ j (S + BitVec.ofNat 32 (16 * (R - (j - 1)))) (j - 1) (R - j) s) :
    WP isa (.block prepBody) s fun s' =>
      SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ (j + 1) (S + BitVec.ofNat 32 (16 * (R - j))) j (R - (j + 1)) s' ∧
        s'.zf = some (decide (R = j + 1)) := by
  have hR := hs.le
  rw [prepBody, show prepStep ++ ([.movdquLoad .xmm0 (at_ .esi 0)] : List Instr) ++ key ++ _ =
    prepStep ++ ((.movdquLoad .xmm0 (at_ .esi 0) :: key) ++
    ([.movdquStore (at_ .ebx 0) .xmm2, .alu .sub .ecx (.imm 1)] : List Instr)) from rfl]
  refine prepStep_ok hj1 (by omega_using [hj]) h fun s₁ h₁ => ?_
  obtain ⟨ki, ke⟩ := h₁.tab.key hN hs (j := R - j) (by omega_using [hR])
  have he : addr (S + BitVec.ofNat 32 (16 * (R - j))) 0 = addr S (16 * (R - j)) := by rw [addr_add, Nat.add_zero]
  refine h₁.run hfit (by rw [h₁.tab.wr]; exact hscr) (n := 464) (by omega_using [hN, show dec.saved = 704 from rfl])
    (by rw [he]; exact ki) (by decide +kernel) fun s₂ h₂ w₂ x₂ => ?_
  refine h₂.store setupOk hfit hN (by rw [w₂, h₁.tab.wr]; exact hscr) (by omega_using [hj, hR]) ?_ fun s₃ h₃ w₃ => ?_
  · rw [x₂, slotKey, ite_eq_right (by omega_using [hj1, hj]), xvals_load, key_val (fun k hk => h₁.tab.ld k hk)
      ((put_ne _ _ (by decide)).trans h₁.x7), put_self, at_, ea_mk, h₁.esi, he, ke]
  refine WP.mono (wp_g (Q := fun s' => s'.mem = s₃.mem ∧ s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧
    (∀ r, r ≠ .ecx → s'.gpr r = s₃.gpr r) ∧
    s'.gpr .ecx = s₃.gpr .ecx - 1 ∧ s'.zf = some (s₃.gpr .ecx - 1 == 0)) rfl ?_) fun s' hh => ?_
  · exact Wp.wp_subi fun s₄ u₄ _ z => WP.block_nil ⟨u₄.mem, u₄.rd, u₄.wr, u₄.other, u₄.gpr, z⟩
  · obtain ⟨⟨m, rd, wr, g, cx, z⟩, x⟩ := hh
    have ec : s₃.gpr .ecx - 1 = BitVec.ofNat 32 (R - (j + 1)) := by
      rw [h₃.ecx, Wp.ofNat_pred (by omega_using [hj])]; congr 1
    refine ⟨h₃.gpr m rd wr x (g _ (by decide)) (g _ (by decide)) ((g _ (by decide)).trans h₃.esi)
      ((g _ (by decide)).trans h₃.ebx) (cx.trans ec), ?_⟩
    rw [z, ec, Wp.ofNat_beq_zero (by omega_using [hR])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hj]))

/-- The slots written. -/
theorem prep_ok (hfit : B.toNat + N ≤ 2 ^ 32) (hN : dec.saved + 16 ≤ N) (hscr : reg32 B N ∈ s₀.wr)
    (hs : Sched N B S R w s₀) {s : State} (h : TabSt dec all B s₀ all.length s) (h6 : s.xmm .xmm6 = inv)
    (h7 : s.xmm .xmm7 = mask) :
    WP isa dec.prep s fun s' => TabSt dec all B s₀ all.length s' ∧
      CoreIn dec all N B R (slotKey R (keyAt S s₀)) s' := by
  have hR := hs.le
  refine WP.seq (WP.mono (prepHead_ok hfit hN hscr hs h h6 h7) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ R
    (S + BitVec.ofNat 32 (16 * (R - (R - 1)))) (R - 1) 0) ?_ fun s₂ h₂ => ?_)
  · refine WP.loop (M := isa) (fun n s' => ∃ j, n = R - j ∧ 1 ≤ j ∧ j < R ∧
      SlotSt dec all B (slotKey R (keyAt S s₀)) s₀ j (S + BitVec.ofNat 32 (16 * (R - (j - 1)))) (j - 1) (R - j) s')
      (fun n s' ⟨j, hn, h1, hj, i⟩ => ?_) (R - 1) s₁ ⟨1, rfl, Nat.le_refl _, by omega_using [hR], h₁⟩
    refine WP.mono (prepBody_ok hfit hN hscr hs h1 hj i) fun s'' ⟨i', z⟩ => ?_
    by_cases e : R = j + 1
    · refine .inl ⟨by simp [eval, z, e], ?_⟩
      have i'' := i'
      rw [← e, Nat.sub_self, show j = R - 1 by omega_using [e]] at i''
      exact i''
    · exact .inr ⟨by simp [eval, z, e], R - (j + 1), by omega_using [hn, hj, e], j + 1, rfl, by omega_using [],
        by omega_using [hj, e], i'⟩
  · refine prepStep_ok (by omega_using [hR]) (Nat.le_refl R) h₂ fun s₃ h₃ => ?_
    refine WP.mono (copyKey_ok hfit hN hscr hs (Nat.le_refl R) (.inr rfl) h₃) fun s₄ h₄ =>
      ⟨h₄.tab, h₄.coreIn hfit hN hscr hs⟩

end Dec

/-! ## A direction's functions -/

/-- A direction computes `F R w` of a block, for the rounds `R` and the key
schedule `w`: from any entry, its setup and `prep` leave slots with which
its rounds do. -/
structure CryptOk (d : Dir) (all : List (BitVec 128))
    (F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop where
  setup : SetupOk d all
  prep : ∀ {N : Nat} {B S : BitVec 32} {R : Nat} {w : List Byte} {s₀ : State}, B.toNat + N ≤ 2 ^ 32 →
    d.saved + 16 ≤ N → reg32 B N ∈ s₀.wr → Sched N B S R w s₀ → ∃ sk : Nat → BitVec 128,
      (∀ {s : State}, TabSt d all B s₀ all.length s → s.xmm .xmm6 = inv → s.xmm .xmm7 = mask →
        WP isa d.prep s fun s' => TabSt d all B s₀ all.length s' ∧ CoreIn d all N B R sk s') ∧
      ∀ {s : State}, CoreIn d all N B R sk s → WP isa d.core s fun s' => Kept s s' ∧
        st (s'.xmm .xmm0) = F R w (st (s.xmm .xmm0))

theorem Enc.cryptOk : CryptOk enc Enc.all cipher where
  setup := Enc.setupOk
  prep := fun {N B S R w s₀} hfit hN hscr hs => ⟨Enc.slotKey R (keyAt S s₀), fun h h6 h7 =>
    Enc.prep_ok hfit hN hscr hs h h6 h7, fun h => WP.mono (core_ok Enc.dirOk h) fun s' ⟨k, e⟩ => ⟨k, by
      rw [e]; exact Enc.cipher_ok (by have := hs.le; omega_using [this]) hs.key _⟩⟩

theorem Dec.cryptOk : CryptOk dec Dec.all invCipher where
  setup := Dec.setupOk
  prep := fun {N B S R w s₀} hfit hN hscr hs => ⟨Dec.slotKey R (keyAt S s₀), fun h h6 h7 =>
    Dec.prep_ok hfit hN hscr hs h h6 h7, fun h => WP.mono (core_ok Dec.dirOk h) fun s' ⟨k, e⟩ => ⟨k, by
      rw [e]; exact Dec.cipher_ok (by have := hs.le; omega_using [this]) hs.key _⟩⟩

section
variable {d : Dir} {all : List (BitVec 128)} {N : Nat} {B : BitVec 32} {R : Nat} {sk : Nat → BitVec 128} {s₀ : State}

/-- Where the rounds run, after writes elsewhere. -/
theorem CoreIn.of_frame {s s' : State} (h : CoreIn d all N B R sk s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (h6 : s'.xmm .xmm6 = s.xmm .xmm6) (h7 : s'.xmm .xmm7 = s.xmm .xmm7) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hl : d.slots = 16 * all.length)
    (hB : ∀ o, o + 16 ≤ d.slots + 240 → ∀ r ∈ rs, Region.Disjoint ⟨addr B o, 16⟩ r)
    (hA : ∀ r ∈ rs, Region.Disjoint ⟨addr (s.gpr .esp) 8, 4⟩ r) : CoreIn d all N B R sk s' where
  edi := hedi.trans h.edi
  fit := h.fit
  room := h.room
  scr := by rw [hwr]; exact h.scr
  tab := fun k hk => (hf.readW (Region.contains_self _ _) (hB _ (by omega_using [hk, hl])) (by decide)).trans (h.tab k hk)
  slot := fun j hj => (hf.readW (Region.contains_self _ _)
    (hB _ (by have := h.le; omega_using [hj, this])) (by decide)).trans (h.slot j hj)
  x6 := h6.trans h.x6
  x7 := h7.trans h.x7
  rounds := h.rounds
  argIn := by rw [hrd, hwr, hesp]; exact h.argIn
  arg := by rw [hesp]; exact (hf.readW (Region.contains_self _ _) hA (by decide)).trans h.arg

/-- The callee-saved registers restored. -/
theorem restore_ok {s : State} (hedi : s.gpr .edi = B) (hesp : s.gpr .esp = s₀.gpr .esp) (hfit : B.toNat + N ≤ 2 ^ 32)
    (hN : d.saved + 16 ≤ N) (hscr : reg32 B N ∈ s.wr) (hs : Spill.Saved s.mem (addr B) s₀.gpr d.savedRegs) :
    WP isa (.block d.restore) s fun s' => s'.mem = s.mem ∧ ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  rw [show d.restore = Spill.restoreCode .edi
    ([(.ebx, d.saved), (.esi, d.saved + 4), (.ebp, d.saved + 8)] ++ [(.edi, d.saved + 12)]) ++ [] from rfl]
  refine Spill.restoreBase_ok _ (fun p hp => ?_) (fun p hp => ?_) (by rw [hedi]; exact hs) fun s' u =>
    WP.block_nil ⟨u.mem, fun r hr => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact Reg.noConfusion
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hedi]
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact in_rd (in_reg hscr hfit (by omega_using [hN]) (by decide))
  · by_cases hr' : r = .esp
    · subst hr'
      exact (u.other _ (by simp)).trans hesp
    · refine u.regs r ?_
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false]
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp_all

end

end VG.Proof.Aes.X86.Vperm
