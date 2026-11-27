module

meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
meta import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Impl.Scrypt.AArch64.Resident
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Scrypt.Contract
import all Init.Data.Nat.Power2.Basic
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Impl.Scrypt.AArch64.Resident
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Impl.MdStream.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.MdStream.Spec

/-! ### `Scrypt.AArch64.Resident.Pair`, which this module and modules that import it used -/

section

/-! ### `Scrypt.AArch64.BlockMixVerified`, which this module and modules that import it used -/

section

/-! ### `Scrypt.AArch64.Common`, which this module and modules that import it used -/

section

/-!
# scrypt on AArch64: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are the weakest-precondition rules for the
AArch64 forms, and the 64-byte exclusive-or.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_blockmix(b = x0, r = x1, y = x2, ry = x3,
scratch = x4)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its frame (saving `x30`) is the 16 bytes below the stack pointer. -/
def blockMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let y : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .x3 = s.gpr .x1 ∧ 0 < r
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_romix(b = x0, r = x1, v = x2, vlen = x3,
scratch = x4, slen = x5)`: if `r > 0`, `vlen = N r` for a power of two `N`,
and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. It
has no frame (it saves `x30` in `scratch`); its calls of `vg_scrypt_blockmix`
use the 16 bytes below the stack pointer. The indices `j` of step 3 are
public. -/
def roMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let v : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x3).toNat % r = 0 ∧ ((s.gpr .x3).toNat / r).isPowerOfTwo ∧
    (s.gpr .x5).toNat = r + 2
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x0) (128 * r) =
      roMix r ((s.gpr .x3).toNat / r) (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .x1).toNat ((s₁.gpr .x3).toNat / (s₁.gpr .x1).toNat)
        (bytesAt s₁.mem (s₁.gpr .x0) (128 * (s₁.gpr .x1).toNat)) =
      roMixIndices (s₂.gpr .x1).toNat ((s₂.gpr .x3).toNat / (s₂.gpr .x1).toNat)
        (bytesAt s₂.mem (s₂.gpr .x0) (128 * (s₂.gpr .x1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_ldr wp_str)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n <<< sh))
    (by simp [exec, h, State.read]) (k _ (Upd.write64 _ _ _))

end

end VG.Proof.Scrypt.AArch64.BlockMix

end

end

/-! ### `Scrypt.AArch64.Salsa`, which this module and modules that import it used -/

section

/-!
# The Salsa20/8 Core on AArch64: the rounds
-/

@[expose] public section

namespace VG.Proof.Scrypt.AArch64

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_x1 {k : Nat} (hk : k < 16) : wreg k ≠ .x1 := by
  have key : ∀ k, k < 16 → wreg k ≠ .x1 := by decide
  exact key k hk

/-- The registers that hold words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

/-! ## One line, on registers -/

/-- `a ^= R(b + c)` through `w1`, rotating right by `sh`. -/
theorem line_regs {a b c : Reg} (ha : a ≠ .x1) {sh : Nat} (hsh : sh < 32) (s : State) (va vb vc : Word)
    (hva : s.gpr a = va.setWidth 64) (hvb : s.gpr b = vb.setWidth 64)
    (hvc : s.gpr c = vc.setWidth 64) :
    WP isa (.block [.add .w .x1 b c, .ror .w .x1 .x1 sh, .logic .eor .w a a .x1]) s fun s' =>
      s'.gpr a = (va ^^^ (vb + vc).rotateRight sh).setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_logic, exec_ror_w hsh, isa, State.read, State.write, Size.bits, hva, hvb, hvc, ha,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h1 h2 => ?_, trivial⟩
  simp only [h1, h2, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop :=
  ∀ k (hk : k < 16), s.gpr (wreg k) = v[k].setWidth 64

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  have ne : ∀ {a b}, a < 16 → b < 16 → a ≠ b → wreg a ≠ wreg b := fun ha hb hab e =>
    hab (wreg_inj ha hb e)
  refine WP.mono (line_regs (wreg_ne_x1 hi) (show 32 - n < 32 by omega_using [h1]) s _ _ _ (h.holds i hi) (h.holds j hj)
    (h.holds k hk)) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw hx => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, rotateLeft_eq _ (by omega_using [h1]) (by omega_using [h2])]
    · simp only [e, ite_false]
      rw [hr _ (ne hm' hi (Ne.symm e)) (wreg_ne_x1 hm')]
      exact h.holds m hm'
  · rw [hr r (fun e => hw ⟨i, hi, e⟩) hx]
    exact h.keep r hw hx

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.Scrypt.AArch64

/-!
# The Salsa20/8 Core on AArch64: the whole function
-/

namespace VG.Proof.Scrypt.AArch64

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

theorem not_words_preserved {r : Reg} (hr : r ∈ preserved) : ¬ Words r ∧ r ≠ .x1 := by
  have key : ∀ r ∈ preserved, ∀ k, k < 16 → wreg k ≠ r := by decide
  refine ⟨fun ⟨k, hk, h⟩ => key r hr k hk h.symm, ?_⟩
  rintro rfl; simp [preserved] at hr

end VG.Proof.Scrypt.AArch64

end

end

/-!
# scryptBlockMix on AArch64: the loop's layout and invariants

The function's body runs inside a frame saving `x30`; the state `s₀` here is
the one the body starts in, and the frame is handled in
this file.
-/

@[expose] public section

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_subImm sub_ofNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev rr : Nat := (s₀.gpr .x1).toNat
abbrev yP : Addr := s₀.gpr .x2
abbrev sc : Addr := s₀.gpr .x4
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- The caller's `x19`–`x24` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sc s₀) s₀.gpr bmSaved m

end

/-- The callee-saved registers the code never writes (`x30` aside). -/
def others : List Reg := [.x25, .x26, .x27, .x28]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  x3 : s₀.gpr .x3 = s₀.gpr .x1
  pos : 0 < rr s₀

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
  simp only [Region.Contains]
  have := (sc s₀ - yP s₀).isLt
  omega_arith

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega_arith)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bB s₀ k
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  x24 : s.gpr .x24 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_arith)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega_arith))

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by revert p; decide
  have hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega_arith) (by omega_arith)
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_arith : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_arith, ← blk_B s₀ (by omega_arith), yAt_eq]
  have hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_arith)]
    exact b_frame hp F₂ (by omega_arith)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_arith) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_arith
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₁]
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₂]

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [mov .x24 .x21, .addImm .x .x19 .x19 64, .addImm .x .x20 .x20 64,
      .addImm .x .x21 .x21 64, .subImm .x .x23 .x23 1]) s (Inv s₀ (k + 1)) := by
  have lt := r_lt hp
  refine wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => wp_addImm (by decide) fun s₈ u₈ =>
    wp_addImm (by decide) fun s₉ u₉ => wp_subImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₁₀.gpr r = s.gpr r :=
    fun r h19 h20 h21 h23 h24 => by
      rw [u₁₀.other _ h23, u₉.other _ h21, u₈.other _ h20, u₇.other _ h19, u₆.other _ h24]
  refine ⟨(by omega_arith), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.x19, add_ofNat]
    congr 2; omega_arith
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.x20, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x21, add_ofNat]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x23, sub_ofNat (by omega_arith)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.x21]
    rfl
  · intro r hr
    have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_arith)).2]
    rfl

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the whole function

The prologue saves our caller's `x19`–`x24` in `scratch` and sets up the
loop's registers; the loop runs the `r` pairs; the epilogue restores the
registers. Around all of it, a frame saves `x30`, which the calls replace.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero readW_writeW_save write_frame_bytes)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .x4 bmSaved ++
    ([mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .x4 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]) s₁ (Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    wp_lsl (by decide) fun e ue => wp_add fun f uf => wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subImm (by decide) fun i ui => WP.block_nil ?_
  have x1 : d.gpr .x1 = s₀.gpr .x1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e9 : e.gpr .x9 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, x1, shl_eq (by simp; omega_arith), Nat.mul_comm]
  have g9 : g'.gpr .x9 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), x1, shl_eq (by simp; omega_arith),
      Nat.mul_comm]
  have hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .x9 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
      i.gpr r = s₀.gpr r := fun r h9 h19 h20 h21 h22 h23 h24 => by
    rw [ui.other _ h24, uh.other _ h24, ug.other _ h9, uf.other _ h21, ue.other _ h9,
      ud.other _ h22, uc.other _ h20, ub.other _ h19, ua.other _ h23, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega_arith)]
    rfl
  · intro r hr
    have : r ≠ .x9 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h9, h19, h20, h21, h22, h23, h24⟩ := this
    exact k r h9 h19 h20 h21 h22 h23 h24
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_arith), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_arith]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_arith))

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ≠ .x30 → r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) :=
  WP.mono (Spill.restore_wp (b := .x22) h.x22 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr h30 =>
      h'.gpr_of ((preserved_cases r hr h30).imp id (h.keep r))⟩

/-! ## The body of the frame -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_arith, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

/-! ## The whole function -/

/-- The frame's 16 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The state the body starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the public arguments

Only the pointers and `r` are public: the registers that hold them agree
in two runs with the same public data (`agree₀`).
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Scrypt.AArch64.BlockMix

end

end

/-! ### `Scrypt.AArch64.Resident.Load`, which only this module used -/

section

/-! ### `Scrypt.AArch64.Resident.Words`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_ne_x1 wreg_inj)
open VG.Impl.Scrypt.AArch64 (wreg)

theorem narrow64 (x : Word) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

def addr (p : Addr) (k : Nat) : Addr := p + BitVec.ofNat 64 (4*k)
def words (m : Mem) (p : Addr) : Vector Word 16 := Vector.ofFn fun k => m.readW (addr p k.val) 32

theorem words_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    (words m p)[k] = m.readW (addr p k) 32 := by
  simp only [words, Vector.getElem_ofFn]

theorem pin_ne {r : Reg} (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
    ¬ Words r ∧ r ≠ .x1 := by
  have h : ∀ k, k < 16 →
      wreg k ≠ .x19 ∧ wreg k ≠ .x20 ∧ wreg k ≠ .x21 ∧
      wreg k ≠ .x22 ∧ wreg k ≠ .x23 ∧ wreg k ≠ .x24 := by decide
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first | decide | (rintro ⟨k,hk,e⟩; obtain ⟨a,b,c,d,e',f⟩ := h k hk; first | exact a e.symm | exact b e.symm | exact c e.symm | exact d e.symm | exact e' e.symm | exact f e.symm)

structure Meta (s₀ : State) (out : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, ¬ Words r → r ≠ .x1 → s.gpr r = s₀.gpr r
  frame : Frame [⟨out,64⟩] s₀.mem s.mem

def mixed (s₀ : State) (src : Addr) (x : Vector Word 16) : Vector Word 16 :=
  Vector.zipWith (· ^^^ ·) x (words s₀.mem src)

structure XI (s₀ : State) (src out : Addr) (x : Vector Word 16) (i : Nat) (s : State)
    : Prop extends Meta s₀ out s where
  holds : ∀ j (hj : j < 16), s.gpr (wreg j) =
    (if j < i then (mixed s₀ src x)[j] else x[j]).setWidth 64
  written : ∀ j (hj : j < 16), j < i → s.mem.readW (addr out j) 32 = (mixed s₀ src x)[j]

theorem mixed_get (s₀ : State) (src : Addr) (x : Vector Word 16) {j : Nat} (hj : j < 16) :
    (mixed s₀ src x)[j] = x[j] ^^^ s₀.mem.readW (addr src j) 32 := by
  simp only [mixed, Vector.getElem_zipWith, words_get]

theorem part (p : Addr) {j : Nat} (hj : j < 16) : (Region.mk p 64).Contains (addr p j) 4 :=
  VG.Proof.Scrypt.AArch64.contains_off (by omega_using [hj]) (by omega_using [hj])

theorem xor_step {s₀ s : State} {src out : Addr} {x : Vector Word 16} {i : Nat}
    {d : Reg} (hi : i < 16) (hd : d = .x20 ∨ d = .x21)
    (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (h : XI s₀ src out x i s) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Resident.xorWord d i)) s (XI s₀ src out x (i+1)) := by
  have ns := pin_ne (r := .x19) (by simp)
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have h19 : s.gpr .x19 = src := (h.keep _ ns.1 ns.2).trans hsrc
  have hD : s.gpr d = out := (h.keep _ nd.1 nd.2).trans hdst
  have n1 := wreg_ne_x1 hi
  have dn : d ≠ wreg i := fun e => nd.1 ⟨i,hi,e⟩
  have hread : s.mem.readW (addr src i) 32 = s₀.mem.readW (addr src i) 32 :=
    h.frame.readW (part src hi) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact sep) (by decide)
  have hread' : s.mem.readW (src + BitVec.ofNat 64 (4*i)) 32 =
      s₀.mem.readW (src + BitVec.ofNat 64 (4*i)) 32 := hread
  have hw : s.gpr (wreg i) = x[i].setWidth 64 := by
    rw [h.holds i hi, VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i)]
  have ir : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.rd,h.wr,h19]; exact hin i hi
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.xorWord, runBlock_cons, runStep_some,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega_using [hi]) ir, exec_logic, isa,
    State.read, State.write, Size.bits, n1, hw, h19,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, ↓reduceIte, Nat.reduceLeDiff, hread']
  rw [exec_str_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega_using [hi])
    (by simpa [State.write, dn, nd.2, hD, h.wr, addr] using hout i hi)]
  simp only [runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left',↓reduceIte,narrow64]
  refine ⟨⟨h.rd,h.wr,h.sp,?_,?_⟩,?_,?_⟩
  · intro r hr hn
    have n : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [n,hn,ite_false]
    exact h.keep r hr hn
  · simpa only [hD, dn, nd.2, ite_false, addr, narrow64, hread'] using
      h.frame.writeW (List.mem_singleton_self _) (x[i] ^^^ s₀.mem.readW (addr src i) 32) (part out hi)
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [ite_true,BitVec.setWidth_xor,mixed_get s₀ src x hi,
        VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i), addr]
    · have n : wreg j ≠ wreg i := fun ee => e (wreg_inj hj hi ee)
      simp only [n,wreg_ne_x1 hj,ite_false]
      rw [h.holds j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt, VG.Proof.Scrypt.AArch64.ite_pos' (by omega_using [hjlt])]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt, VG.Proof.Scrypt.AArch64.ite_neg' (by omega_using [e, hjlt])]
  · intro j hj hji
    by_cases e : j = i
    · subst j
      simp only [dn,nd.2,ite_false,hD,Mem.readW_writeW_self32,addr,mixed_get s₀ src x hi]
    · simp only [dn,nd.2,ite_false,hD,addr]
      rw [VG.Proof.Scrypt.AArch64.readW_writeW_word _ _ _ hj hi e]
      exact h.written j hj (by omega_using [hji, e])
theorem xor_ok {s₀ : State} {src out : Addr} {x : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (hh : Holds x s₀) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Scrypt.AArch64.Resident.xorWord d))) s₀
      fun s => Meta s₀ out s ∧ Holds (mixed s₀ src x) s ∧
        ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 = (mixed s₀ src x)[j] := by
  have h0 : XI s₀ src out x 0 s₀ :=
    ⟨⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩,
      fun j hj => by simpa using hh j hj,fun _ _ h => by omega⟩
  refine WP.mono (wp_range_flatMap (M := isa) (XI s₀ src out x)
    (fun k s hk h => xor_step hk hd hsrc hdst sep hin hout h) 16 (by omega_using []) s₀ h0) ?_
  intro s h
  exact ⟨h.toMeta,fun j hj => by simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj] using h.holds j hj,
    fun j hj => h.written j hj hj⟩

/-- Feed-forward retains every completed output word in its scalar register. -/
structure FI (s₀ : State) (out : Addr) (R : Vector Word 16) (i : Nat) (s : State)
    : Prop extends Meta s₀ out s where
  holds : ∀ j (hj : j < 16), s.gpr (wreg j) =
    (if j < i then R[j] + (words s₀.mem out)[j] else R[j]).setWidth 64
  written : ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 =
    if j < i then R[j] + (words s₀.mem out)[j] else (words s₀.mem out)[j]

theorem finish_step {s₀ s : State} {out : Addr} {R : Vector Word 16} {i : Nat}
    {d : Reg} (hi : i < 16) (hd : d = .x20 ∨ d = .x21)
    (hdst : s₀.gpr d = out)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4)
    (h : FI s₀ out R i s) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Resident.finishWord d i)) s (FI s₀ out R (i+1)) := by
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have hD : s.gpr d = out := (h.keep _ nd.1 nd.2).trans hdst
  have n1 := wreg_ne_x1 hi
  have dn : d ≠ wreg i := fun e => nd.1 ⟨i,hi,e⟩
  have hread : s.mem.readW (out + BitVec.ofNat 64 (4*i)) 32 = (words s₀.mem out)[i] := by
    exact (h.written i hi).trans (VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i))
  have hw : s.gpr (wreg i) = R[i].setWidth 64 := by
    rw [h.holds i hi, VG.Proof.Scrypt.AArch64.ite_neg' (Nat.lt_irrefl i)]
  have iw : InRegions s.wr (s.gpr d + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.wr,hD]; exact hout i hi
  have ir : InRegions (s.rd ++ s.wr) (s.gpr d + BitVec.ofNat 64 (4*i)) 4 := by
    rcases iw with ⟨r,hr,hc⟩
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.finishWord,runBlock_cons,runStep_some,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega_using [hi]) ir,exec_add,isa,
    State.read,State.write,Size.bits,n1,hw,hD,
    BitVec.setWidth_setWidth_of_le,BitVec.setWidth_eq,↓reduceIte,Nat.reduceLeDiff,hread]
  rw [exec_str_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega_using [hi])
    (by simpa [State.write,dn,nd.2,hD] using iw)]
  simp only [runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left',↓reduceIte,narrow64]
  refine ⟨⟨h.rd,h.wr,h.sp,?_,?_⟩,?_,?_⟩
  · intro r hr hn
    have n : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [n,hn,ite_false]
    exact h.keep r hr hn
  · simpa only [hD,dn,nd.2,ite_false,addr,narrow64] using
      h.frame.writeW (List.mem_singleton_self _) (R[i] + (words s₀.mem out)[i]) (part out hi)
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [ite_true,VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i)]
    · have n : wreg j ≠ wreg i := fun ee => e (wreg_inj hj hi ee)
      simp only [n,wreg_ne_x1 hj,ite_false]
      rw [h.holds j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt,VG.Proof.Scrypt.AArch64.ite_pos' (by omega_using [hjlt])]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt,VG.Proof.Scrypt.AArch64.ite_neg' (by omega_using [e, hjlt])]
  · intro j hj
    by_cases e : j = i
    · subst j
      simp only [dn,nd.2,ite_false,hD,addr,Mem.readW_writeW_self32,
        VG.Proof.Scrypt.AArch64.ite_pos' (Nat.lt_succ_self i)]
    · simp only [dn,nd.2,ite_false,hD,addr]
      rw [VG.Proof.Scrypt.AArch64.readW_writeW_word _ _ _ hj hi e]
      change s.mem.readW (addr out j) 32 = _
      rw [h.written j hj]
      by_cases hjlt : j < i
      · rw [VG.Proof.Scrypt.AArch64.ite_pos' hjlt,VG.Proof.Scrypt.AArch64.ite_pos' (by omega_using [hjlt])]
      · rw [VG.Proof.Scrypt.AArch64.ite_neg' hjlt,VG.Proof.Scrypt.AArch64.ite_neg' (by omega_using [e, hjlt])]

theorem finish_ok {s₀ : State} {out : Addr} {R : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hdst : s₀.gpr d = out)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds R s₀) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Scrypt.AArch64.Resident.finishWord d))) s₀
      fun s => Meta s₀ out s ∧ Holds (Vector.zipWith (· + ·) R (words s₀.mem out)) s ∧
        ∀ j (hj : j < 16), s.mem.readW (addr out j) 32 = R[j] + (words s₀.mem out)[j] := by
  have h0 : FI s₀ out R 0 s₀ :=
    ⟨⟨rfl,rfl,rfl,fun _ _ _ => rfl,Frame.refl _ _⟩,
      fun j hj => by simpa using hh j hj,fun j hj => by simp [words_get]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ out R)
    (fun k s hk h => finish_step hk hd hdst hout h) 16 (by omega_using []) s₀ h0) ?_
  intro s h
  refine ⟨h.toMeta,fun j hj => ?_,fun j hj => ?_⟩
  · simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj,Vector.getElem_zipWith] using h.holds j hj
  · simpa only [VG.Proof.Scrypt.AArch64.ite_pos' hj] using h.written j hj

theorem step_words {s₀ : State} {src out : Addr} {x : Vector Word 16} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds x s₀) :
    WP isa (VG.Impl.Scrypt.AArch64.Resident.step d) s₀ fun s =>
      Meta s₀ out s ∧ Holds (core (mixed s₀ src x)) s ∧
      words s.mem out = core (mixed s₀ src x) ∧ bytesAt s.mem out 64 = serialize (core (mixed s₀ src x)) := by
  refine WP.seq (WP.mono (xor_ok hd hsrc hdst sep hin hout hh) fun s₁ ⟨m₁,h₁,w₁⟩ => ?_)
  obtain ⟨t,s₂,e₂,h₂⟩ := VG.Proof.Scrypt.AArch64.rounds_ok h₁ 4
  have wo : words s₂.mem out = mixed s₀ src x := by
    apply Vector.ext
    intro j hj
    rw [words_get _ _ hj,h₂.mem,w₁ j hj]
  have nd := pin_ne (r := d) (by rcases hd with rfl | rfl <;> simp)
  have hd₂ : s₂.gpr d = out := (h₂.keep d nd.1 nd.2).trans ((m₁.keep d nd.1 nd.2).trans hdst)
  refine WP.seq ⟨t,s₂,e₂,?_⟩
  refine WP.mono (finish_ok hd hd₂ (fun j hj => by rw [h₂.wr,m₁.wr]; exact hout j hj) h₂.holds) ?_
  intro s₃ ⟨m₃,h₃,w₃⟩
  refine ⟨⟨m₃.rd.trans (h₂.rd.trans m₁.rd),m₃.wr.trans (h₂.wr.trans m₁.wr),
    m₃.sp.trans ((Exec.sp e₂).trans m₁.sp),fun r hr hn =>
      (m₃.keep r hr hn).trans ((h₂.keep r hr hn).trans (m₁.keep r hr hn)),?_⟩,?_,?_,?_⟩
  · exact m₁.frame.trans (by rw [← h₂.mem]; exact m₃.frame)
  · simpa only [wo,core] using h₃
  · apply Vector.ext
    intro j hj
    simpa only [words_get _ _ hj,core,Vector.getElem_zipWith,wo] using w₃ j hj
  · apply bytesAt_eq_serialize
    intro j hj
    simpa only [core,Vector.getElem_zipWith,wo,addr] using w₃ j hj

theorem wordLE_xor {a b : List Byte} {j : Nat} (ha : 4*j+4 ≤ a.length) (hb : 4*j+4 ≤ b.length) :
    wordLE (VG.Spec.Pbkdf2.xorBytes a b) j = wordLE a j ^^^ wordLE b j := by
  have hd (i : Nat) (hi : i < 4) :
      (VG.Spec.Pbkdf2.xorBytes a b).getD (4*j+i) 0 = a.getD (4*j+i) 0 ^^^ b.getD (4*j+i) 0 := by
    simp only [VG.Spec.Pbkdf2.xorBytes,List.getD_eq_getElem?_getD,List.getElem?_zipWith,
      List.getElem?_eq_getElem (by omega_using [ha, hi] : 4*j+i < a.length),
      List.getElem?_eq_getElem (by omega_using [hb, hi] : 4*j+i < b.length),Option.getD_some]
  have hd0 := hd 0 (by omega_using [])
  simp only [Nat.add_zero] at hd0
  simp only [wordLE,hd 3 (by omega_using []),hd 2 (by omega_using []),hd 1 (by omega_using []),hd0]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_xor]
  (repeat' split) <;> rfl

theorem step_ok {s₀ : State} {src out xp : Addr} {d : Reg}
    (hd : d = .x20 ∨ d = .x21) (hsrc : s₀.gpr .x19 = src) (hdst : s₀.gpr d = out)
    (sep : (Region.mk src 64).Disjoint ⟨out,64⟩)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr src j) 4)
    (hout : ∀ j < 16, InRegions s₀.wr (addr out j) 4) (hh : Holds (words s₀.mem xp) s₀) :
    WP isa (VG.Impl.Scrypt.AArch64.Resident.step d) s₀ fun s =>
      Meta s₀ out s ∧ Holds (words s.mem out) s ∧
      bytesAt s.mem out 64 = salsa (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem xp 64) (bytesAt s₀.mem src 64)) := by
  have mi : (Vector.ofFn fun j : Fin 16 => wordLE
      (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem xp 64) (bytesAt s₀.mem src 64)) j.val) =
      mixed s₀ src (words s₀.mem xp) := by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn,mixed_get s₀ src _ hj,words_get _ _ hj]
    rw [wordLE_xor (by simp [bytesAt]; omega_using [hj]) (by simp [bytesAt]; omega_using [hj]),
      wordLE_bytesAt _ _ (by omega_using [hj]),wordLE_bytesAt _ _ (by omega_using [hj])]
    rfl
  refine WP.mono (step_words hd hsrc hdst sep hin hout hh) fun s ⟨hm,hh,we,hb⟩ => ?_
  exact ⟨hm,by rw [we]; exact hh,by simpa only [salsa,mi] using hb⟩

end VG.Proof.Scrypt.AArch64.Resident

end

end


@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_inj)
open VG.Impl.Scrypt.AArch64 (wreg)

structure LI (s₀ : State) (i : Nat) (s : State) : Prop where
  holds : ∀ j (hj : j < 16), j < i → s.gpr (wreg j) = (words s₀.mem (s₀.gpr .x24))[j].setWidth 64
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ s : State} {i : Nat} (hi : i < 16)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .x24) j) 4)
    (h : LI s₀ i s) :
    WP isa (.block [VG.Impl.Scrypt.AArch64.Resident.loadWord i]) s (LI s₀ (i+1)) := by
  have n24 := (pin_ne (r := .x24) (by simp)).1
  have hx : s.gpr .x24 = s₀.gpr .x24 := h.keep _ n24
  have ir : InRegions (s.rd ++ s.wr) (s.gpr .x24 + BitVec.ofNat 64 (4*i)) 4 := by
    rw [h.rd,h.wr,hx]; exact hin i hi
  apply WP.of_runBlock
  simp only [VG.Impl.Scrypt.AArch64.Resident.loadWord,runBlock_cons,runStep_some,runBlock_nil,
    exec_ldr_w (show 4*i % 4 = 0 ∧ 4*i < 16384 by omega_using [hi]) ir,isa,Option.some.injEq,exists_eq_left']
  refine ⟨?_,h.mem,h.rd,h.wr,h.sp,?_⟩
  · intro j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · have ne : wreg j ≠ wreg i := fun e => (by omega_using [hji] : j ≠ i) (wreg_inj hj hi e)
      simp only [State.write,ne,ite_false]
      exact h.holds j hj hji
    · simp only [State.write,ite_true,Size.bits,h.mem,hx,words_get _ _ hi,addr]
  · intro r hr
    have ne : r ≠ wreg i := fun e => hr ⟨i,hi,e⟩
    simp only [State.write,ne,ite_false]
    exact h.keep r hr

theorem load_ok (s₀ : State)
    (hin : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .x24) j) 4) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.load) s₀ (LI s₀ 16) := by
  have eq : VG.Impl.Scrypt.AArch64.Resident.load =
      (List.range 16).flatMap (fun i => [VG.Impl.Scrypt.AArch64.Resident.loadWord i]) := by
    decide +kernel
  rw [eq]
  exact wp_range_flatMap (M := isa) (LI s₀) (fun i s hi h => load_step hi hin h)
    16 (by omega_using []) s₀ ⟨fun _ _ h => by omega,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
end VG.Proof.Scrypt.AArch64.Resident

end

end


@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64 (Holds Words wreg_ne_x1)
open VG.Impl.Scrypt.AArch64 (wreg)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem)
open VG.Proof.MdStream.AArch64 (wp_addImm wp_mov wp_subImm)

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends BlockMix.Inv s₀ k s where
  holds : Holds (words s.mem (BlockMix.xP s₀ k)) s

theorem other_ne {r : Reg} (hr : r ∈ BlockMix.others) : ¬ Words r ∧ r ≠ .x1 := by
  exact VG.Proof.Scrypt.AArch64.not_words_preserved (by
    simp only [BlockMix.others,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

theorem Meta.pin {s₀ s : State} {out : Addr} (h : Meta s₀ out s) {r : Reg}
    (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
    s.gpr r = s₀.gpr r := h.keep r (pin_ne hr).1 (pin_ne hr).2

theorem load_inv {s₀ : State} (hp : BlockMix.Pre s₀) {s : State} (h : BlockMix.Inv s₀ 0 s) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.load) s (Inv s₀ 0) := by
  have hi : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr (s.gpr .x24) j) 4 := by
    intro j hj
    rw [h.rd,h.wr,h.x24,hp.rd,hp.wr]
    simp only [BlockMix.xP,addr]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by have := hp.pos; omega_using [hj, this]))
  refine WP.mono (load_ok s hi) fun s' u => ?_
  have eq (r : Reg) (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24) :
      s'.gpr r = s.gpr r := u.keep r (pin_ne hr).1
  refine ⟨⟨h.k_le,u.rd.trans h.rd,u.wr.trans h.wr,u.sp.trans h.sp,
    (eq _ (by simp)).trans h.x19,(eq _ (by simp)).trans h.x20,(eq _ (by simp)).trans h.x21,
    (eq _ (by simp)).trans h.x22,(eq _ (by simp)).trans h.x23,(eq _ (by simp)).trans h.x24,
    fun r hr => (u.keep r (other_ne hr).1).trans (h.keep r hr),?_,?_,?_,?_⟩,?_⟩
  · rw [u.mem]; exact h.frame
  · rw [u.mem]; exact h.saved
  · rw [u.mem]; exact h.done
  · rw [u.mem]; exact h.x
  · intro j hj
    simpa only [u.mem,h.x24] using u.holds j hj hj

theorem tail_holds {s : State} (hh : Holds (words s.mem (s.gpr .x21)) s) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.tail) s fun s' => s'.mem = s.mem ∧
      Holds (words s'.mem (s.gpr .x21)) s' := by
  refine wp_mov fun a ua => wp_addImm (by decide) fun b ub => wp_addImm (by decide) fun c uc =>
    wp_addImm (by decide) fun d ud => wp_subImm (by decide) fun e ue => WP.block_nil ?_
  have hm : e.mem = s.mem := by rw [ue.mem,ud.mem,uc.mem,ub.mem,ua.mem]
  refine ⟨hm,fun j hj => ?_⟩
  have hn : wreg j ≠ .x19 ∧ wreg j ≠ .x20 ∧ wreg j ≠ .x21 ∧ wreg j ≠ .x23 ∧ wreg j ≠ .x24 := by
    have h : ∀ j, j < 16 → wreg j ≠ .x19 ∧ wreg j ≠ .x20 ∧ wreg j ≠ .x21 ∧ wreg j ≠ .x23 ∧ wreg j ≠ .x24 := by decide
    exact h j hj
  rw [ue.other _ hn.2.2.2.1,ud.other _ hn.2.2.1,uc.other _ hn.2.1,ub.other _ hn.1,ua.other _ hn.2.2.2.2,hm]
  exact hh j hj

theorem body_ok {s₀ : State} (hp : BlockMix.Pre s₀) {k : Nat} (hk : k < BlockMix.rr s₀)
    {s : State} (h : Inv s₀ k s) : WP isa VG.Impl.Scrypt.AArch64.Resident.body s (Inv s₀ (k+1)) := by
  have oe : 64*k+64 ≤ 128*BlockMix.rr s₀ := by omega_using [hk]
  have oo : 64*(BlockMix.rr s₀+k)+64 ≤ 128*BlockMix.rr s₀ := by omega_using [hk]
  have ib : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr (BlockMix.bB s₀ k) j) 4 := by
    intro j hj
    rw [h.rd,h.wr,hp.rd,hp.wr]
    simp only [addr,BlockMix.bB]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by omega_using [hk, hj]))
  have ow : ∀ j < 16, InRegions s.wr (addr (BlockMix.yE s₀ k) j) 4 := by
    intro j hj
    rw [h.wr,hp.wr]
    simp only [addr,BlockMix.yE]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_y hp (by omega_using [hk, hj]))
  refine WP.seq (WP.mono (step_ok (by simp) h.x19 h.x20
    ((hp.b_y.sub_left (BlockMix.b_sub hp (by omega_using [hk]))).sub_right (BlockMix.y_sub hp oe)) ib ow h.holds)
    fun a ⟨ma,ha,ba⟩ => ?_)
  refine WP.seq (wp_addImm (by decide) fun b ub => WP.block_nil ?_)
  have b19 : b.gpr .x19 = BlockMix.bP s₀ + BitVec.ofNat 64 (64*(2*k+1)) := by
    rw [ub.gpr,ma.pin (by simp),h.x19,add_ofNat]
    congr 2; omega_using []
  have b21 : b.gpr .x21 = BlockMix.yO s₀ k := by rw [ub.other _ (by decide),ma.pin (by simp),h.x21]
  have hb : Holds (words b.mem (BlockMix.yE s₀ k)) b := by
    intro j hj
    have ne : wreg j ≠ .x19 := fun e => (pin_ne (r := .x19) (by simp)).1 ⟨j,hj,e.symm⟩
    rw [ub.other _ ne,ub.mem]
    exact ha j hj
  have ib' : ∀ j < 16, InRegions (b.rd ++ b.wr) (addr (BlockMix.bP s₀ + BitVec.ofNat 64 (64*(2*k+1))) j) 4 := by
    intro j hj
    rw [ub.rd,ub.wr,ma.rd,ma.wr,h.rd,h.wr,hp.rd,hp.wr]
    simp only [addr]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_b hp (by omega_using [hk, hj]))
  have ow' : ∀ j < 16, InRegions b.wr (addr (BlockMix.yO s₀ k) j) 4 := by
    intro j hj
    rw [ub.wr,ma.wr,h.wr,hp.wr]
    simp only [addr,BlockMix.yO]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (BlockMix.in_y hp (by omega_using [hk, hj]))
  refine WP.seq (WP.mono (step_ok (by simp) b19 b21
    ((hp.b_y.sub_left (BlockMix.b_sub hp (by omega_using [hk]))).sub_right (BlockMix.y_sub hp oo)) ib' ow' hb)
    fun c ⟨mc,hc,bc⟩ => ?_)
  have f1 : Frame [BlockMix.slot s₀ (64*k),⟨BlockMix.sc s₀,64⟩] s.mem a.mem := ma.frame.mono (by simp [BlockMix.slot])
  have f2 : Frame [BlockMix.slot s₀ (64*(BlockMix.rr s₀+k)),⟨BlockMix.sc s₀,64⟩] a.mem c.mem := by
    rw [← ub.mem]; exact mc.frame.mono (by simp [BlockMix.slot])
  rw [ub.mem] at bc
  obtain ⟨ff,ss,dd⟩ := BlockMix.mem_ok hp hk h.toInv f1 ba f2 bc
  have kee (r : Reg) (hr : r ≠ .x19) (hw : ¬ Words r) (hn : r ≠ .x1) : c.gpr r = s.gpr r := by
    rw [mc.keep r hw hn,ub.other r hr,ma.keep r hw hn]
  have mid : BlockMix.Mid s₀ k c := ⟨mc.rd.trans (ub.rd.trans (ma.rd.trans h.rd)),
    mc.wr.trans (ub.wr.trans (ma.wr.trans h.wr)),mc.sp.trans (ub.sp.trans (ma.sp.trans h.sp)),
    (mc.pin (by simp)).trans b19,by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x20],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x21],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x22],
    by rw [kee _ (by decide) (pin_ne (by simp)).1 (by decide),h.x23],
    fun r hr => (kee r (by simpa [BlockMix.others] using fun e => by subst r; simp [BlockMix.others] at hr)
      (other_ne hr).1 (other_ne hr).2).trans (h.keep r hr),ff,ss,dd⟩
  have ht : Holds (words c.mem (c.gpr .x21)) c := by rw [mid.x21]; exact hc
  exact WP.mono ((BlockMix.regs_ok hp hk mid).and (tail_holds ht)) fun s' ⟨hi,_,hh⟩ =>
    ⟨hi,by simpa only [BlockMix.xP,mid.x21] using hh⟩
end VG.Proof.Scrypt.AArch64.Resident

end

end

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64.BlockMix
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt bytesAt_congr)
open VG.Proof.MdStream.AArch64 (eval_nonzero ofNat_beq_zero write_frame_bytes)

theorem loop_ok {s₀ : State} (hp : BlockMix.Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.loop VG.Impl.Scrypt.AArch64.Resident.body (.nonzero .x .x23)) s (Inv s₀ (rr s₀)) := by
  have lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀-k ∧ k < rr s₀ ∧ Inv s₀ k s)
    ?_ (rr s₀) s ⟨0,rfl,hp.pos,h⟩
  rintro n s ⟨k,rfl,hk,hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (rr s₀-(k+1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero,hi'.x23,bne,ofNat_beq_zero (by omega_using [lt])]
    simp
  by_cases hl : rr s₀-(k+1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl],?_⟩
    rwa [show k+1 = rr s₀ by omega_using [hk, hl]] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl],rr s₀-(k+1),by omega_using [hk],k+1,rfl,by omega_using [hl],hi'⟩

theorem prologue_ok {s₀ : State} (hp : BlockMix.Pre s₀) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.prologue) s₀ (BlockMix.Inv s₀ 0) := by
  change WP isa (.block VG.Impl.Scrypt.AArch64.bmPrologue) s₀ _
  rw [prologue_eq]
  exact save_ok hp fun s₁ g hrd hwr hsp hm => setup_ok hp g hrd hwr hsp hm

theorem correctMain {s₀ : State} (hp : BlockMix.Pre s₀) :
    WP isa VG.Impl.Scrypt.AArch64.Resident.main s₀ fun s' =>
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (yP s₀) (128*rr s₀) = blockMix (rr s₀) (BlockMix.B s₀) := by
  refine WP.seq (WP.block_append (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_))
  refine WP.mono (load_inv hp h₁) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃.toInv) fun s' ⟨hm,hsp,hg⟩ => ⟨hg,hsp.trans h₃.sp,?_⟩
  rw [hm]
  exact BlockMix.post_of fun i hi => h₃.done i hi

theorem correct
    (hd : 16 * VG.Impl.Scrypt.AArch64.Resident.main.aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : BlockMix.Pre s₀) (hs : BlockMix.Stack s₀) :
    WP isa VG.Impl.Scrypt.AArch64.Resident.code s₀ fun s' =>
      GprAbi s₀ s' ∧ Proof.Scrypt.blockMixAArch64.post s₀ s' := by
  have hpi : BlockMix.Pre (BlockMix.inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.x3, hp.pos⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_)
    (WP.mono (correctMain hpi) fun s' ⟨hk, hsp, hpost⟩ mm u f => ?_) hd
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : BlockMix.B (BlockMix.inner s₀) = bytesAt s₀.mem (bP s₀) (128 * rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * rr s₀ := hi
          exact write_frame_bytes (R := BlockMix.bR s₀) hs.b (by have := r_lt hp; simp only; omega_arith)
            (by simp only; omega_arith)
      -- The output lies apart from the frame, whose bytes the pop loses.
      show bytesAt mm (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s₀.mem (bP s₀) (128 * rr s₀))
      rw [← e]
      exact (bytesAt_congr fun i hi => lost_byte (R := BlockMix.yR s₀) f hs.y.symm
        (show i < rr s₀ * 128 by omega_using [hi])).trans hpost

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixAArch64.post s s' := by
  obtain ⟨t,s',he,h⟩ := correct (by decide +kernel) (BlockMix.pre_of hs).1 (BlockMix.pre_of hs).2
  exact ⟨t,s',he,⟨h.1.1,h.1.2,Exec.preservedV he (by lit_decide)⟩,h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixAArch64.pre
    Proof.Scrypt.blockMixAArch64.pub Impl.Scrypt.AArch64.blockMix := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

end VG.Proof.Scrypt.AArch64.Resident
