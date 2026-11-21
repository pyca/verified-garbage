module

import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Impl.Blake2.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact

/-! ### `Blake2.RISCV64.Stream.Common`, which this module and modules that import it used -/

section

/-! ### `Blake2.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# BLAKE2 compression function on RISC-V: the contract

The contract the streaming functions use for their calls of the compression
function; the artifacts' contract is the shared one of
`Spec/Blake2/Contract.lean`, which implies it.
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.RISCV64 VG.Spec.Blake2

/-- RISC-V contract for `compress(state = a0, blocks = a1, n = a2, t = a3,
last = a4, scratch = a5)`: updates the state at `state` with the `n` blocks at
`blocks`, block `i` with the counter `t + bb · i` and the final block flag if
the low word of `last` is not zero. It reads the blocks and reads and writes
the state and 280 bytes of scratch space, which do not overlap each other.
The pointers, `n`, `t` and `last` are public. -/
def compressRISCV64 {w : Nat} (P : Params w) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 8 * (w / 8)⟩
    let blocks : Region := ⟨s.gpr .a1, blockBytes w * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 280⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' := stateAt w s'.mem (s.gpr .a0) =
    compressBlocks P (stateAt w s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
      (s.gpr .a3).toNat ((s.gpr .a4).setWidth 32 != 0)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ (s₁.gpr .a4).setWidth 32 = (s₂.gpr .a4).setWidth 32 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

end VG.Proof.Blake2

end

end

/-!
# Streaming BLAKE2 on RISC-V: common lemmas

The contracts the proofs of `init`, `update` and `finalize` are written
against, what they need of the compression function they call (`CalleeOk`),
the call (`compressWith_ok`), the loops copying bytes into the buffer and
zeroing it, and the saves and restores in the scratch space, as on PPC64LE
(`Proof/Blake2/PPC64LE/Stream/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.RISCV64 VG.Spec.Blake2

section
variable {w : Nat} (P : Params w)

/-- RISC-V contract for `init(state = a0, outlen = a1, key = a2, keylen =
a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, bufOff w + blockBytes w⟩
    let key : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧
    1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ P.maxBytes ∧ (s.gpr .a3).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .a1).toNat (s.gpr .a3).toNat) s'.mem
    (s.gpr .a0) (keyBlock w (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `update`'s postcondition: `state` and `len` in `st` and `n`. -/
def updatePost (s s' : State) : Prop :=
  ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .a0) d →
    s.gpr .a1 = BitVec.ofNat 64 d.length → d.length + (s.gpr .a3).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (s.gpr .a0) (d ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)

/-- RISC-V contract for `update_scratch(state = a0, count = a1, data = a2,
len = a3, scratch = a4)`, with `sc` bytes of scratch: the code uses 336 (the
compression function's 280 and our 48, from a pointer it rounds up by at
most 7); Argon2 passes 576 (`Proof/Argon2/RISCV64/HPrime/Absorb.lean`). -/
def updateRISCV64 (sc : Nat := 576) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let scratch : Region := ⟨s.gpr .a4, sc⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch
  post := updatePost P
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-- RISC-V contract for `update(state = a0, count = a1, data = a2, len =
a3)`, with its scratch space in a frame of 336 bytes below the stack
pointer. -/
def updateFramedRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 336, 336⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 336 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post := updatePost P
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `finalize`'s postcondition. -/
def finalizePost (s s' : State) : Prop :=
  ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .a0) d → d.length < 2 ^ 64 →
    s.gpr .a1 = BitVec.ofNat 64 d.length → bytesAt s'.mem (s.gpr .a2) (bufOff w) = finalHash P h0 d

/-- RISC-V contract for `finalize_scratch(state = a0, count = a1, out = a2,
scratch = a3)`, with `sc` bytes of scratch (as for `updateRISCV64`). -/
def finalizeRISCV64 (sc : Nat := 576) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .a2, bufOff w⟩
    let scratch : Region := ⟨s.gpr .a3, sc⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch
  post := finalizePost P
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- RISC-V contract for `finalize(state = a0, count = a1, out = a2)`, with
its scratch space in a frame of 336 bytes below the stack pointer. -/
def finalizeFramedRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .a2, bufOff w⟩
    let stack : Region := ⟨s.sp - 336, 336⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 336 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post := finalizePost P
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end

namespace RISCV64.Stream

open VG.Impl.Blake2.RISCV64.Stream (N B mov copyLoop zeroLoop compressWith saved save restore)
open VG.Impl.Blake2.RISCV64 (lbb compress)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_mv wp_addi wp_add wp_sub wp_lbu wp_sb wp_sd wp_ld wp_li
  eval_zero eval_nonzero)
open VG.RISCV64.Align (pad pad_lt align_eq align_al)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : Params w}

/-! ## Numbers -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem and_mask {n : Nat} (hn : n ≤ 16) (x : BitVec 64) :
    x &&& BitVec.ofNat 64 (2 ^ n - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ n) := by
  have hp : 2 ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hn
  have h1 : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 64 by omega_using [hp]), Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt x.toNat (Nat.two_pow_pos n)
  omega_using [hp]

/-- `x + (-1)`. -/
theorem add_neg_one (x : BitVec 64) : x + BitVec.ofInt 64 (-1) = x - BitVec.ofNat 64 1 := by
  rw [BitVec.sub_eq_add_neg]; rfl

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by simp

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega_using [h]

/-- The sizes, all small. -/
theorem Ok.len (h : Ok P) : bufOff w + blockBytes w ≤ 192 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N64 (h : Ok P) : bufOff w ≤ 64 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : Ok P) : lbb w < 64 ∧ 2 ^ lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : N w = bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> lbb w = BitVec.ofNat 64 (m / blockBytes w) := by
  obtain ⟨-, lgB⟩ := hP.lbb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : Ok P) (x : BitVec 64) :
    x &&& BitVec.ofInt 64 ((B w - 1 : Nat) : Int) = BitVec.ofNat 64 (x.toNat % blockBytes w) := by
  rw [ofInt_nat]
  rcases hP.w with rfl | rfl
  · exact and_mask (n := 7) (by decide) x
  · exact and_mask (n := 6) (by decide) x

/-- The block size, and one less, as immediates. -/
theorem B_lt (hP : Ok P) : B w < 2048 := by rcases hP.w with rfl | rfl <;> decide

theorem imm_B1 (hP : Ok P) : imm12 ((B w - 1 : Nat) : Int) := by
  have := B_lt hP; unfold imm12; omega_using [this]

theorem imm_m1 : imm12 (-1) := by decide

/-! ## Instructions with immediates -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addiI {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi h) (k _ (Upd.write _ _ _))

theorem wp_andi {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n &&& BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem wp_srl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

/-- `addi d, n, -1`. -/
theorem wp_dec {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (-1) :: is)) s Q :=
  wp_addiI imm_m1 fun s' u => k s' (by rw [← add_neg_one]; exact u)

end

/-! ## The compression function -/

/-- What the calls need of the compression function: its contract, and that it
pushes no frames. -/
structure CalleeOk (P : Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressRISCV64 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressRISCV64 P).post s s'
  noFrames : code.noFrames = true

/-- What the call of the compression function needs of the state `s` before
the argument set-up: the hash value `st` at `s7`, the scratch space `scr` at
`s8` and the `len` bytes of blocks at `src` do not overlap each other, and
may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) (len : Nat) : Prop where
  s7 : s.gpr .s7 = st
  s8 : s.gpr .s8 = scr
  d₁ : Region.Disjoint ⟨st, bufOff w⟩ ⟨scr, 280⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, bufOff w⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, 280⟩
  hc : Covers [⟨src, len⟩, ⟨st, bufOff w⟩, ⟨scr, 280⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, bufOff w⟩, ⟨scr, 280⟩] s.wr

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) (src n t : BitVec 64) (last : Bool) : Prop where
  a0 : s.gpr .a0 = σ.gpr .s7
  a1 : s.gpr .a1 = src
  a2 : s.gpr .a2 = n
  a3 : s.gpr .a3 = t
  a4 : ((s.gpr .a4).setWidth 32 != 0) = last
  a5 : s.gpr .a5 = σ.gpr .s8
  cs : ∀ r ∈ preserved, s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- Compressing the `n` blocks at `src` into the hash value at `s7`, with
scratch space at `s8`, by calling the compression function, after `args`
set up its arguments. -/
theorem compressWith_ok {args : List Instr} (hf : CalleeOk P (compress P)) {s : State}
    {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (hs : WP isa (.block (([mov .a0 .s7] : List Instr) ++ args ++ ([mov .a5 .s8] : List Instr))) s
      fun s' => Setup s s' src n t last)
    (h : CallOk (w := w) s st scr src (blockBytes w * n.toNat))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, bufOff w⟩, ⟨scr, 280⟩] s.mem s'.mem →
      stateAt w s'.mem st = compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last →
      Q s') :
    WP isa (compressWith P args) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono hs fun s₁ hs => ?_)
  have e0 : s₁.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.a0.trans h.s7)
  have e1 : s₁.callEntry.gpr .a1 = src := (State.callEntry_gpr _ (by decide)).trans hs.a1
  have e2 : s₁.callEntry.gpr .a2 = n := (State.callEntry_gpr _ (by decide)).trans hs.a2
  have e3 : s₁.callEntry.gpr .a3 = t := (State.callEntry_gpr _ (by decide)).trans hs.a3
  have e4 : s₁.callEntry.gpr .a4 = s₁.gpr .a4 := State.callEntry_gpr _ (by decide)
  have e5 : s₁.callEntry.gpr .a5 = scr := (State.callEntry_gpr _ (by decide)).trans (hs.a5.trans h.s8)
  refine WP.call (k := compressRISCV64 P) hf.verified
    (rd := [⟨src, blockBytes w * n.toNat⟩]) (wr := [⟨st, bufOff w⟩, ⟨scr, 280⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e0, e1, e2, e5]
    exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw
  · intro s' hrd hwr hsp hfr hcs _ hpost
    simp only [compressRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, e0, e1, e2, e3, e4, hs.a4, hs.mem] at hpost
    exact hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (hsp.trans hs.sp)
      (fun r hr => (hcs r hr).trans (hs.cs r hr)) (hs.mem ▸ hfr) hpost

/-! ## Branches -/

theorem zero_iff (s : State) {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.zero r) s = some (decide (k = 0)) := by
  show VG.RISCV64.eval (.zero r) s = _
  rw [eval_zero, h, ofNat_beq_zero hk]

theorem nonzero_iff (s : State) {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.nonzero r) s = some (decide (k ≠ 0)) := by
  show VG.RISCV64.eval (.nonzero r) s = _
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (dst src : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  s9 : s.gpr .s9 = src + BitVec.ofNat 64 j
  a7 : s.gpr .a7 = BitVec.ofNat 64 (r + j)
  t3 : s.gpr .t3 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .a7 → x ≠ .t3 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The loop copying `k ≥ 1` bytes from `src` (at `s9`) to the buffer, from
byte `r` on (in `a7`). -/
theorem copyLoop_ok {s₀ : State} {st src : Addr} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hs7 : s₀.gpr .s7 = st) (hs9 : s₀.gpr .s9 = src) (ha7 : s₀.gpr .a7 = BitVec.ofNat 64 r)
    (ht3 : s₀.gpr .t3 = BitVec.ofNat 64 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, k⟩ ⟨st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega_using [], by omega_using [hk], by omega_using [], by simp [hs9],
      by rw [ha7, Nat.add_zero], by rw [ht3, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega_using [hj]))).bytes (R := ⟨src, k⟩)
      (by simpa using hd) (by show k ≤ 2 ^ 64; omega_using [hk']) hj
  -- The byte written.
  have hout : InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hs7' : s.gpr .s7 = st := by
    rw [h.other .s7 (by decide) (by decide) (by decide) (by decide) (by decide), hs7]
  refine wp_lbu (a := src + BitVec.ofNat 64 j) (by decide) (by rw [h.s9]; simp) hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_sb (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega_using [hN]) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hs7', h.a7, N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₄ u₄ => wp_addi (imm := 1) (by decide) fun s₅ u₅ =>
    wp_dec fun s₆ u₆ => WP.block_nil ?_
  have ht3' : s₆.gpr .t3 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.t3, sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  have hI : CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega_using [hj], ?_, ?_, ht3', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.s9, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.a7, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₆.other x h5, u₅.other x h4, u₄.other x h3, g₃.gpr, u₂.other x h2, u₁.other x h1,
        h.other x h1 h2 h3 h4 h5]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₀.mem src k).length := by simp [bytesAt]; omega_using [hj]
      have hl : (List.take j (bytesAt s₀.mem src k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega_using [hk', hj]), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [nonzero_iff s₆ ht3' (by omega_using [hk'])]; simp; omega_using [hjk], hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [nonzero_iff s₆ ht3' (by omega_using [hk'])]; simp; omega_using [hj, hjk],
      k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjk], hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  a7 : s.gpr .a7 = BitVec.ofNat 64 (r + j)
  t3 : s.gpr .t3 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .t2 → x ≠ .a7 → x ≠ .t3 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer, from byte `r` on (in `a7`). -/
theorem zeroLoop_ok {s₀ : State} {st : Addr} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hs7 : s₀.gpr .s7 = st) (ha7 : s₀.gpr .a7 = BitVec.ofNat 64 r)
    (ht3 : s₀.gpr .t3 = BitVec.ofNat 64 k) (ht1 : s₀.gpr .t1 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega_using [], by omega_using [hk], by omega_using [], by rw [ha7, Nat.add_zero], by rw [ht3, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hs7' : s.gpr .s7 = st := by rw [h.other .s7 (by decide) (by decide) (by decide), hs7]
  refine wp_add fun s₁ u₁ => wp_sb (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega_using [hN]) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hs7', h.a7, N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_dec fun s₄ u₄ => WP.block_nil ?_
  have ht3' : s₄.gpr .t3 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t3, sub_ofNat (by omega_using [hj]),
      Nat.sub_sub]
  have hI : ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega_using [hj], ?_, ht3', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.a7, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .t1 (by decide) (by decide) (by decide), ht1, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega_using [hk', hj]), List.length_replicate]
      rfl
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [nonzero_iff s₄ ht3' (by omega_using [hk'])]; simp; omega_using [hjk], hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [nonzero_iff s₄ ht3' (by omega_using [hk'])]; simp; omega_using [hj, hjk],
      k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjk], hI⟩

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  have hN := hP.len
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega_using [hi]), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega_using [h1, hi])

/-! ## Saving and restoring the caller's registers -/

/-- The caller's registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved b g saved m

/-- The memory after saving them (values `g`) at `b + 280 …`. -/
abbrev saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem := Spill.saveMem m b g saved

/-- The scratch space, rounded up to a multiple of 8. -/
abbrev rnd (x : Addr) : Addr := x + BitVec.ofNat 64 (pad x)

theorem saved_off : ∀ p ∈ saved, 280 ≤ p.2 ∧ p.2 + 8 ≤ 328 := by decide

theorem saveMem_congr {l : List (Reg × Nat)} (m : Mem) (b : Addr) {g g' : Reg → BitVec 64}
    (h : ∀ p ∈ l, g p.1 = g' p.1) : Spill.saveMem m b g l = Spill.saveMem m b g' l := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    simp only [Spill.saveMem]
    rw [h (r, d) List.mem_cons_self, ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Saved b g (saveMem m b g) :=
  Spill.saveMem_saved (by decide) m b g

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 280, 48⟩] m (saveMem m b g) :=
  Spill.saveMem_frame (by decide) (by decide) m b g

theorem saved_ne_t0 : ∀ p ∈ saved, p.1 ≠ .t0 := by decide

/-- Rounding the scratch pointer in `sc` up into `t0`, and saving the
registers there. -/
theorem save_ok {sc : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, 280 ≤ d → d + 8 ≤ 328 → InRegions s.wr (rnd (s.gpr sc) + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr .t0 = rnd (s.gpr sc) → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (rnd (s.gpr sc)) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save sc ++ rest)) s Q := by
  unfold save
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_addiI (show imm12 7 by decide) fun s₁ u₁ => wp_andi (show imm12 (-8) by decide) fun s₂ u₂ => ?_
  have h0 : s₂.gpr .t0 = rnd (s.gpr sc) := by rw [u₂.gpr, u₁.gpr, align_eq]
  have g₂ : ∀ r, r ≠ .t0 → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
  refine Spill.save_ok (by rw [h0]; exact align_al _) (by decide)
    (fun p hp => by rw [h0, u₂.wr, u₁.wr]; exact hin _ (saved_off p hp).1 (saved_off p hp).2) ?_
  refine k _ h0 g₂ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp]) ?_
  show Spill.saveMem s₂.mem (s₂.gpr .t0) s₂.gpr saved = _
  rw [h0, u₂.mem, u₁.mem]
  exact saveMem_congr _ _ fun p hp => g₂ _ (saved_ne_t0 p hp)

/-- Restoring the registers from the save area at `scr` (in `s8`). -/
theorem restore_ok {s : State} {scr : Addr} (hs8 : s.gpr .s8 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ d, 280 ≤ d → d + 8 ≤ 328 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q :=
  WP.mono (Spill.restore_wp (l := saved) hal hs8 (by decide) (by decide)
    (fun p hp => hin _ (saved_off p hp).1 (saved_off p hp).2) hsv)
    fun s' h => k s' h.gpr h.other h.mem h.rd h.wr h.sp

/-- The callee-saved registers our code never touches. -/
abbrev untouched : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6]

theorem notU {r : Reg} (hr : r ∈ untouched) (x : Reg) (hx : x ∉ untouched := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

/-- The callee-saved registers are the caller's again once `restore` has run
and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  rcases preserved_split r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hsv p hp
  · exact hu r h

/-! ## The number of buffered bytes, and the buffer's arguments -/

theorem bufLen_ok (hP : Ok P) {s : State} :
    WP isa (Impl.Blake2.RISCV64.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .a7 = BitVec.ofNat 64 (Blake2.bufLen w (s.gpr .s11).toNat) ∧
      (∀ r, r ≠ .a7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.RISCV64.Stream.bufLen
  have hn := (s.gpr .s11).isLt
  generalize hn' : (s.gpr .s11).toNat = n at hn
  have hs11 : s.gpr .s11 = BitVec.ofNat 64 n := by rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (wp_dec fun s₁ u₁ => wp_andi (imm_B1 hP) fun s₂ u₂ =>
    wp_addi (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .a7 → s₃.gpr r = s.gpr r := fun r h1 => by
    rw [u₃.other r h1, u₂.other r h1, u₁.other r h1]
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (decide (n = 0)) (zero_iff s₃ (by rw [g _ (by decide), hs11]) hn)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_li (imm := 0) (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, fun r h1 => by rw [u₄.other r h1, g r h1],
      by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr], by rw [u₄.sp, hsp]⟩
    rw [u₄.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr, hsp⟩
    rw [u₃.gpr, u₂.gpr, u₁.gpr, hs11, sub_ofNat (by omega_using [hb]), mask_mod hP,
      toNat_ofNat_lt (by omega_using [hn']), ← BitVec.ofNat_add]
    simp only [Blake2.bufLen, hb, ↓reduceIte]

/-- The arguments for compressing the buffer, with the byte count in `s11` as
the counter and the final block flag `imm`. -/
theorem bufArgs_ok (hP : Ok P) {σ : State} {imm : Nat} (hi : imm < 2048) :
    WP isa (.block (([mov .a0 .s7] : List Instr) ++ ([.addi .a1 .s7 (N w : Nat), .li .a2 1,
      mov .a3 .s11, .li .a4 (imm : Int)] : List Instr) ++ ([mov .a5 .s8] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .s7 + BitVec.ofNat 64 (bufOff w)) (BitVec.ofNat 64 1)
        (σ.gpr .s11) ((BitVec.ofNat 64 imm).setWidth 32 != 0) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_addi (by have := hP.N64; rw [N_eq]; omega_using [this]) fun s₂ u₂ =>
    wp_li (imm := 1) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_li hi fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), N_eq]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end RISCV64.Stream

end VG.Proof.Blake2

end

end

/-! ### `Blake2.RISCV64.Stream.Update`, which the modules that import this one used -/

section

/-!
# Streaming BLAKE2 on RISC-V: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`), with the structure of the PPC64LE proof
(`VG.Proof.Blake2.PPC64LE.Stream.Update`): `correctMain` for the code with
its scratch space in `a4` (`update_scratch`), and `correctFramed` for it in
a frame on the stack (`update`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream.Update

open VG VG.RISCV64 VG.Spec.Blake2
open VG.Impl.Blake2.RISCV64.Stream (N B mov copyLoop fill compressBuf head direct tail rest
  updateMain update updateScratch saved save restore frameBytes)
open VG.Impl.Blake2.RISCV64 (lbb compress)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_mv wp_addi wp_li wp_add wp_sub)
open VG.RISCV64.Align (pad pad_lt align_al)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR
  stateAt_congr bytesAt_congr bytesAt_add updateRISCV64 updatePost)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev cnt : Nat := (s₀.gpr .a1).toNat
abbrev dp : Addr := s₀.gpr .a2
abbrev len : Nat := (s₀.gpr .a3).toNat
abbrev scr : Addr := s₀.gpr .a4
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev sb : Addr := rnd (scr s₀)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 336⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : (updateRISCV64 P 336).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (s₀.gpr .a1).isLt

/-- A range of the rounded scratch space within the scratch space. -/
theorem sb_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 328) :
    Region.Sub ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ (scR s₀) := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.sub_base _ (by omega_using [h, this])

theorem sb_sub0 (s₀ : State) {n : Nat} (h : n ≤ 328) : Region.Sub ⟨sb s₀, n⟩ (scR s₀) := by
  have := sb_sub s₀ (d := 0) (n := n) (by omega_using [h])
  simpa using this

theorem sb_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 328) :
    (scR s₀).Contains (sb s₀ + BitVec.ofNat 64 d) n := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (st s₀) d ∧ s₀.gpr .a1 = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega_using [this])]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s7 : s.gpr .s7 = st s₀
  s8 : s.gpr .s8 = sb s₀
  s9 : s.gpr .s9 = dp s₀ + BitVec.ofNat 64 c
  s10 : s.gpr .s10 = BitVec.ofNat 64 (len s₀ - c)
  s11 : s.gpr .s11 = BitVec.ofNat 64 (cnt s₀ + c)
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  frame : Frame [stR s₀ w, scR s₀] s₀.mem s.mem
  saved : Saved (sb s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  a7 : s.gpr .a7 = BitVec.ofNat 64 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg :=
  [.s7, .s8, .s9, .s10, .s11, .s0, .s1, .s2, .s3, .s4, .s5, .s6]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  s7 := by rw [hg _ (by simp)]; exact h.s7
  s8 := by rw [hg _ (by simp)]; exact h.s8
  s9 := by rw [hg _ (by simp)]; exact h.s9
  s10 := by rw [hg _ (by simp)]; exact h.s10
  s11 := by rw [hg _ (by simp)]; exact h.s11
  keep := fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-- Writes to the state and the compression function's scratch space keep the
saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (sb s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨sb s₀, 280⟩] m m') : Saved (sb s₀) s₀.gpr m' :=
  Spill.Saved.frame h hf fun p hp' r' hr' => by
    obtain hoff := saved_off p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (sb_sub s₀ (by omega_using [hoff]))
    · exact Offset.disjoint_base _ (by omega_using [hoff]) (by omega_using [hoff])

/-! ## Prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .a4 ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s10 .a3, mov .s11 .a1])) s₀
      fun s => Common w s₀ 0 s ∧ s.mem = saveMem s₀.mem (sb s₀) s₀.gpr := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], sb_contains s₀ (by omega_using [hd₂])⟩)
    fun s₁ h₀ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁ _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), h₀]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · have : r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 ∧ r ≠ .s10 ∧ r ≠ .s11 ∧ r ≠ .t0 := by
      revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1, u₃.other _ this.2.1,
      u₂.other _ this.1, g₁ _ this.2.2.2.2.2]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, sb_sub s₀ (by decide)⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; exact saveMem_saved _ _ _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## The bytes in the buffer -/

theorem bufLen_ok' (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hm : s.mem = saveMem s₀.mem (sb s₀) s₀.gpr) :
    WP isa (Impl.Blake2.RISCV64.Stream.bufLen (w := w)) s (Inv P s₀ 0 (Blake2.bufLen w (cnt s₀))) := by
  have hN := hP.len
  obtain hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (st s₀) (d ++ D s₀ 0) (Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    obtain e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine repr_congr hP (fun i hi => ?_) hd.1
    rw [hm]
    exact (saveMem_frame _ _ _).bytes (R := stR s₀ w)
      (by simpa using hp.st_scr.sub_right (sb_sub s₀ (by decide))) (by simp only; omega_using [hN]) hi
  refine WP.mono (bufLen_ok hP) fun s' ⟨h23, g, m, rd, wr, sp⟩ => ?_
  rw [hC.s11, Nat.add_zero, toNat_ofNat_lt (cnt_lt s₀)] at h23
  exact { hC.of_gpr (fun r hr => g r (notC hr .a7)) m rd wr sp with
    a7 := h23, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    obtain hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega_using [h])
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    obtain hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hj])]
    simp [hj, List.getD_eq_getElem?_getD]

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hr26 : s.gpr .s7 = st s₀)
    (hr28 : s.gpr .s9 = dp s₀ + BitVec.ofNat 64 c) (hr30 : s.gpr .a7 = BitVec.ofNat 64 r)
    (hr11 : s.gpr .t3 = BitVec.ofNat 64 k) (hf : Frame [stR s₀ w, scR s₀] s₀.mem s.mem)
    (hs : Saved (sb s₀) s₀.gpr s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .a7 → x ≠ .t3 → s'.gpr x = s.gpr x) ∧
      s'.gpr .s9 = dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .a7 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s.sp ∧ Frame [stR s₀ w, scR s₀] s₀.mem s'.mem ∧
      Saved (sb s₀) s₀.gpr s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (st s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hck, hi]) (by omega_using [hck, hL, hi])⟩
  obtain hdst : ∀ i < k, InRegions s.wr (st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hrk, hi]) (by omega_using [hrk, hl, hi])⟩
  obtain hd : Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (Offset.sub_base _ (by omega_using [hck]))).sub_right (Offset.sub_base _ (by omega_using [hrk]))
  refine copyLoop_ok (w := w) hP.N64 hk (by omega_using [hrk, hl]) hr26 hr28 hr30 hr11 hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  obtain hx : bytesAt s.mem (dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt hL) (show c + i < len s₀ by omega_using [hck, hi])
  obtain hm : s'.mem = writeBytes s.mem (st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx]
  obtain hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Offset.contains_base _ (by omega_using [hrk]) (by omega_using [hrk, hl]))
  refine ⟨h.other, h.s9.trans (Offset.add_add _ _ _), h.a7, h.rd.trans hrd, h.wr.trans hwr, h.sp,
    hf.trans (hfw.mono (by simp)), saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  obtain e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k := by
    rw [D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
  · rwa [bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => writeBytes_before _ _ _ (by omega_using [hi]) (by rw [bytesAt_length]; omega_using [hrk, hl])
  · rw [hm, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega_using [hrk, hl])]

/-! ## Calling the compression function -/

/-- The blocks compressed are the (full) buffer or blocks of data. -/
def Src (w : Nat) (s₀ : State) (src : Addr) (n : Nat) : Prop :=
  (src = st s₀ + BitVec.ofNat 64 (bufOff w) ∧ n = blockBytes w) ∨
    ∃ c₀, src = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + n ≤ len s₀

theorem callOk (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s)
    {src : Addr} {n : Nat} (hsrc : Src w s₀ src n) : CallOk (w := w) s (st s₀) (sb s₀) src n := by
  obtain hl := hP.len; have := len_lt s₀
  obtain eN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  obtain eso : Region.Sub ⟨sb s₀, 280⟩ (scR s₀) := sb_sub0 s₀ (by decide)
  obtain eSrc : Region.Sub ⟨src, n⟩ (stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base _ (by omega_using []))
    · exact .inr (h' ▸ Offset.sub_base _ (by omega_using [hc₀]))
  refine ⟨h.s7, h.s8, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_, ?_, ?_⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hl])
    · exact (hp.d_st.sub_left (h' ▸ Offset.sub_base _ (by omega_using [hc₀]))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀ w, by simp, bufOff w, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, pad (scr s₀), rfl, by have := pad_lt (scr s₀); simp only; omega_using [this]⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, pad (scr s₀), rfl, by have := pad_lt (scr s₀); simp only; omega_using [this]⟩

theorem commonRegs_preserved : ∀ r ∈ commonRegs, r ∈ preserved := by decide

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨st s₀, bufOff w⟩, ⟨sb s₀, 280⟩] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := hP.len
  obtain hf' : Frame [stR s₀ w, ⟨sb s₀, 280⟩] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨sb s₀, 280⟩, by simp, fun _ h => h⟩
  obtain hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr =>
    hcs r (commonRegs_preserved r hr)
  refine ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by simp)]; exact h.s7,
    by rw [hg _ (by simp)]; exact h.s8, by rw [hg _ (by simp)]; exact h.s9,
    by rw [hg _ (by simp)]; exact h.s10, by rw [hg _ (by simp)]; exact h.s11,
    fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr,
    h.frame.trans (hf'.sub fun r hr => ?_), saved_frame hp h.saved hf'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, sb_sub0 s₀ (by decide)⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀)
    {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf P) s (Inv P s₀ c 0) := by
  have hl := hP.len
  have hN := hP.N64
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (compressWith_ok hf (bufArgs_ok hP (by decide))
    (by rw [one_toNat, Nat.mul_one]; exact callOk hP hp hI.toCommon (.inl ⟨by rw [hI.s7], rfl⟩))
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => WP.block_nil ?_
  obtain hC := hI.toCommon.after_call hP hp hrd hwr hsp hcs hfr
  refine { hC.of_gpr (fun r hr => u₂.other r (notC hr .a7)) u₂.mem u₂.rd u₂.wr u₂.sp with
    a7 := by rw [u₂.gpr], repr := fun h0 d hd => ?_ }
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  have hlt := hd.2.2
  rw [hst, one_toNat, compressBlocks_one, hI.s7, hI.s11, List.length_append, D, bytesAt_length,
    ← hd.cnt_eq, toNat_ofNat_lt (by rw [← hd.cnt_eq] at hlt; omega_using [hc, hlt])]
  rfl

/-! ## `head`: filling the buffer -/

theorem lt_of_div_zero {x b : Nat} (hb : 0 < b) (h : x / b = 0) : x < b := by
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.div_pos hc hb
  omega_using [h, this]

theorem le_of_div_ne {x b : Nat} (h : x / b ≠ 0) : b ≤ x := by
  refine Nat.le_of_not_lt fun hc => h (Nat.div_eq_of_lt hc)

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hcn := cnt_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  obtain ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  obtain ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_li (B_lt hP) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_srl hP.lbb.1 fun s₃ u₃ => WP.block_nil ?_)
  obtain h11 : s₃.gpr .t3 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.a7, B_eq, sub_ofNat hr]
  obtain h9 : s₃.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c) / blockBytes w) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.s10, shr_ofNat hP (by omega_using [hL])]
  obtain g₃ : ∀ x, x ≠ .t1 → x ≠ .t3 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h1, u₂.other x h2, u₁.other x h2]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- `t3` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .t3 = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .t1 → x ≠ .t3 → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ fun t ht => ?_)
  · refine WP.ite _ (zero_iff s₃ h9 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega_using [hL, this]))
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      obtain hlt := lt_of_div_zero hpos hb
      refine WP.seq (wp_add fun s₄ u₄ => wp_srl hP.lbb.1 fun s₅ u₅ => WP.block_nil ?_)
      obtain h9' : s₅.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c + r) / blockBytes w) := by
        rw [u₅.gpr, u₄.gpr, g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide), hI.s10, hI.a7,
          ← BitVec.ofNat_add, shr_ofNat hP (by omega_using [hr, hl, hlt])]
      obtain g₅ : ∀ x, x ≠ .t1 → x ≠ .t3 → s₅.gpr x = s.gpr x := fun x h1 h2 => by
        rw [u₅.other x h1, u₄.other x h1, g₃ x h1 h2]
      obtain hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, hm₃]
      obtain hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, hrd₃]
      obtain hwr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, hwr₃]
      obtain hsp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, hsp₃]
      refine WP.ite _ (zero_iff s₅ h9' (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega_using [hr, hl, hlt, this]))
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        obtain hlt' := lt_of_div_zero hpos hb'
        refine wp_mv fun s₆ u₆ => WP.block_nil ⟨?_, fun x h1 h2 => by rw [u₆.other x h2, g₅ x h1 h2],
          by rw [u₆.mem, hm₅], by rw [u₆.rd, hrd₅], by rw [u₆.wr, hwr₅], by rw [u₆.sp, hsp₅]⟩
        rw [u₆.gpr, g₅ _ (by decide) (by decide), hI.s10, ha, Nat.min_eq_right (by omega_using [hlt'])]
      · simp only [decide_eq_false_iff_not] at hb'
        obtain hle := le_of_div_ne hb'
        refine WP.block_nil ⟨?_, g₅, hm₅, hrd₅, hwr₅, hsp₅⟩
        rw [u₅.other _ (by decide), u₄.other _ (by decide), h11, ha, Nat.min_eq_left (by omega_using [hle])]
    · simp only [decide_eq_false_iff_not] at hb
      obtain hle := le_of_div_ne hb
      refine WP.block_nil ⟨?_, g₃, hm₃, hrd₃, hwr₃, hsp₃⟩
      rw [h11, ha, Nat.min_eq_left (by omega_using [hle])]
  obtain ⟨tx11, tg, tm, trd, twr, tsp⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_)
  obtain g₆ : ∀ x, x ≠ .t1 → x ≠ .t3 → x ≠ .s10 → x ≠ .s11 → s₆.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₆.other x h4, u₅.other x h3, tg x h1 h2]
  obtain h611 : s₆.gpr .t3 = BitVec.ofNat 64 a := by rw [u₆.other _ (by decide), u₅.other _ (by decide), tx11]
  obtain h622 : s₆.gpr .s10 = BitVec.ofNat 64 (len s₀ - (c + a)) := by
    rw [u₆.other _ (by decide), u₅.gpr, tx11, tg _ (by decide) (by decide), hI.s10, sub_ofNat (by omega_using [ha₂])]
    exact congrArg _ (by omega_using [])
  obtain h624 : s₆.gpr .s11 = BitVec.ofNat 64 (cnt s₀ + (c + a)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tx11, tg _ (by decide) (by decide), hI.s11,
      ← BitVec.ofNat_add, Nat.add_assoc]
  obtain hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, tm]
  obtain hrd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, trd]
  obtain hwr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, twr]
  obtain hsp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, tsp]
  obtain hkeep₆ : ∀ r ∈ untouched, s₆.gpr r = s₀.gpr r := fun r hr => by
    rw [g₆ r (notU hr .t1) (notU hr .t3) (notU hr .s10) (notU hr .s11), hI.keep r hr]
  refine WP.ite _ (zero_iff s₆ h611 (by omega_using [hL, ha₂])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨⟨by omega_using [hc], hrd₆.trans hI.rd, hwr₆.trans hI.wr, hsp₆.trans hI.sp, ?_, ?_, ?_, h622,
      h624, hkeep₆, by rw [hm₆]; exact hI.frame, by rw [hm₆]; exact hI.saved⟩, ?_, ?_⟩
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.s9
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.a7
    · rw [hm₆, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega_using [hb]) (by omega_using [ha₁, hb]) (by omega_using [ha₂, hb])
      (hrd₆.trans hI.rd) (hwr₆.trans hI.wr)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s9)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.a7) h611
      (by rw [hm₆]; exact hI.frame) (by rw [hm₆]; exact hI.saved) (by rw [hm₆]; exact hI.repr))
      fun s₈ ⟨g₈, h821, h823, rd₈, wr₈, sp₈, f₈, sv₈, rp₈⟩ => ?_
    refine ⟨⟨by omega_using [ha₂, hb], rd₈, wr₈, sp₈.trans (hsp₆.trans hI.sp), ?_, ?_, h821, ?_, ?_, fun r hr => ?_, f₈, sv₈⟩,
      h823, rp₈⟩
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h622
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h624
    · rw [g₈ r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .a7) (notU hr .t3)]
      exact hkeep₆ r hr

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s) :
    WP isa (head P) s (HeadPost P s₀) := by
  obtain hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.ite _ (zero_iff s hI.a7 (by omega_using [hr, hl'])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.ite _ (zero_iff s₂ hI₂.s10 (by omega_using [hL])) (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₂, .inl ⟨by omega_using [hb'], by omega_using [hb]⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      obtain e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega_using [hr, hb']
      rw [e] at hI₂
      exact WP.mono (compressBuf_ok hP hf hp hI₂) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega_using [hb'], rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

/-- The arguments for compressing blocks of data. -/
theorem directArgs_ok {σ : State} (hB : B w < 2048) :
    WP isa (.block (([mov .a0 .s7] : List Instr) ++ ([mov .a1 .s9, mov .a2 .t2,
      .addi .a3 .s11 (B w : Nat), .li .a4 0] : List Instr) ++ ([mov .a5 .s8] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .s9) (σ.gpr .t2) (σ.gpr .s11 + BitVec.ofNat 64 (B w)) false := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_addi hB fun s₄ u₄ =>
    wp_li (imm := 0) (by decide) fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain hcs : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {c : Nat}
    (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (direct P) s (Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hcn := cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  obtain hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_dec fun s₁ u₁ => wp_srl hP.lbb.1 fun s₂ u₂ => WP.block_nil ?_)
  obtain h10 : s₂.gpr .t2 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr, hI.s10, sub_ofNat (by omega_using [hc]), shr_ofNat hP (by omega_using [hL]), hk]
  have hC₂ : Common w s₀ c s₂ := hI.toCommon.of_gpr
    (fun r hr => by rw [u₂.other r (notC hr .t2), u₁.other r (notC hr .t1)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  obtain h23 : s₂.gpr .a7 = BitVec.ofNat 64 0 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hI.a7
  obtain hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.ite _ (zero_iff s₂ h10 (by omega_using [hL, hkle])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₂, h23, by rw [hm₂]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  obtain hBk : blockBytes w * k + 1 ≤ len s₀ - c := by omega_using [hdm, hkle, hb]
  obtain hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega_using [hb])
  obtain hsrc : Src w s₀ (s₂.gpr .s9) (blockBytes w * (s₂.gpr .t2).toNat) :=
    .inr ⟨c, hC₂.s9, by rw [h10, toNat_ofNat_lt (by omega_using [hL, hkle])]; omega_using [hBk]⟩
  refine WP.seq (compressWith_ok hf (directArgs_ok (B_lt hP)) (callOk hP hp hC₂ hsrc)
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  obtain hC' := hC₂.after_call hP hp hrd hwr hsp hcs hfr
  refine wp_dec fun s₁ u₁ => wp_andi (imm_B1 hP) fun s₄ u₄ =>
    wp_addi (imm := 1) (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_mv fun s₉ u₉ => wp_li (imm := 0) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain hm : (len s₀ - c - 1) % blockBytes w + 1 = len s₀ - (c + blockBytes w * k) := by omega_using [hc, hdm]
  obtain hr9 : s₅.gpr .t1 = BitVec.ofNat 64 (len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₄.gpr, u₁.gpr, hC'.s10, sub_ofNat (by omega_using [hc]), mask_mod hP,
      toNat_ofNat_lt (by omega_using [hL]), ← BitVec.ofNat_add, hm]
  obtain h10₆ : s₆.gpr .t2 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₁.other _ (by decide), hC'.s10, hr9,
      sub_ofNat (by omega_using [])]
    exact congrArg _ (by omega_using [hdm])
  obtain hg : ∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .s10 → x ≠ .s11 → x ≠ .a7 → s₁₀.gpr x = s'.gpr x :=
    fun x h1 h2 h3 h4 h5 h6 => by
      rw [u₁₀.other x h6, u₉.other x h4, u₈.other x h5, u₇.other x h3, u₆.other x h2, u₅.other x h1,
        u₄.other x h1, u₁.other x h1]
  obtain hm₉ : s₁₀.mem = s'.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₁.mem]
  refine ⟨⟨by omega_using [hc, hdm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₁.rd, hC'.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₁.wr, hC'.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₁.sp, hC'.sp]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.s7
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.s8
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h10₆, u₅.other _ (by decide), u₄.other _ (by decide),
      u₁.other _ (by decide), hC'.s9, Offset.add_add]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), hr9]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other .s11 (by decide),
      u₇.other .t2 (by decide), h10₆, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₁.other _ (by decide), hC'.s11, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .s10) (notU hr .s11) (notU hr .a7)]
    exact hC'.keep r hr
  · rw [u₁₀.gpr]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    obtain e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₂.mem (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₂.data hp (by omega_using [hm, hi])).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₂]; exact hI.repr h0 d hd) ?_
    rw [hst, h10, hC₂.s9, hC₂.s11, B_eq, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega_using [hkle, hlt]),
      toNat_ofNat_lt (by omega_using [hBk', hm, hcnt, hlt]), List.length_append, D, bytesAt_length, ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  obtain hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mv fun s₁ u₁ => wp_add fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain hg : ∀ x, x ≠ .t3 → x ≠ .s11 → x ≠ .s10 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  obtain h11 : s₃.gpr .t3 = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.s10]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega_using [hc₁]) (by omega_using [hc₂]) (by omega_using [hc₁])
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.s7)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.s9)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.a7) h11
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h421, h423, rd₄, wr₄, sp₄, f₄, sv₄, rp₄⟩ => ?_
  obtain e : c + (len s₀ - c) = len s₀ := by omega_using [hc₁]
  rw [e] at h421 rp₄
  rw [Nat.zero_add] at h423 rp₄
  obtain g : ∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .a7 → x ≠ .t3 → x ≠ .s11 → x ≠ .s10 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [g₄ x h1 h2 h3 h4 h5, hg x h5 h6 h7]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, by rw [sp₄, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, h421, ?_, ?_,
    fun r hr => ?_, f₄, sv₄⟩, h423, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), hI.s11, hI.s10, ← BitVec.ofNat_add]
    exact congrArg _ (by omega_using [e])
  · rw [g r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .a7) (notU hr .t3) (notU hr .s11)
      (notU hr .s10)]
    exact hI.keep r hr

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {s : State}
    (h : HeadPost P s₀ s) : WP isa (rest P) s (Full P s₀) := by
  obtain hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  have hc := hI.c_le
  unfold rest
  refine WP.ite _ (zero_iff s hI.s10 (by omega_using [hL])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI, hr⟩
    · omega_using [hb, hc']
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega_using [hb]
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI) fun s₂ hI₂ => ?_)
    obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega_using [hc', hdm]) (by omega_using [hdm, hmod]) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega_using [hc', hdm]⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (s₀ : State) (s : State) : Prop :=
  Common w s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (st s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P s₀ s) : Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ updatePost P s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Done P s₀ s) :
    WP isa (.block restore) s (Post P s₀) := by
  refine restore_ok (scr := sb s₀) hI.1.s8 (align_al _)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], sb_contains s₀ (by omega_using [hd₂])⟩)
    s₀.gpr hI.1.saved fun s' hs ho hmem _ _ hsp => ⟨⟨preserved_of hs fun r hr => ?_,
      by rw [hsp, hI.1.sp], hs (.ra, 280) (by decide)⟩, fun h0 d hr hc hl => ?_⟩
  · rw [ho r (by revert r; decide), hI.1.keep r hr]
  · rw [hmem]; exact hI.2 h0 d ⟨hr, hc, hl⟩

/-- `update`, with its scratch space in `a4`. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (updateMain P .a4) s₀ (Post P s₀) := by
  obtain hL := len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok' hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  refine WP.ite _ (zero_iff s₂ hI.s10 (by omega_using [hL])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq, Nat.sub_zero] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI.toCommon, fun h0 d hd => ?_⟩
    have := hI.repr h0 d hd
    obtain e0 : ∀ n, n = 0 → bytesAt s₀.mem (dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show D s₀ (len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not, Nat.sub_zero] at hb
    obtain hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega_using [hb]) hI) fun s₄ h =>
      WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

theorem noFrames_updateMain (hf : CalleeOk P (compress P)) (sc : Reg) :
    (updateMain P sc).noFrames = true := by
  simp only [updateMain, head, rest, fill, compressBuf, direct, tail, Impl.Blake2.RISCV64.Stream.compressWith,
    copyLoop, Impl.Blake2.RISCV64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- `update_scratch`, with the 336 bytes of scratch it uses. -/
theorem correctN (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateRISCV64 P 336).pre s₀) :
    WP isa (updateScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateRISCV64 P 336).post s₀ s' :=
  correctMain hP hf (pre_of hpre)

/-- `update_scratch`, with 576 bytes of scratch, for Argon2's calls: the code
runs as it does with the first 336 of them (`WP.narrow`). -/
theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateRISCV64 P).pre s₀) :
    WP isa (updateScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hss, hds, hdc⟩ := hpre
  obtain hsub : Region.Sub (scR s₀) ⟨scr s₀, 576⟩ := Region.sub_prefix (by decide)
  obtain hpσ : Pre w (s₀.withRegions [dR s₀] [stR s₀ w, scR s₀]) :=
    ⟨rfl, rfl, hss.sub_right hsub, hds, hdc.sub_right hsub⟩
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun _ _ _ _ _ h => h) (noFrames_updateMain hf .a4)
  · rw [hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨scr s₀, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨scr s₀, 576⟩, by simp, 0, by simp, by simp⟩

/-- `update`: `update_scratch`, with its scratch space in a frame. -/
theorem correctFramed (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateFramedRISCV64 P).pre s₀) :
    WP isa (update P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateFramedRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hds, -, hsp, hks, hkd⟩ := hpre
  refine WP.alloc (by decide) hsp ?_
  refine WP.seq (Wp.wp_addSp (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  let F : Region := ⟨s₀.sp - BitVec.ofNat 64 336, 336⟩
  obtain ha4 : s₁.gpr .a4 = s₀.sp - BitVec.ofNat 64 336 := by
    rw [u₁.gpr]; simp [allocd, frameBytes]
  obtain g₁ : ∀ r, r ≠ .a4 → s₁.gpr r = s₀.gpr r := fun r hr => u₁.other r hr
  have hrd₁ : s₁.rd = s₀.rd := u₁.rd
  have hwr₁ : s₁.wr = F :: s₀.wr := u₁.wr
  let σ := s₁.withRegions [dR s₀] [stR s₀ w, F]
  obtain hpσ : Pre w σ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show [dR s₀] = [dR σ]
      simp only [dR, dp, len, σ, State.withRegions_gpr, g₁ .a2 (by decide), g₁ .a3 (by decide)]
    · show [stR s₀ w, F] = [stR σ w, scR σ]
      simp only [stR, st, scR, scr, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha4, F]
    · simp only [stR, scR, scr, st, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha4]
      exact hks.symm
    · simp only [stR, dR, dp, len, st, σ, State.withRegions_gpr, g₁ .a0 (by decide),
        g₁ .a2 (by decide), g₁ .a3 (by decide)]
      exact hds
    · simp only [scR, dR, dp, len, scr, σ, State.withRegions_gpr, g₁ .a2 (by decide),
        g₁ .a3 (by decide), ha4]
      exact hkd.symm
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun s' hrd' hwr' hsp' _ hpost m _ fl => ?_)
    (noFrames_updateMain hf .a4)
  · rw [hrd₁, hwr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  · rw [hwr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  obtain ⟨⟨hpres, hsp₂, hra⟩, hpost⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hpres hsp₂ hra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun h0 d hr hc hl => ?_⟩
  · show s'.gpr r = s₀.gpr r
    rw [hpres r hr, g₁ r (by revert r; decide)]
  · show s'.sp + BitVec.ofNat 64 frameBytes = s₀.sp
    rw [hsp₂, u₁.sp]; exact BitVec.sub_add_cancel _ _
  · show s'.gpr .ra = s₀.gpr .ra
    rw [hra, g₁ _ (by decide)]
  · have := hpost h0 d
    simp only [State.withRegions_mem, State.withRegions_gpr, u₁.mem,
      g₁ .a0 (by decide), g₁ .a1 (by decide), g₁ .a2 (by decide), g₁ .a3 (by decide)] at this
    -- The `free` loses the frame's bytes, which lie apart from the state.
    exact repr_congr hP (fun i hi => lost_byte fl (R := stR s₀ w) hks.symm hi) (this hr hc hl)

end VG.Proof.Blake2.RISCV64.Stream.Update

end

end

/-!
# Streaming BLAKE2 on RISC-V: `finalize`

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE.Stream.Finalize`):
`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_ok`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`compressWith_ok`), copies the
hash value out a byte at a time (`output_ok`) and restores the registers
(`restore_ok`); `correctMain` for the code with its scratch space in `a3`
(`finalize_scratch`), and `correctFramed` for it in a frame on the stack
(`finalize`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream.Finalize

open VG VG.RISCV64 VG.Spec.Blake2
open VG.Impl.Blake2.RISCV64.Stream (N B mov zeroLoop pad compressLast output finalizeMain finalize
  finalizeScratch saved save restore frameBytes)
open VG.Impl.Blake2.RISCV64 (compress)
open VG.Proof.Blake2 (finalizeRISCV64 finalizeFramedRISCV64 finalizePost bufOff final_eq stateAt_congr
  bytesAt_congr bytesAt_add bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_mv wp_li wp_sub wp_lbu wp_sb)
open VG.RISCV64.Align (pad_lt align_al)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_snoc writeBytes_before)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev op : Addr := s₀.gpr .a2
abbrev scr : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev sb : Addr := rnd (scr s₀)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨op s₀, bufOff w⟩
abbrev scR : Region := ⟨scr s₀, 336⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)

theorem pre_of {w : Nat} {P : Params w} {s₀ : State} (h : (finalizeRISCV64 P 336).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A range of the rounded scratch space within the scratch space. -/
theorem sb_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 328) :
    Region.Sub ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ (scR s₀) := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (VG.RISCV64.Align.pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.sub_base _ (by omega_using [h, this])

theorem sb_sub0 (s₀ : State) {n : Nat} (h : n ≤ 328) : Region.Sub ⟨sb s₀, n⟩ (scR s₀) := by
  have := sb_sub s₀ (d := 0) (n := n) (by omega_using [h])
  simpa using this

theorem sb_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 328) :
    (scR s₀).Contains (sb s₀ + BitVec.ofNat 64 d) n := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (VG.RISCV64.Align.pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : Pre w s₀) {g : Reg → BitVec 64} {m m' : Mem}
    (h : Saved (sb s₀) g m) (hf : Frame [stR s₀ w, outR s₀ w, ⟨sb s₀, 280⟩] m m') :
    Saved (sb s₀) g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    obtain hoff := saved_off p hp'
    obtain hsub : Region.Sub ⟨sb s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := sb_sub s₀ (by omega_using [hoff])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left hsub
    · exact hp.out_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega_using [hoff]) (by omega_using [hoff])

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s7 : s.gpr .s7 = st s₀
  s8 : s.gpr .s8 = sb s₀
  s9 : s.gpr .s9 = op s₀
  s11 : s.gpr .s11 = s₀.gpr .a1
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  mem : s.mem = saveMem s₀.mem (sb s₀) s₀.gpr

theorem prologue_ok {w : Nat} {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .a3 ++ ([mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s11 .a1] : List Instr)))
      s₀ (Start s₀) := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], sb_contains s₀ (by omega_using [hd₂])⟩)
    fun s₁ h₀ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      g₁ _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₀]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide)]
  · rw [u₅.other _ (notU hr .s11), u₄.other _ (notU hr .s9), u₃.other _ (notU hr .s8),
      u₂.other _ (notU hr .s7), g₁ _ (notU hr .t0)]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## Zeroing the rest of the buffer -/

section
variable {w : Nat}

/-- Zeroing the buffer from byte `r` (in `a7`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hN : bufOff w ≤ 64) (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2048) (hs7 : s.gpr .s7 = st) (ha7 : s.gpr .a7 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad (w := w)) s fun s' =>
      (∀ x, x ≠ .t1 → x ≠ .t3 → x ≠ .t2 → x ≠ .a7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold pad
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => wp_li (by rw [B_eq]; omega_using [hbb]) fun s₂ u₂ =>
    wp_sub fun s₃ u₃ => WP.block_nil ?_)
  obtain g : ∀ x, x ≠ .t1 → x ≠ .t3 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  obtain h11 : s₃.gpr .t3 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .a7 (by decide), u₂.gpr, u₁.other .a7 (by decide), ha7,
      B_eq, sub_ofNat hr]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ (zero_iff s₃ h11 (by omega_using [hbb])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ _ => g x h1 h2, hrd₃, hwr₃, hsp₃, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₃]
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st) (r := r) hN (by omega_using [hb]) (by omega_using [hr, hbb])
      (by rw [g _ (by decide) (by decide), hs7])
      (by rw [g _ (by decide) (by decide), ha7]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr₃]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 h4 => by rw [h.other x h3 h4 h2, g x h1 h2], by rw [h.rd, hrd₃],
      by rw [h.wr, hwr₃], by rw [h.sp, hsp₃], ?_⟩
    rw [h.mem, hm₃]

end

/-! ## Bytes -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv => lhs; rw [show bb = r + (bb - r) by omega_using [hr]]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      writeBytes_before m st _ (by omega_using [hi] : N + i < N + r) (by simp; omega_using [hr, hlt])]
  · rw [hm]; exact bytesAt_writeBytes_self _ _ (by simp) (by omega_using [hlt])

/-! ## Copying the hash value out -/

section
variable {w : Nat}

/-- After copying `k` bytes. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .t1 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
    s.mem = writeBytes σ.mem (σ.gpr .s9) (bytesAt σ.mem (σ.gpr .s7) k)

theorem bytesAt_succ (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  simp [bytesAt, List.range_succ]

theorem output_ok {σ : State} (hN : bufOff w ≤ 64)
    (hin : ∀ a n, (⟨σ.gpr .s7, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .s9, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .s7, bufOff w⟩ ⟨σ.gpr .s9, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .t1 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = writeBytes σ.mem (σ.gpr .s9) (bytesAt σ.mem (σ.gpr .s7) (bufOff w)) := by
  unfold output
  rw [N_eq]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hsp, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, rfl, by simp [bytesAt, writeBytes_nil]⟩
  obtain hl : (bytesAt σ.mem (σ.gpr .s7) k).length = k := by simp [bytesAt]
  refine wp_lbu (a := σ.gpr .s7 + BitVec.ofNat 64 k) (by omega_using [hN, hk])
    (by rw [hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hN, hk])))
    fun s₁ u₁ => wp_sb (a := σ.gpr .s9 + BitVec.ofNat 64 k) (by omega_using [hN, hk]) ?_ ?_ fun s₂ g₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
        by rw [g₂.wr, u₁.wr, hwr], by rw [g₂.sp, u₁.sp, hsp], ?_⟩
  · rw [u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hN, hk]))
  · have hv : s.mem (σ.gpr .s7 + BitVec.ofNat 64 k) = σ.mem (σ.gpr .s7 + BitVec.ofNat 64 k) := by
      rw [hm]
      exact (writeBytes_frame (R := ⟨σ.gpr .s9, bufOff w⟩) _ _ _
        (contains_prefix _ (by rw [hl]; omega_using [hk]))).bytes (R := ⟨σ.gpr .s7, bufOff w⟩)
        (by simpa using hd) (by show bufOff w ≤ 2 ^ 64; omega_using [hN]) hk
    rw [g₂.mem, u₁.gpr, u₁.mem, hv, hm, setWidth_byte, bytesAt_succ,
      writeBytes_snoc _ _ _ _ (by rw [hl]; omega_using [hN, hk]), hl]

end

/-! ## The whole function -/

section
variable {w : Nat} {P : Params w}

theorem noFrames_finalizeMain (hf : CalleeOk P (compress P)) (sc : Reg) :
    (finalizeMain P sc).noFrames = true := by
  simp only [finalizeMain, pad, compressLast, Impl.Blake2.RISCV64.Stream.compressWith, zeroLoop,
    Impl.Blake2.RISCV64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The registers kept from the prologue to the epilogue. -/
abbrev commonKeep : List Reg :=
  [.s7, .s8, .s9, .s11, .s0, .s1, .s2, .s3, .s4, .s5, .s6]

theorem commonKeep_ok : ∀ r ∈ commonKeep,
    r ∈ preserved ∧ r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .t2 ∧ r ≠ .a7 := by decide

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ finalizePost P s₀ s'

/-- `finalize`, with its scratch space in `a3`. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (finalizeMain P .a3) s₀ (Post P s₀) := by
  have hl := hP.len
  have hN := hP.N64
  have hbb := hP.bb
  obtain hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  obtain hsave_st : ∀ r ∈ [(⟨sb s₀ + BitVec.ofNat 64 280, 48⟩ : Region)], (stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (sb_sub s₀ (by decide))
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [h₁.mem]; exact (saveMem_frame _ _ _).bytes (R := stR s₀ w) hsave_st (by simp only; omega_using [hl]) hi
  refine WP.seq (WP.mono (bufLen_ok hP) fun s₂ ⟨r23₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [h₁.s11] at r23₂
  generalize hn : (s₀.gpr .a1).toNat = n at r23₂
  obtain hr : Blake2.bufLen w n ≤ blockBytes w := bufLen_le (by omega_using [hbb]) n
  obtain hx19₂ : s₂.gpr .s7 = st s₀ := by rw [g₂ _ (by decide), h₁.s7]
  refine WP.seq (WP.mono (pad_ok (st := st s₀) hN hr (by omega_using [hl]) hx19₂ r23₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨stR s₀ w, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])⟩
  obtain g₃' : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t2 → r ≠ .a7 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h4]
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  obtain hsp₃ : s₃.sp = s₀.sp := by rw [sp₃, sp₂, h₁.sp]
  obtain hx19₃ : s₃.gpr .s7 = st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s7]
  obtain hx20₃ : s₃.gpr .s8 = sb s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s8]
  obtain hm₃ : s₃.mem = writeBytes s₁.mem (st s₀ + BitVec.ofNat 64 (bufOff w + Blake2.bufLen w n))
      (List.replicate (blockBytes w - Blake2.bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  obtain hbuf : Region.Sub ⟨st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega_using [])
  obtain hscr : Region.Sub ⟨sb s₀, 280⟩ (scR s₀) := sb_sub0 s₀ (by decide)
  obtain hcall : CallOk (w := w) s₃ (st s₀) (sb s₀) (s₃.gpr .s7 + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (BitVec.ofNat 64 1).toNat) := by
    rw [show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.mul_one, hx19₃]
    refine ⟨hx19₃, hx20₃, (hp.st_scr.sub_left hstN).sub_right hscr,
      Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hl]), (hp.st_scr.sub_left hbuf).sub_right hscr, ?_, ?_⟩
    · rw [hrd₃, hwr₃, hp.rd, hp.wr, List.nil_append]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, bufOff w, rfl, by simp only; omega_using []⟩
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega_using []⟩
      · exact ⟨scR s₀, by simp, VG.RISCV64.Align.pad (scr s₀), rfl,
          by have := pad_lt (scr s₀); simp only; omega_using [this]⟩
    · rw [hwr₃, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega_using []⟩
      · exact ⟨scR s₀, by simp, VG.RISCV64.Align.pad (scr s₀), rfl,
          by have := pad_lt (scr s₀); simp only; omega_using [this]⟩
  unfold compressLast
  refine WP.seq (compressWith_ok hf (bufArgs_ok hP (by decide)) hcall fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_)
  obtain cs : ∀ r ∈ commonKeep, s₄.gpr r = s₁.gpr r := fun r hr => by
    obtain ⟨h1, h3, h4, h5, h6⟩ := commonKeep_ok r hr
    rw [cs₄ r h1, g₃' r h3 h4 h5 h6]
  obtain hx19₄ : s₄.gpr .s7 = st s₀ := by rw [cs _ (by simp), h₁.s7]
  obtain hx21₄ : s₄.gpr .s9 = op s₀ := by rw [cs _ (by simp), h₁.s9]
  obtain hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (σ := s₄) hN (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, sp₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hx19₄] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega_using [h]⟩
  · rw [hwr₄, hp.wr]
    rw [hx21₄] at h
    exact ⟨outR s₀ w, by simp, h⟩
  · rw [hx19₄, hx21₄]; exact hp.st_out.sub_left hstN
  -- What the call and the stores wrote.
  obtain F₁ : Frame [stR s₀ w, outR s₀ w, ⟨sb s₀, 280⟩] s₁.mem s₅.mem := by
    obtain f₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega_using [hr]) (by omega_using [hl, hr]))
    obtain f₅ : Frame [outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hx21₄]
      exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain hsv : Saved (sb s₀) s₀.gpr s₅.mem := Saved.frame hp (h₁.mem ▸ saveMem_saved _ _ _) F₁
  refine restore_ok (scr := sb s₀) (by rw [g₅ _ (by decide), cs _ (by simp), h₁.s8]) (align_al _)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [rd₅, wr₅, rd₄, wr₄, hrd₃, hwr₃, hp.wr],
      sb_contains s₀ (by omega_using [hd₂])⟩) s₀.gpr hsv
    fun s₆ hs ho m₆ _ _ sp₆ => ⟨⟨preserved_of hs fun r hr => ?_, by rw [sp₆, sp₅, sp₄, hsp₃],
      hs (.ra, 280) (by decide)⟩, ?_⟩
  · rw [ho r (by revert r; decide), g₅ r (notU hr .t1), cs r (by revert r; decide), h₁.keep r hr]
  · intro h0 d hR hlt hcnt
    obtain hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    obtain hx24₃ : (s₃.gpr .s11).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s11, hn]
    rw [m₆, m₅, hx21₄, hx19₄, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega_using [hl]),
      bytesAt_state _ _ hP.w.symm, e₄, show (BitVec.ofNat 64 1).toNat = 0 + 1 from rfl,
      compressBlocks_succ, compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero,
      hx24₃, hx19₃, show ((BitVec.ofNat 64 1).setWidth 32 != 0) = true from rfl]
    refine final_eq P (by omega_using [hbb]) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega_using [hi] : i < bufOff w + Blake2.bufLen w d.length)
          (by simp; omega_using [hl, hr]), hkeep i (by omega_using [hi])]
    · rw [pad_bytes hr (by omega_using [hl]) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega_using [hr, hi])]

/-- `finalize_scratch`, with the 336 bytes of scratch it uses. -/
theorem correctN (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeRISCV64 P 336).pre s₀) :
    WP isa (finalizeScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeRISCV64 P 336).post s₀ s' :=
  correctMain hP hf (pre_of hpre)

/-- `finalize_scratch`, with 576 bytes of scratch, for Argon2's calls: the
code runs as it does with the first 336 of them (`WP.narrow`). -/
theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeRISCV64 P).pre s₀) :
    WP isa (finalizeScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hso, hss, hos⟩ := hpre
  obtain hsub : Region.Sub (scR s₀) ⟨scr s₀, 576⟩ := Region.sub_prefix (by decide)
  obtain hpσ : Pre w (s₀.withRegions [] [stR s₀ w, outR s₀ w, scR s₀]) :=
    ⟨rfl, rfl, hso, hss.sub_right hsub, hos.sub_right hsub⟩
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun _ _ _ _ _ h => h) (noFrames_finalizeMain hf .a3)
  · rw [hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨scr s₀, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨scr s₀, 576⟩, by simp, 0, by simp, by simp⟩

/-- `finalize`: `finalize_scratch`, with its scratch space in a frame. -/
theorem correctFramed (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeFramedRISCV64 P).pre s₀) :
    WP isa (finalize P) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeFramedRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hso, -, hsp, hks, hko⟩ := hpre
  refine WP.alloc (by decide) hsp ?_
  refine WP.seq (Wp.wp_addSp (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  let F : Region := ⟨s₀.sp - BitVec.ofNat 64 336, 336⟩
  obtain ha3 : s₁.gpr .a3 = s₀.sp - BitVec.ofNat 64 336 := by
    rw [u₁.gpr]; simp [allocd, frameBytes]
  obtain g₁ : ∀ r, r ≠ .a3 → s₁.gpr r = s₀.gpr r := fun r hr => u₁.other r hr
  have hrd₁ : s₁.rd = s₀.rd := u₁.rd
  have hwr₁ : s₁.wr = F :: s₀.wr := u₁.wr
  let σ := s₁.withRegions [] [stR s₀ w, outR s₀ w, F]
  obtain hpσ : Pre w σ := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · show [stR s₀ w, outR s₀ w, F] = [stR σ w, outR σ w, scR σ]
      simp only [stR, st, outR, op, scR, scr, σ, State.withRegions_gpr, g₁ .a0 (by decide),
        g₁ .a2 (by decide), ha3, F]
    · simp only [stR, outR, st, op, σ, State.withRegions_gpr, g₁ .a0 (by decide), g₁ .a2 (by decide)]
      exact hso
    · simp only [stR, scR, scr, st, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha3]
      exact hks.symm
    · simp only [outR, scR, scr, op, σ, State.withRegions_gpr, g₁ .a2 (by decide), ha3]
      exact hko.symm
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun s' hrd' hwr' hsp' _ hpost m _ fl => ?_)
    (noFrames_finalizeMain hf .a3)
  · rw [hrd₁, hwr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  · rw [hwr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  obtain ⟨⟨hpres, hsp₂, hra⟩, hpost⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hpres hsp₂ hra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun h0 d hr hl hc => ?_⟩
  · show s'.gpr r = s₀.gpr r
    rw [hpres r hr, g₁ r (by revert r; decide)]
  · show s'.sp + BitVec.ofNat 64 frameBytes = s₀.sp
    rw [hsp₂, u₁.sp]; exact BitVec.sub_add_cancel _ _
  · show s'.gpr .ra = s₀.gpr .ra
    rw [hra, g₁ _ (by decide)]
  · have := hpost h0 d
    simp only [State.withRegions_mem, State.withRegions_gpr, u₁.mem,
      g₁ .a0 (by decide), g₁ .a1 (by decide), g₁ .a2 (by decide)] at this
    -- The `free` loses the frame's bytes, which lie apart from the digest.
    refine Eq.trans ?_ (this hr hl hc)
    exact bytesAt_congr fun i hi => lost_byte fl (R := outR s₀ w) hko.symm hi

end

end VG.Proof.Blake2.RISCV64.Stream.Finalize
