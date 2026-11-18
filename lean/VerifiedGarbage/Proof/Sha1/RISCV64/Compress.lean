module

public import VerifiedGarbage.Proof.Sha1.StateMem
public meta import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Semantics
public meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.Double
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Sha1.Spec
meta import VerifiedGarbage.Impl.Sha1.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Double
public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.Sha1
meta import VerifiedGarbage.TCB.Artifact

/-! ### `Sha1.RISCV64.Contract`, which only this module used -/

section

/-!
# SHA-1: the RISC-V contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply them
(`Contract.Implies`). The return address is in `ra`, which the target's
calling convention requires to be preserved (`VG.RISCV64.abiPreserved`),
not on the stack. `update` and `finalize` keep their working space in a
frame of 144 bytes below the stack pointer, which must not overlap their
buffers.
-/

@[expose] public section

namespace VG.Proof.Sha1

open Spec.Sha1

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 10])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (80 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 20⟩
    let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 80⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .a0) =
      compressBlocks (stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes). The pointer is public. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 84⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize)`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (84
bytes). These may not overlap each other, nor the 144 bytes below the stack
pointer (its frame), which do not wrap around. The stack pointer is 16-byte
aligned. The pointers, `count` and `len` are public; the state and the data
are secret. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 84⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20])`: if
the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

The code may read and write `state` (84 bytes, whose contents on exit are
unspecified) and `out` (20 bytes). These may not overlap each other, nor the
144 bytes below the stack pointer (its frame), which do not wrap around.
The stack pointer is 16-byte aligned. The pointers and `count` are public;
the state is secret. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 84⟩
    let out : Region := ⟨s.gpr .a2, 20⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .a2) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha1

end

end

/-! ### `Sha1.RISCV64.Rounds`, which only this module used -/

section

/-!
# SHA-1 compression function on RISC-V: the message schedule and the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Sha1/PPC64LE/Compress.lean`): each round is `f(b, c, d)`,
symbolically executed once per function (`fcode_ok`), between the addition
of `Wₜ` and `Kₜ` and the rest of the round (`tail_ok`), executed once for all
rounds. The words are the low 32 bits of the registers, and `a` and `b` are
doubled, a word in both halves of its register (`Vars`, `dbl`).
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha1.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1 (roundKW round_eq rounds_zero rounds_succ W_lt W_ge ch_eq maj_eq)

/-- The working variables `v` in the registers of round `t`: `a` and `b`
doubled, and `c`, `d` and `e` in the low 32 bits. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = dbl v[0] ∧ s.gpr (var t 1) = dbl v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4]

/-- The pointers, the count, the return address and the callee-saved
registers: never written by the rounds. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8,
  .s9, .s10, .s11]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega_using []

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .t0, work.getD ((1 + 5 - c) % 5) .t0,
      work.getD ((2 + 5 - c) % 5) .t0, work.getD ((3 + 5 - c) % 5) .t0,
      work.getD ((4 + 5 - c) % 5) .t0].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega_using []))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := pubRegs_ne' r h

/-- `KR` is none of the others. -/
theorem kr_ne : KR ∉ work ∧ KR ≠ T0 ∧ KR ≠ T1 ∧ KR ≠ T2 ∧ KR ∉ pubRegs := by decide

/-! ## One round -/

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x ||| y) &&& z ||| x &&& y

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  (repeat' split) <;> simp only [fval, ch_eq, maj_eq, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d : Reg) (s : State) (x y z : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work)
    (hb : (s.gpr b).setWidth 32 = x) (hc : (s.gpr c).setWidth 32 = y) (hd : (s.gpr d).setWidth 32 = z) :
    WP isa (.block (fcode g b c d)) s fun s' =>
      (s'.gpr T1).setWidth 32 = fval g x y z ∧ (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, b1, b2, -⟩ := work_ne hbw
  obtain ⟨-, c1, c2, -⟩ := work_ne hcw
  obtain ⟨-, d1, d2, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 d1 b2 c2 d2 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp only [fcode, T1, T2, runBlock_cons, runStep_some, runBlock_nil, exec_logic, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, b1, c1, d1, ↓reduceIte,
    reduceCtorEq, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩ <;>
  simp only [lo32_xor, lo32_and, lo32_or, hb, hc, hd, fval]

theorem round_split (t : Nat) :
    round t = ([.add (var t 4) (var t 4) T0, .add (var t 4) (var t 4) KR] : List Instr) ++
      (fcode (fn t) (var t 1) (var t 2) (var t 3) ++
        (([.add (var t 4) (var t 4) T1] : List Instr) ++ tail (var t 0) (var t 1) (var t 4))) := by
  simp only [Impl.Sha1.RISCV64.round, List.append_assoc]

/-- A rotation left, as `rotl` computes it in the low word. -/
theorem rotl_lo (y : Word) {n : Nat} (hn : n < 32) :
    (sext32 (y >>> (32 - n)) ||| sext32 (y <<< n)).setWidth 32 = y.rotateLeft n := by
  rw [lo32_or, lo32_sext, lo32_sext, BitVec.or_comm, rotl_shifts _ hn]

/-- `f(b, c, d)` added into `e`, then the rest of the round, with `a` and `b`
doubled: `e` gets `ROTL⁵(a)` and is doubled, and `b` is rotated. -/
theorem tail_ok (a b e : Reg) (s : State) (x y z fv : Word)
    (haw : a ∈ work) (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hae : a ≠ e)
    (ha : s.gpr a = dbl x) (hb : s.gpr b = dbl y) (he : (s.gpr e).setWidth 32 = z)
    (hf : (s.gpr T1).setWidth 32 = fv) :
    WP isa (.block (([.add e e T1] : List Instr) ++ tail a b e)) s fun s' =>
      s'.gpr e = dbl (z + fv + x.rotateLeft 5) ∧
      (s'.gpr b).setWidth 32 = y.rotateLeft 30 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨-, a1, -, -⟩ := work_ne haw
  obtain ⟨-, e1, -, -⟩ := work_ne hew
  obtain ⟨-, b1, -, -⟩ := work_ne hbw
  have heb := hbe.symm
  simp only [T1] at a1 e1 b1 hf ⊢
  apply WP.of_runBlock
  simp only [tail, T1, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_logic, exec_shift_d (show 27 < 64 by decide),
    exec_shift_d (show 2 < 64 by decide), exec_shift_d (show 32 < 64 by decide),
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    e1, b1, hbe, heb, hae, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial⟩
  · rw [dbl_mk, lo32_add, lo32_add, he, hf, ha, dbl_rot x 5 27 (by decide) (by decide)]
  · rw [hb, dbl_rot y 30 2 (by decide) (by decide)]

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr T0).setWidth 32 = w) (hk : (s.gpr KR).setWidth 32 = K t) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
      s'.gpr KR = s.gpr KR := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  have k4 : var t 4 ≠ KR := fun e => kr_ne.1 (e ▸ m4)
  rw [round_split, WP.block_append_iff]
  -- `e += Wₜ + Kₜ`
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq, exists_eq_left']
  generalize hs₀ : (s.write (var t 4) (s.gpr (var t 4) + s.gpr T0)).write (var t 4) _ = s₀
  have he₀ : (s₀.gpr (var t 4)).setWidth 32 = v[4] + w + K t := by
    rw [← hs₀, RegUpd.gpr_write_self, lo32_add, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (Ne.symm k4),
      lo32_add, h4, hw, hk]
  have k₀ : ∀ r, r ≠ var t 4 → s₀.gpr r = s.gpr r := fun r hr => by
    rw [← hs₀, RegUpd.gpr_write_of_ne _ _ hr, RegUpd.gpr_write_of_ne _ _ hr]
  rw [WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s₀ v[1] v[2] v[3] m1 m2 m3 (by rw [k₀ _ h14, h1, dbl_lo])
    (by rw [k₀ _ h24]; exact h2) (by rw [k₀ _ h34]; exact h3))
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s₀.gpr r := fun r hr =>
    hk₁ r (work_ne hr).2.1 (work_ne hr).2.2.1
  refine WP.mono (tail_ok (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] (v[4] + w + K t) _ m0 m1 m4 h14 h04
    (by rw [k₁ _ m0, k₀ _ h04]; exact h0) (by rw [k₁ _ m1, k₀ _ h14]; exact h1)
    (by rw [k₁ _ m4]; exact he₀) hT1)
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have hm₀ : s₀.mem = s.mem := by rw [← hs₀]; rfl
  have hrd₀ : s₀.rd = s.rd := by rw [← hs₀]; rfl
  have hwr₀ : s₀.wr = s.wr := by rw [← hs₀]; rfl
  refine ⟨?_, by rw [hm₂, hm₁, hm₀], by rw [hrd₂, hrd₁, hrd₀], by rw [hwr₂, hwr₁, hwr₀], fun r hr => ?_, ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega_using []),
      var_succ t _ (show 1 < 4 by omega_using []), var_succ t _ (show 2 < 4 by omega_using []),
      var_succ t _ (show 3 < 4 by omega_using [])]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      congr 1; ac_rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).2.1, k₁ _ m0, k₀ _ h04, h0]; rfl
    · rw [hb]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).2.1, k₁ _ m2, k₀ _ h24, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).2.1, k₁ _ m3, k₀ _ h34, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2.2.2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp.2.1, hk₁ r hp.2.1 hp.2.2,
      k₀ r (Ne.symm (hne 4))]
  · have k1 : KR ≠ var t 1 := fun e => kr_ne.1 (e ▸ m1)
    rw [hk₂ _ (Ne.symm k4) k1 kr_ne.2.2.1, hk₁ _ kr_ne.2.2.1 kr_ne.2.2.2.1, k₀ _ (Ne.symm k4)]

/-- `Kₜ` changes only every 20 rounds. -/
theorem K_succ {t : Nat} (h : (t + 1) % 20 ≠ 0) : K (t + 1) = K t := by
  unfold Spec.Sha1.K
  (repeat' split) <;> first | rfl | omega_arith

/-! ## The message schedule -/

theorem slot_lt (j : Nat) : slot j < 2048 := by
  simp only [slot]; omega_using []

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

/-- With `scratch` 8-byte aligned, the slots are naturally aligned. -/
theorem slot_al {scr : Addr} (hal : scr.toNat % 8 = 0) (j : Nat) :
    (scr + BitVec.ofNat 64 (slot j)).toNat % 4 = 0 := by
  simp only [slot]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * (j % 16)) (by omega_using [])]
  have := scr.isLt
  omega_using [hal]

/-- A load of a slot, with `scratch` (`a3`) aligned. -/
theorem exec_lw_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 4) :
    exec (.load .w t .a3 (slot j)) s =
      some (s.write t ((s.mem.readW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 32).setWidth 64)) :=
  exec_load_w (slot_lt j) (slot_al hal j) hin

/-- A store to a slot, with `scratch` (`a3`) aligned. -/
theorem exec_sw_slot {s : State} {t : Reg} {j : Nat} (hal : (s.gpr .a3).toNat % 8 = 0)
    (hout : InRegions s.wr (s.gpr .a3 + BitVec.ofNat 64 (slot j)) 4) :
    exec (.store .w t .a3 (slot j)) s =
      some { s with mem := s.mem.writeW (s.gpr .a3 + BitVec.ofNat 64 (slot j)) ((s.gpr t).setWidth 32) } :=
  exec_store_w (slot_lt j) (slot_al hal j) hout

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr1 : s.gpr .a1 = bp) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : t < 16 → beWord s.mem bp (4 * t) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr T0).setWidth 32 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha1.RISCV64.schedule, ht, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (loadBE32_ok (by decide) (by decide) (by decide) (by omega_using [ht]) (by rw [hr1]; exact hi))
      fun s₁ e => ?_
    have g3 : s₁.gpr .a3 = scr := by rw [e, ← hr3]; rfl
    have gw : s₁.wr = s.wr := by rw [e]; rfl
    have gr : s₁.rd = s.rd := by rw [e]; rfl
    have gm : s₁.mem = s.mem := by rw [e]; rfl
    have g0 : (s₁.gpr T0).setWidth 32 = W M t := by
      rw [e, RegUpd.gpr_write_self, lo32_ext, hr1, hb]
    have gk : ∀ r, r ≠ T0 → r ≠ T1 → s₁.gpr r = s.gpr r := fun r h0 h1 => by
      rw [e, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h1]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_store_w (s := s₁) (slot_lt t) (by rw [g3]; exact slot_al hal t)
        (by rw [gw, g3]; exact hout t), Option.some.injEq, exists_eq_left', g3]
    exact ⟨g0, by rw [gm, g0], gr, gw, gk⟩
  · have hw := hwin (by omega_using [ht])
    have e3 := hw (t - 3) (by omega_using [ht]) (by omega_using [])
    have e8 := hw (t - 8) (by omega_using [ht]) (by omega_using [])
    have e14 := hw (t - 14) (by omega_using [ht]) (by omega_using [])
    have e16 := hw (t - 16) (by omega_using [ht]) (by omega_using [])
    rw [show slot (t - 3) = slot (t + 13) by simp only [slot]; omega_using [ht]] at e3
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega_using [ht]] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega_using [ht]] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega_using [ht]] at e16
    simp only [Impl.Sha1.RISCV64.schedule, ht, ite_false, rotl, T0, T1, List.cons_append,
      List.nil_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic,
      exec_shift_w (show 1 < 32 by decide), exec_shift_w (show 32 - 1 < 32 by decide),
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
      ↓reduceIte, hr3, exec_lw_slot, exec_sw_slot, hal, hin, hout, Option.some.injEq,
      exists_eq_left']
    have hW := W_ge M (t := t) (by omega_using [ht])
    simp only [lo32_xor, lo32_ext, e3, e8, e14, e16, rotl_lo _ (show 1 < 32 by decide), ← hW]
    exact ⟨trivial, trivial, trivial, trivial, fun r h0 h1 => by simp only [h0, h1, ↓reduceIte]⟩

/-! ## The 80 rounds -/

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base scr (by omega_using []) (by omega_using [])

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr, slot]
  exact Offset.sep scr (by omega_using [h]) (by omega_using []) (by omega_using [])

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j
  kr : t % 20 ≠ 0 → (s.gpr KR).setWidth 32 = K t

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hr1 : sB.gpr .a1 = bp) (hr3 : sB.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → beWord m bp (4 * t) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega_using []), fun h => absurd rfl h⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    rw [List.append_assoc, WP.block_append_iff]
    have hs_r1 : s.gpr .a1 = bp := (hs.pub .a1 (by decide)).trans hr1
    have hs_r3 : s.gpr .a3 = scr := (hs.pub .a3 (by decide)).trans hr3
    refine WP.mono (schedule_ok t s M bp scr hs_r1 hs_r3 hal
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1
      simp only [Vars, e] at hv ⊢
      exact hv
    -- `Kₜ`.
    rw [WP.block_append_iff]
    refine WP.mono (Q := fun (s₂ : State) => (s₂.gpr KR).setWidth 32 = K t ∧ (∀ r, r ≠ KR → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ?_ fun s₂ ⟨kv₂, k₂, hm₂', hrd₂', hwr₂'⟩ => ?_
    · by_cases hk : t % 20 = 0
      · simp only [kload, hk, ite_true]
        exact WP.mono (li32_ok (K t)) fun s' e => by
          subst e
          exact ⟨by rw [RegUpd.gpr_write_self, lo32_sext], fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl,
            rfl⟩
      · simp only [kload, hk, ite_false]
        refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
        rw [hr₁ _ kr_ne.2.1 kr_ne.2.2.1]
        exact hs.kr hk
    have hv₂' : Vars t s₂ (VG.Spec.Sha1.rounds H M t) := by
      have e : ∀ k, s₂.gpr (var t k) = s₁.gpr (var t k) := fun k =>
        k₂ _ fun h => kr_ne.1 (h ▸ var_mem t k)
      simp only [Vars, e]
      exact hv₁
    have hT0₂ : (s₂.gpr T0).setWidth 32 = W M t := by rw [k₂ _ (Ne.symm kr_ne.2.1)]; exact hT0
    refine WP.mono (round_ok t s₂ _ _ hv₂' hT0₂ kv₂) fun s₃ ⟨hv₃, hm₃, hrd₃, hwr₃, hr₃, kr₃⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₃, hrd₂', hrd₁, hs.rd], by rw [hwr₃, hwr₂', hwr₁, hs.wr], ?_, ?_,
      fun hk => ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₃
    · have := pubRegs_ne hr
      rw [hr₃ r hr, k₂ r (fun h => kr_ne.2.2.2.2 (h ▸ hr)), hr₁ r this.1 this.2.1, hs.pub r hr]
    · rw [hm₃, hm₂', hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₃, hm₂', hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega_using [hj, hj', hjt])) (by decide)]
        exact hs.win j (by omega_using [hj, hjt]) (by omega_using [hj'])
    · rw [kr₃, kv₂, K_succ hk]

end VG.Proof.Sha1.RISCV64

end

end

/-!
# SHA-1 compression function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the SHA-256
proof (`Proof/Sha256/RISCV64/Compress.lean`), with the hash value read and
written a word at a time if `state` is a multiple of 4 (`loadA_ok`,
`updA_step`), else a byte at a time (`Proof/Framework/RISCV64/ByteLoad.lean`),
the same words either way (`loadP_ok`, `updateP_ok`), the scratch space rounded up to a multiple of 8 first
(`Proof/Framework/RISCV64/Align.lean`), and no saved register.
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.RISCV64.Align VG.Impl.Sha1.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Sha1 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)
open VG.Proof.Sha1.StateMem (readW_writeW_word stateAt_eq stateAt_get)
open VG.Proof.Sha1 (W_lt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr₀ : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev scr : Addr := scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀))
abbrev stR : Region := ⟨st s₀, 20⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr₀ s₀, 80⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

/-- An offset of the rounded scratch space, as one of `scratch`. -/
theorem scr_add (s₀ : State) (d : Nat) :
    scr s₀ + BitVec.ofNat 64 d = scr₀ s₀ + BitVec.ofNat 64 (pad (scr₀ s₀) + d) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem scr_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    (scrR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

theorem scr_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 72) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := by
  rw [scr_add]
  have := pad_lt (scr₀ s₀)
  exact Offset.sub_base _ (by omega_using [h, this])

theorem win_sub (s₀ : State) : Region.Sub (winRegion (scr s₀)) (scrR s₀) := by
  have := scr_sub s₀ (d := 0) (n := 64) (by omega_using [])
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 5) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 5) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega_using [])⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], scr_contains s₀ (by simp only [slot]; omega_using [])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by rw [BitVec.ofNat_add, BitVec.add_assoc]]
  exact Offset.contains_base _ (by omega_using [hi, ht]) (by omega_using [hi, ht, this])

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

theorem preserved_pub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a3 : s.gpr .a3 = scr s₀
  kept : ∀ r ∈ pubRegs, r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a1 : s.gpr .a1 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## Loading the MD buffer -/

theorem var0_inj {j k : Nat} (hj : j < 5) (hk : k < 5) (h : var 0 j = var 0 k) : j = k := by
  obtain key : ∀ j < 5, ∀ k < 5, var 0 j = var 0 k → j = k := by decide
  exact key j hj k hk h

theorem var0_ne {k : Nat} (hk : k < 5) : var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by
  obtain key : ∀ k < 5, var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by decide
  exact key k hk

theorem var0_pub {k : Nat} (hk : k < 5) : ∀ r ∈ pubRegs, r ≠ var 0 k := by
  obtain key : ∀ k < 5, ∀ r ∈ pubRegs, r ≠ var 0 k := by decide
  exact key k hk

/-- The first `k` words of the MD buffer are loaded. -/
structure LdI (s₁ : State) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, s.gpr (var 0 j) = ((stateAt s₁.mem (s₁.gpr .a0))[j]!).setWidth 64
  pub : ∀ r ∈ pubRegs, s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) {k : Nat} (hk : k < 5) {s : State} (h : LdI s₁ k s) :
    WP isa (.block (loadLE32 (var 0 k) T0 .a0 (4 * k))) s (LdI s₁ (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine WP.mono (loadLE32_ok ne.1 (by decide) ne.2.1 (by omega_using [hk])
    (by rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk)) fun s' e => ?_
  subst e
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (var0_inj (by omega_arith) hk e) (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (var0_ne (by omega_arith : j < 5)).2.1]
      exact h.vars j hj
    · rw [RegUpd.gpr_write_self, h.mem, h0, ← hr0, getElem!_pos _ j hk, stateAt_get _ _ hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var0_pub hk r hr),
      RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne' r hr).1 e]
    exact h.pub r hr

theorem loadW_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : WP isa (.block loadW) s (LdI s 5) :=
  wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => load_step hp hr0 hrd hwr hk h)
    5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `x + 4k` is a multiple of 4 for `x` one. -/
theorem al_of {x : Addr} (h : x &&& BitVec.ofInt 64 3 = 0) (k : Nat) :
    (x + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  obtain e : (x &&& BitVec.ofInt 64 3).toNat = x.toNat % 4 := by
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 3).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [h, show (0 : BitVec 64).toNat = 0 from rfl] at e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [e]

theorem loadA_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hal : ∀ k < 5, (st s₀ + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0)
    {k : Nat} (hk : k < 5) {s : State} (h : LdI s₁ k s) :
    WP isa (.block [.load .w (var 0 k) .a0 (4 * k)]) s (LdI s₁ (k + 1)) := by
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine VG.RISCV64.Steps.wp_lwu (off := 4 * k) (a := st s₀ + BitVec.ofNat 64 (4 * k)) (by omega_using [hk])
    (by rw [h0]) (hal k hk) (by rw [h.rd, h.wr, hrd, hwr]; exact hp.in_state hk) fun s' u => WP.block_nil ?_
  refine ⟨fun j hj => ?_, fun r hr => ?_, u.mem.trans h.mem, u.rd.trans h.rd, u.wr.trans h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [u.other _ (fun e => absurd (var0_inj (by omega_arith) hk e) (by omega_using [hj]))]
      exact h.vars j hj
    · rw [u.gpr, h.mem, ← hr0, getElem!_pos _ j hk, stateAt_get _ _ hk]
  · rw [u.other _ (var0_pub hk r hr)]
    exact h.pub r hr

theorem loadA_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hal : ∀ k < 5, (st s₀ + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0) :
    WP isa (.block loadA) s (LdI s 5) :=
  wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => loadA_step hp hr0 hrd hwr hal hk h)
    5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Doubling `a` and `b` after the words are loaded. -/
theorem dbl_ok {s₀ : State} {s s₁ : State} (hr0 : s.gpr .a0 = st s₀) (h : LdI s 5 s₁) :
    WP isa (.block dblAB) s₁ fun s₂ =>
      Vars 0 s₂ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = s.mem := by
  unfold dblAB
  have v := h.vars
  rw [hr0] at v
  have v' (k : Nat) (hk : k < 5) : s₁.gpr (var 0 k) = ((stateAt s.mem (st s₀))[k]).setWidth 64 := by
    rw [v k hk, getElem!_pos _ k hk]
  obtain n01 : var 0 0 ≠ var 0 1 := by decide
  obtain t0 : var 0 0 ≠ T1 := by decide
  obtain t1 : var 0 1 ≠ T1 := by decide
  simp only [T1] at t0 t1 ⊢
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_shift_d (show 32 < 64 by decide),
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, h.rd, h.wr, h.mem⟩
  · simp only [RegUpd.gpr_write, t0, n01, ↓reduceIte]; rw [v' 0 (by decide), dbl_ext]
  · simp only [RegUpd.gpr_write, t1, Ne.symm n01, ↓reduceIte]; rw [v' 1 (by decide), dbl_ext]
  · simp only [RegUpd.gpr_write, show var 0 2 ≠ var 0 0 by decide, show var 0 2 ≠ var 0 1 by decide,
      show var 0 2 ≠ .t6 by decide, ↓reduceIte]
    rw [v' 2 (by decide), lo32_ext]
  · simp only [RegUpd.gpr_write, show var 0 3 ≠ var 0 0 by decide, show var 0 3 ≠ var 0 1 by decide,
      show var 0 3 ≠ .t6 by decide, ↓reduceIte]
    rw [v' 3 (by decide), lo32_ext]
  · simp only [RegUpd.gpr_write, show var 0 4 ≠ var 0 0 by decide, show var 0 4 ≠ var 0 1 by decide,
      show var 0 4 ≠ .t6 by decide, ↓reduceIte]
    rw [v' 4 (by decide), lo32_ext]
  · have h0 : r ≠ var 0 0 := var0_pub (by decide) r hr
    obtain h1 : r ≠ var 0 1 := var0_pub (by decide) r hr
    obtain h6 : r ≠ .t6 := (pubRegs_ne' r hr).2.1
    simp only [RegUpd.gpr_write, h0, h1, h6, ↓reduceIte]
    exact h.pub r hr

/-- `loadP`: by words if `state` is a multiple of 4, else by bytes. -/
theorem loadP_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa loadP s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.seq (VG.RISCV64.Steps.wp_andi (by decide) fun s1 u => WP.block_nil ?_)
  obtain g0 : s1.gpr .a0 = st s₀ := by rw [u.other _ (by decide), hr0]
  -- From `s1`, which differs from `s` only in `T0`.
  obtain back : ∀ s', LdI s1 5 s' → LdI s 5 s' := fun s' h =>
    ⟨fun j hj => by rw [h.vars j hj, u.mem, u.other _ (by decide)],
      fun r hr => by rw [h.pub r hr, u.other _ (pubRegs_ne hr).1], by rw [h.mem, u.mem],
      by rw [h.rd, u.rd], by rw [h.wr, u.wr]⟩
  obtain hite : WP isa (.ite (.zero T0) (.block loadA) (.block loadW)) s1 (LdI s 5) := by
    refine WP.ite (s1.gpr T0 == 0) (by simp [eval]) (fun h => ?_) (fun _ => ?_)
    · have hz : st s₀ &&& BitVec.ofInt 64 3 = 0 := by
        rw [← hr0, ← u.gpr]; simpa using h
      exact WP.mono (loadA_ok hp g0 (by rw [u.rd, hrd]) (by rw [u.wr, hwr]) fun k _ => al_of hz k) back
    · exact WP.mono (loadW_ok hp g0 (by rw [u.rd, hrd]) (by rw [u.wr, hwr])) back
  exact WP.seq (WP.mono hite fun s₂ h₂ => dbl_ok hr0 h₂)

/-! ## Adding the MD buffer into the words -/

/-- The first `k` of five words `f` written at `p`. -/
def writeUpTo (m : Mem) (p : Addr) (f : HashValue) (k : Nat) : Mem :=
  (List.range k).foldl (fun m j => m.writeW (p + BitVec.ofNat 64 (4 * j)) f[j]!) m

theorem writeUpTo_succ (m : Mem) (p : Addr) (f : HashValue) (k : Nat) :
    writeUpTo m p f (k + 1) = (writeUpTo m p f k).writeW (p + BitVec.ofNat 64 (4 * k)) f[k]! := by
  simp [writeUpTo, List.range_succ, List.foldl_append]

theorem readW_writeUpTo (m : Mem) (p : Addr) (f : HashValue) {k j : Nat} (hk : k ≤ 5) (hj : j < 5) :
    (writeUpTo m p f k).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      if j < k then f[j]! else m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  induction k with
  | zero => simp [writeUpTo]
  | succ k ih =>
    rw [writeUpTo_succ]
    by_cases hjk : j = k
    · subst hjk; rw [Mem.readW_writeW_self32]; simp
    · rw [readW_writeW_word _ _ _ hj (by omega_using [hk]) hjk, ih (by omega_using [hk])]
      by_cases h : j < k
      · simp [h, show j < k + 1 by omega_using [h]]
      · simp [h, show ¬ j < k + 1 by omega_using [hjk, h]]

theorem frame_writeUpTo {r : Region} {m : Mem} {p : Addr} (f : HashValue) {k : Nat} (hk : k ≤ 5)
    (hc : ∀ j < 5, r.Contains (p + BitVec.ofNat 64 (4 * j)) 4) :
    Frame [r] m (writeUpTo m p f k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    rw [writeUpTo_succ]
    exact (ih (by omega_using [hk])).writeW (List.mem_singleton_self _) _ (hc k (by omega_using [hk]))

/-- The first `k` words are updated, from the state `s₂` after the
operations, whose words are `V`, and the MD buffer `H` it holds. -/
structure UInv (s₀ s₂ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j, k ≤ j → j < 5 → (s.gpr (var 0 j)).setWidth 32 = V[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₂.gpr r
  mem : s.mem = writeUpTo s₂.mem (st s₀) (Vector.zipWith (· + ·) V H) k
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr

theorem update_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!)
    {k : Nat} (hk : k < 5) {s : State} (h : UInv s₀ s₂ V H k s) :
    WP isa (.block (updateW k)) s (UInv s₀ s₂ V H (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  obtain hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk
  unfold updateW
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega_using [hk]) hin) fun s₁ e₁ => ?_
  subst e₁
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, Option.some.injEq,
    exists_eq_left']
  -- The state after the addition.
  generalize hs₂' : State.write _ _ _ = s₃
  obtain g0 : s₃.gpr .a0 = st s₀ := by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ (Ne.symm ne.1), RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), h0]
  obtain gv : (s₃.gpr (var 0 k)).setWidth 32 = V[k]! + H[k]! := by
    rw [← hs₂', RegUpd.gpr_write_self, lo32_add, RegUpd.gpr_write_of_ne _ _ ne.2.1,
      RegUpd.gpr_write_of_ne _ _ ne.2.2, h.vars k (Nat.le_refl _) hk, RegUpd.gpr_write_self, lo32_ext,
      h0, h.mem, readW_writeUpTo _ _ _ (by omega_using [hk]) hk]
    simp only [Nat.lt_irrefl, ite_false]
    rw [hH k hk]
  obtain gm : s₃.mem = s.mem := by rw [← hs₂']; rfl
  obtain gwr : s₃.wr = s.wr := by rw [← hs₂']; rfl
  obtain grd : s₃.rd = s.rd := by rw [← hs₂']; rfl
  obtain gr : ∀ r, r ≠ var 0 k → r ≠ T0 → r ≠ T1 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [← hs₂', RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2,
      RegUpd.gpr_write_of_ne _ _ h3]
  refine WP.mono (storeLE32_ok (Ne.symm ne.2.1) (by decide) (by omega_using [hk])
    (by rw [gwr, h.wr, hwr, g0]; exact hp.out_state hk)) fun s₄ e₄ => ?_
  subst e₄
  refine ⟨fun j hj hj' => ?_, fun r hr => ?_, ?_, grd.trans h.rd, gwr.trans h.wr⟩
  · have hne : var 0 j ≠ var 0 k := fun e => absurd (var0_inj hj' hk e) (by omega_using [hj])
    rw [RegUpd.gpr_write_of_ne _ _ (var0_ne hj').2.1]
    show (s₃.gpr (var 0 j)).setWidth 32 = _
    rw [gr _ hne (var0_ne hj').2.1 (var0_ne hj').2.2]
    exact h.vars j (by omega_using [hj]) hj'
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => (pubRegs_ne' r hr).1 e]
    show s₃.gpr r = _
    rw [gr r (var0_pub hk r hr) (fun e => (pubRegs_ne' r hr).1 e) (fun e => (pubRegs_ne' r hr).2.1 e)]
    exact h.pub r hr
  · rw [RegUpd.mem_write]
    show s₃.mem.writeW _ _ = _
    rw [gm, h.mem, writeUpTo_succ, g0, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]

theorem vars_get {s : State} {V : HashValue} (h : Vars 0 s V) :
    ∀ j, j < 5 → (s.gpr (var 0 j)).setWidth 32 = V[j]! := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  intro j hj
  rw [getElem!_pos V j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega_using [hj]) with rfl | rfl | rfl | rfl | rfl
  exacts [by rw [h0, dbl_lo], by rw [h1, dbl_lo], h2, h3, h4]

theorem update_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!) :
    WP isa (.block ((List.range 5).flatMap updateW)) s₂ (UInv s₀ s₂ V H 5) :=
  wp_range_flatMap (M := isa) (UInv s₀ s₂ V H) (fun _ _ hk h => update_step hp V H hr0 hrd hwr hH hk h)
    5 (Nat.le_refl _) s₂ ⟨fun j _ hj => vars_get hv j hj, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem updA_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hal : ∀ k < 5, (st s₀ + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!)
    {k : Nat} (hk : k < 5) {s : State} (h : UInv s₀ s₂ V H k s) :
    WP isa (.block (updA k)) s (UInv s₀ s₂ V H (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  unfold updA
  refine VG.RISCV64.Steps.wp_lwu (off := 4 * k) (a := st s₀ + BitVec.ofNat 64 (4 * k)) (by omega_using [hk])
    (by rw [h0]) (hal k hk) (by rw [h.rd, h.wr, hrd, hwr]; exact hp.in_state hk) fun s1 u1 => ?_
  refine VG.RISCV64.Steps.wp_add fun s3 u3 => ?_
  obtain g0 : s3.gpr .a0 = st s₀ := by rw [u3.other _ (Ne.symm ne.1), u1.other _ (by decide), h0]
  obtain gv : (s3.gpr (var 0 k)).setWidth 32 = V[k]! + H[k]! := by
    rw [u3.gpr, lo32_add, u1.other _ ne.2.1, u1.gpr, lo32_ext, h.vars k (Nat.le_refl _) hk, h.mem,
      readW_writeUpTo _ _ _ (by omega_using [hk]) hk]
    simp only [Nat.lt_irrefl, ite_false]
    rw [hH k hk]
  refine VG.RISCV64.Steps.wp_sw (off := 4 * k) (a := st s₀ + BitVec.ofNat 64 (4 * k)) (by omega_using [hk])
    (by rw [g0]) (hal k hk) (by rw [u3.wr, u1.wr, h.wr, hwr]; exact hp.out_state hk)
    fun s4 m4 => WP.block_nil ?_
  obtain gr : ∀ r, r ≠ var 0 k → r ≠ T0 → s4.gpr r = s.gpr r := fun r h1 h2 => by
    rw [m4.gpr, u3.other _ h1, u1.other _ h2]
  refine ⟨fun j hj hj' => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hne : var 0 j ≠ var 0 k := fun e => absurd (var0_inj hj' hk e) (by omega_using [hj])
    rw [gr _ hne (var0_ne hj').2.1]
    exact h.vars j (by omega_using [hj]) hj'
  · rw [gr r (var0_pub hk r hr) (pubRegs_ne hr).1]
    exact h.pub r hr
  · rw [m4.mem, u3.mem, u1.mem, h.mem, writeUpTo_succ, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]
  · rw [m4.rd, u3.rd, u1.rd, h.rd]
  · rw [m4.wr, u3.wr, u1.wr, h.wr]

/-- `updateP`: by words if `state` is a multiple of 4, else by bytes. -/
theorem updateP_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 5, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!) :
    WP isa updateP s₂ (UInv s₀ s₂ V H 5) := by
  refine WP.seq (VG.RISCV64.Steps.wp_andi (by decide) fun s1 u => WP.block_nil ?_)
  obtain g0 : s1.gpr .a0 = st s₀ := by rw [u.other _ (by decide), hr0]
  obtain hv1 : Vars 0 s1 V := by
    obtain e : ∀ j < 5, s1.gpr (var 0 j) = s₂.gpr (var 0 j) := fun j hj => u.other _ (var0_ne hj).2.2
    obtain ⟨v0, v1, v2, v3, v4⟩ := hv
    exact ⟨(e 0 (by decide)) ▸ v0, (e 1 (by decide)) ▸ v1, (e 2 (by decide)) ▸ v2,
      (e 3 (by decide)) ▸ v3, (e 4 (by decide)) ▸ v4⟩
  obtain hH1 : ∀ j < 5, s1.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]! := by
    rw [u.mem]; exact hH
  -- From `s1`, which differs from `s₂` only in `T1`.
  obtain back : ∀ s', UInv s₀ s1 V H 5 s' → UInv s₀ s₂ V H 5 s' := fun s' h =>
    ⟨h.vars, fun r hr => by rw [h.pub r hr, u.other _ (pubRegs_ne hr).2.1],
      by rw [h.mem, u.mem], by rw [h.rd, u.rd], by rw [h.wr, u.wr]⟩
  refine WP.ite (s1.gpr T1 == 0) (by simp [eval]) (fun h => ?_) (fun _ => ?_)
  · have hz : st s₀ &&& BitVec.ofInt 64 3 = 0 := by
      rw [← hr0, ← u.gpr]; simpa using h
    exact WP.mono (wp_range_flatMap (M := isa) (UInv s₀ s1 V H)
      (fun _ _ hk h => updA_step hp V H g0 (by rw [u.rd, hrd]) (by rw [u.wr, hwr])
        (fun k _ => al_of hz k) hH1 hk h)
      5 (Nat.le_refl _) s1 ⟨fun j _ hj => vars_get hv1 j hj, fun _ _ => rfl, rfl, rfl, rfl⟩) back
  · exact WP.mono (update_ok hp V H hv1 g0 (by rw [u.rd, hrd]) (by rw [u.wr, hwr]) hH1) back

/-! ## One block -/

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    beWord s₀.mem (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
  rw [W_lt _ ht]; rfl

theorem frame_byte {rs : List Region} {m m' : Mem} {R : Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, R.Disjoint r) (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

theorem frame_beWord {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  obtain h0 := contains_byte hc (k := 0) (by decide)
  rw [Nat.add_zero] at h0
  simp only [beWord, frame_byte hf hd h0, frame_byte hf hd (contains_byte hc (k := 1) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 2) (by decide)),
    frame_byte hf hd (contains_byte hc (k := 3) (by decide))]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (loadP_ok hp hL.a0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  obtain hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  obtain hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      beWord m (blkAddr s₀ i) (4 * t) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [frame_beWord hm hwin (hp.blk_contains hi ht), hm₁,
      frame_beWord hL.frame (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (hp.blk_contains hi ht)]
    exact blk_word i t ht
  obtain hr1₁ : s₁.gpr .a1 = blkAddr s₀ i := (hpub₁ .a1 (by decide)).trans hL.a1
  obtain hr3₁ : s₁.gpr .a3 = scr s₀ := (hpub₁ .a3 (by decide)).trans hL.a3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hr1₁ hr3₁ (align_al _)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  obtain hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  obtain pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  obtain hr0₂ : s₂.gpr .a0 = st s₀ := by rw [pub₂ .a0 (by decide), hL.a0]
  obtain hrd₂ : s₂.rd = s₀.rd := by rw [hR.rd, hrd₁, hL.rd]
  obtain hwr₂ : s₂.wr = s₀.wr := by rw [hR.wr, hwr₁, hL.wr]
  refine WP.seq (WP.mono (updateP_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr0₂ hrd₂ hwr₂ fun k hk => ?_)
    fun s₃ h₃ => ?_)
  · rw [hR.frame.readW (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])) hst (by decide), hm₁,
      getElem!_pos _ k hk, stateAt_get _ _ hk]
  obtain hr1₃ : s₃.gpr .a1 = blkAddr s₀ i := by rw [h₃.pub .a1 (by decide), pub₂ .a1 (by decide), hL.a1]
  obtain hr2₃ : s₃.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i) := by
    rw [h₃.pub .a2 (by decide), pub₂ .a2 (by decide), hL.a2]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [h₃.mem]
    exact (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])).mono fun r hr => by simp at hr; simp [hr]
  obtain hstate : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hL.state]
    apply stateAt_eq
    intro k hk
    rw [h₃.mem, readW_writeUpTo _ _ _ (Nat.le_refl _) hk]
    simp only [hk, ↓reduceIte]
    rw [getElem!_pos _ k hk]
    rfl
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 64 by decide),
    exec_addi (show imm12 (-1) by decide), Option.some.injEq, exists_eq_left']
  -- The state after advancing.
  generalize hs₄ : State.write _ _ _ = s₄
  obtain g1 : s₄.gpr .a1 = blkAddr s₀ (i + 1) := by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self, hr1₃]
    simp only [blkAddr]
    rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.mul_succ]
  have hnb := hp.nb_lt
  obtain g2 : s₄.gpr .a2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [← hs₄, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide), hr2₃]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 from rfl]
    omega_using [hi]
  obtain gr : ∀ r, r ≠ .a1 → r ≠ .a2 → s₄.gpr r = s₃.gpr r := fun r h1 h2 => by
    rw [← hs₄, RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h1]
  obtain gm : s₄.mem = s₃.mem := by rw [← hs₄]; rfl
  obtain grd : s₄.rd = s₃.rd := by rw [← hs₄]; rfl
  obtain gwr : s₄.wr = s₃.wr := by rw [← hs₄]; rfl
  obtain hcommon : Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [gr _ (by decide) (by decide), h₃.pub .a0 (by decide), hr0₂],
      by rw [gr _ (by decide) (by decide), h₃.pub .a3 (by decide), pub₂ .a3 (by decide), hL.a3],
      fun r hr h1 h2 h3 => ?_, by rw [grd, h₃.rd, hrd₂], by rw [gwr, h₃.wr, hwr₂],
      by rw [gm]; exact hframe, by rw [gm]; exact hstate⟩
    rw [gr r h1 h2, h₃.pub r hr, pub₂ r hr, hL.kept r hr h1 h2 h3]
  obtain hev : eval (.nonzero .a2) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, g2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    obtain hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    obtain h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hnb])] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], { hcommon with a1 := g1, a2 := g2 }⟩

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr1 : s₁.gpr .a1 = bp s₀) (hr2 : s₁.gpr .a2 = s₀.gpr .a2) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .a2 == 0) (by simp [eval]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr2] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr2] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .a2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
    obtain hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        a1 := by simp [blkAddr, hr1]
        a2 := by simp [nb, hr2] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.Sha1.compressRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .a3 = scr s₀ ∧ (∀ r, r ≠ .a3 → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ?_ fun s₁ ⟨h3, hg, hm, hrd, hwr⟩ => ?_)
  · apply WP.of_runBlock
    simp only [align, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
      exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, align_eq, RegUpd.write_write,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩
  obtain hc₀ : Common s₀ 0 s₁ := ⟨by rw [hg _ (by decide)], h3, fun r _ _ _ h => hg r h, hrd, hwr,
    by rw [hm]; exact Frame.refl _ _, by rw [hm]; rfl⟩
  refine WP.mono (blocks_ok hp hc₀ (hg _ (by decide)) (hg _ (by decide))) fun s' hc =>
    ⟨fun r hr => hc.kept r (preserved_pub r hr) (by revert r; decide) (by revert r; decide)
      (by revert r; decide), hc.kept _ (by decide) (by decide) (by decide) (by decide), hc.state⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 80⟩]

/-! The constant-time analysis of the compression function from its arguments, done once for
every check of code that calls it (`taint_decide_sum [compressSum]`), which keeps what is public
of `s1`–`s11`: it writes none of them. -/
taint_summary compressSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) Impl.Sha1.RISCV64.compress
  keeping (Taint.ofRegs [.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

theorem compress_verified :
    Verified RISCV64.target Impl.Sha1.RISCV64.compress Proof.Sha1.compressRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · refine VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_
      (VG.Taint.exists_check_of_sumOk compressSum (RegSet.subset_refl _))
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4]
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.RISCV64
