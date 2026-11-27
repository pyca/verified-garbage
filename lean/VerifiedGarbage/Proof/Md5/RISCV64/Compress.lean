module

public import VerifiedGarbage.Proof.Md5.StateMem
public meta import VerifiedGarbage.Proof.Md5.StateMem
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
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Semantics
public meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Md5.Spec
public import VerifiedGarbage.Impl.Md5.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Md5.Spec
meta import VerifiedGarbage.Impl.Md5.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.Md5
meta import VerifiedGarbage.TCB.Artifact

/-! ### `Md5.RISCV64.Contract`, which only this module used -/

section

/-!
# MD5: the RISC-V contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply them
(`Contract.Implies`). The return address is in `ra`, which the target's
calling convention requires to be preserved (`VG.RISCV64.abiPreserved`),
not on the stack. `update` and `finalize` keep their working space in a
frame of 144 bytes below the stack pointer, which must not overlap their
buffers.
-/

@[expose] public section

namespace VG.Proof.Md5

open Spec.Md5

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`:
updates the MD buffer at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(16 bytes) and `scratch` (64 bytes, 8-byte aligned, whose contents on exit
are unspecified). These may not overlap each other. The pointers and `n` are public; the MD
buffer and the blocks are secret. -/
def compressRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 16⟩
    let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 64⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    stateAt s'.mem (s.gpr .a0) =
      compressBlocks (stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for `vg_md5_init(state: *mut [u8; 80])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (80 bytes). The pointer is public. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 80⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize)`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (80
bytes). These may not overlap each other, nor the 144 bytes below the stack
pointer (its frame), which do not wrap around. The stack pointer is 16-byte
aligned. The pointers, `count` and `len` are public; the state and the data
are secret. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 80⟩
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
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16])`: if
the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the MD5 digest of `m` to `out`.

The code may read and write `state` (80 bytes, whose contents on exit are
unspecified) and `out` (16 bytes). These may not overlap each other, nor the
144 bytes below the stack pointer (its frame), which do not wrap around.
The stack pointer is 16-byte aligned. The pointers and `count` are public;
the state is secret. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 80⟩
    let out : Region := ⟨s.gpr .a2, 16⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .a2) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Md5

end

end

/-! ### `Md5.RISCV64.Steps`, which only this module used -/

section

/-!
# MD5 compression function on RISC-V: the 64 operations

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Md5/PPC64LE/Compress.lean`): each operation is the auxiliary
function of its round, symbolically executed once per round (`fn_ok`),
between the load of `X[k]` from `scratch` and the additions before it (`head_ok`) and the rotation and
addition after it (`tail_ok`), each symbolically executed once for all
operations. The words are the low 32 bits of the registers (`Vars`).
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Md5.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the low 32 bits of the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3]

/-- The pointers, the count, the return address and the callee-saved
registers: never written by the operations. -/
def pubRegs : List Reg := [.a0, .a1, .a2, .a3, .ra, .s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8,
  .s9, .s10, .s11]

/-- The words move one register along each operation. -/
theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega_using []

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 4 - t % 4) % 4]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ .a1 ∧ ∀ p ∈ pubRegs, r ≠ p := by
  decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne' _ (var_mem t k)).1

theorem var_ne_T1 (t k : Nat) : var t k ≠ T1 := (work_ne' _ (var_mem t k)).2.1

theorem var_ne_T2 (t k : Nat) : var t k ≠ T2 := (work_ne' _ (var_mem t k)).2.2.1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne' _ (var_mem t k)).2.2.2.2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .t0 ≠ work.getD ((j + 4 - c) % 4) .t0 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega_using [])) i hi j hj h

theorem pub_ne' : ∀ p ∈ pubRegs, p ≠ T0 ∧ p ≠ T1 ∧ p ≠ T2 := by decide

/-! ## The auxiliary functions -/

/-- The low word of `-1`. -/
theorem lo_m1 : (BitVec.ofInt 64 (-1)).setWidth 32 = 0xffffffff := by decide

theorem fn_ok (r : Nat) (hr : r < 4) (a b c d : Reg) (ha : a ≠ T0) (hb : b ≠ T0) (hc : c ≠ T0)
    (hd : d ≠ T0) (hab : a ≠ b) (had : a ≠ d)
    (s : State) (va vb vc vd : Word) (h₀ : (s.gpr a).setWidth 32 = va) (h₁ : (s.gpr b).setWidth 32 = vb)
    (h₂ : (s.gpr c).setWidth 32 = vc) (h₃ : (s.gpr d).setWidth 32 = vd) :
    WP isa (.block (fn r a b c d)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + roundFn r vb vc vd ∧
      (∀ x, x ≠ a → x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  have hda : d ≠ a := fun h => had h.symm
  apply WP.of_runBlock
  rcases (by omega_using [hr] : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp only [fn, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add,
    exec_logicImm (show imm12 (-1) by decide), RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, ha, hb, hc, hd, hba, hda, ↓reduceIte, Option.some.injEq,
    exists_eq_left'] <;>
  refine ⟨?_, fun x hx hx' => by simp [hx, hx'], trivial, trivial, trivial⟩ <;>
  simp only [lo32_add, lo32_xor, lo32_and, lo32_or, lo_m1, h₀, h₁, h₂, h₃]
  · rw [show roundFn 0 = F from rfl, Proof.Md5.F_eq]
  · rw [show roundFn 1 = G from rfl, Proof.Md5.G_add, BitVec.add_assoc]
  · rw [show roundFn 2 = H from rfl, Proof.Md5.H_eq']
  · rw [show roundFn 3 = I from rfl, Proof.Md5.I_eq]

/-! ## The rest of an operation -/

/-- The instructions of an operation before the auxiliary function. -/
def headI (a : Reg) (k : Nat) (T : Word) : List Instr :=
  .load .w T1 .a3 (4 * k) :: .add a a T1 :: (li32 T1 T ++ [.add a a T1])

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (n : Nat) : List Instr :=
  [.shift .sll .w T0 a n, .shift .srl .w a a (32 - n), .logic .or a a T0, .add a a b]

theorem step_split (t : Nat) :
    step t = headI (var t 0) (ks.getD t 0) (Ts.getD t 0) ++
      (fn (t / 16) (var t 0) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (Proof.Md5.rot t)) := by
  simp only [step, headI, tailI, List.append_assoc, List.cons_append]; rfl

/-- With `scratch` 8-byte aligned, its words are naturally aligned. -/
theorem word_al {scr : Addr} (hal : scr.toNat % 8 = 0) {k : Nat} (hk : k < 16) :
    (scr + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * k) (by omega_using [hk])]
  have := scr.isLt
  omega_using [hal]

theorem head_ok (a : Reg) (k : Nat) (hk : k < 16) (T : Word) (ha₁ : a ≠ T1)
    (s : State) (va x : Word) (scr : Addr) (h₁ : (s.gpr a).setWidth 32 = va)
    (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 (4 * k)) 4)
    (hx : s.mem.readW (scr + BitVec.ofNat 64 (4 * k)) 32 = x) :
    WP isa (.block (headI a k T)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + x + T ∧
      (∀ r, r ≠ a → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [headI, li32, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_load_w (s := s) (show 4 * k < 2048 by omega_using [hk]) (by rw [hr3]; exact word_al hal hk)
      (by rw [hr3]; exact hin), exec_add, exec_lui, exec_addiw_lo12, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, ha₁, ↓reduceIte, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr hr' _ => by simp [hr, hr'], trivial, trivial, trivial⟩
  simp only [lo32_add, lo32_ext, lo32_sext, li32_val, h₁, hx, hr3]

theorem tail_ok (a b : Reg) (n : Nat) (hn0 : 0 < n) (hn : n < 32) (hab : a ≠ b) (ha : a ≠ T0) (hb : b ≠ T0)
    (s : State) (va vb : Word) (h₁ : (s.gpr a).setWidth 32 = va) (h₂ : (s.gpr b).setWidth 32 = vb) :
    WP isa (.block (tailI a b n)) s fun s' =>
      (s'.gpr a).setWidth 32 = va.rotateLeft n + vb ∧
      (∀ r, r ≠ a → r ≠ T0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  have hTa : T0 ≠ a := fun h => ha h.symm
  apply WP.of_runBlock
  simp only [tailI, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    exec_shift_w hn, exec_shift_w (show 32 - n < 32 by omega_using [hn0]), RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, ha, hb, hba, hTa, ↓reduceIte, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr hr' => by simp [hr, hr'], trivial, trivial, trivial⟩
  simp only [lo32_add, lo32_or, lo32_sext, h₁, h₂]
  rw [BitVec.or_comm, rotl_shifts _ hn]

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (scr : Addr)
    (hv : Vars t s v) (hr3 : s.gpr .a3 = scr) (hal : scr.toNat % 8 = 0)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (scr + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := Proof.Md5.ks_lt t ht
  have hr := Proof.Md5.rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (head_ok (var t 0) (ks.getD t 0) hk (Ts.getD t 0) (var_ne_T1 t 0)
    s v[0] (X ⟨ks.getD t 0, hk⟩) scr h0 hr3 hal (hin _ hk) (hX _ hk)) fun s₁ ⟨a₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, 0 < k → k < 4 → s₁.gpr (var t k) = s.gpr (var t k) := fun k h0 h4 =>
    e₁ _ (var_ne t h4 (by omega_using []) (by omega_using [h0])) (var_ne_T1 t k) (var_ne_T2 t k)
  rw [WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega_using [ht]) (var t 0) (var t 1) (var t 2) (var t 3) (var_ne_T0 t 0)
    (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) (var_ne t (by omega_using []) (by omega_using []) (by omega_using []))
    (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])) s₁
    _ v[1] v[2] v[3] a₁ (by rw [e 1 (by omega_using []) (by omega_using [])]; exact h1)
    (by rw [e 2 (by omega_using []) (by omega_using [])]; exact h2) (by rw [e 3 (by omega_using []) (by omega_using [])]; exact h3))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (tail_ok (var t 0) (var t 1) (Proof.Md5.rot t) (by omega_using [hr]) (by omega_using [hr])
    (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])) (var_ne_T0 t 0) (var_ne_T0 t 1) s₂ _ v[1] a₂
    (by rw [e₂ _ (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])).symm (var_ne_T0 t 1),
      e 1 (by omega_using []) (by omega_using [])]; exact h1)) fun s₃ ⟨a₃, e₃, m₃, rd₃, wr₃⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → r ≠ T1 → r ≠ T2 → s₃.gpr r = s.gpr r :=
    fun r h h' h'' h''' => by rw [e₃ r h h', e₂ r h h', e₁ r h h'' h''']
  refine ⟨?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (pub_ne' r hr).1 (pub_ne' r hr).2.1 (pub_ne' r hr).2.2⟩
  rw [Proof.Md5.step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega_using []),
    var_succ t _ (show 1 < 3 by omega_using []), var_succ t _ (show 2 < 3 by omega_using []), Proof.Md5.stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])) (var_ne_T0 t 3) (var_ne_T1 t 3)
      (var_ne_T2 t 3), h3]
  · rw [a₃, BitVec.add_comm _ (v[1]), Proof.Md5.add_fn]
  · rw [g _ (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])) (var_ne_T0 t 1) (var_ne_T1 t 1)
      (var_ne_T2 t 1), h1]
  · rw [g _ (var_ne t (by omega_using []) (by omega_using []) (by omega_using [])) (var_ne_T0 t 2) (var_ne_T1 t 2)
      (var_ne_T2 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (scr : Addr) (sB : State) (hr3 : sB.gpr .a3 = scr)
    (hal : scr.toNat % 8 = 0)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (scr + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (scr + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega_using [ht])) fun s hs => ?_)
    have hs_r3 : s.gpr .a3 = scr := (hs.pub .a3 (by decide)).trans hr3
    refine WP.mono (step_ok t (by omega_using [ht]) s _ X scr hs.vars hs_r3 hal
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.RISCV64

end

end

/-!
# MD5 compression function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the SHA-256
proof (`Proof/Sha256/RISCV64/Compress.lean`), with the MD buffer read and
written a byte at a time (`Proof/Framework/RISCV64/ByteLoad.lean`), the
block's words decoded once into `scratch` (`decode_ok`) and no saved
register.
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Md5.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)
open VG.Proof.Md5.StateMem (readW_writeW_word stateAt_eq stateAt_get)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev bp : Addr := s₀.gpr .a1
abbrev nb : Nat := (s₀.gpr .a2).toNat
abbrev scr : Addr := s₀.gpr .a3
abbrev stR : Region := ⟨st s₀, 16⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 64⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  al : (scr s₀).toNat % 8 = 0

theorem pre_of (s₀ : State) (h : Proof.Md5.compressRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [hn]

theorem in_state {k : Nat} (hk : k < 4) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_state {k : Nat} (hk : k < 4) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_scr {k : Nat} (hk : k < 16) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨scrR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_scr {k : Nat} (hk : k < 16) :
    InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨scrR s₀, by simp [h.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
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
  kept : ∀ r ∈ pubRegs, r ≠ .a1 → r ≠ .a2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  a1 : s.gpr .a1 = blkAddr s₀ i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## Loading the MD buffer -/

theorem var0_inj {j k : Nat} (hj : j < 4) (hk : k < 4) (h : var 0 j = var 0 k) : j = k := by
  obtain key : ∀ j < 4, ∀ k < 4, var 0 j = var 0 k → j = k := by decide
  exact key j hj k hk h

theorem var0_ne {k : Nat} (hk : k < 4) : var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by
  obtain key : ∀ k < 4, var 0 k ≠ .a0 ∧ var 0 k ≠ T0 ∧ var 0 k ≠ T1 := by decide
  exact key k hk

theorem var0_pub {k : Nat} (hk : k < 4) : ∀ r ∈ pubRegs, r ≠ var 0 k := by
  obtain key : ∀ k < 4, ∀ r ∈ pubRegs, r ≠ var 0 k := by decide
  exact key k hk

/-- The first `k` words of the MD buffer are loaded. -/
structure LdI (s₁ : State) (k : Nat) (s : State) : Prop where
  vars : ∀ j < k, (s.gpr (var 0 j)).setWidth 32 = (stateAt s₁.mem (s₁.gpr .a0))[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hr0 : s₁.gpr .a0 = st s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) {k : Nat} (hk : k < 4) {s : State} (h : LdI s₁ k s) :
    WP isa (.block (loadLE32 (var 0 k) T0 .a0 (4 * k))) s (LdI s₁ (k + 1)) := by
  obtain ne := var0_ne hk
  obtain h0 : s.gpr .a0 = st s₀ := (h.pub .a0 (by decide)).trans hr0
  refine WP.mono (loadLE32_ok ne.1 (by decide) ne.2.1 (by omega_using [hk])
    (by rw [h.rd, h.wr, hrd, hwr, h0]; exact hp.in_state hk)) fun s' e => ?_
  subst e
  refine ⟨fun j hj => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (var0_inj (by omega_arith) hk e) (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (var0_ne (by omega_arith : j < 4)).2.1]
      exact h.vars j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, h.mem, h0, ← hr0, getElem!_pos _ j hk,
        stateAt_get _ _ hk]
  · rw [RegUpd.gpr_write_of_ne _ _ (var0_pub hk r hr),
      RegUpd.gpr_write_of_ne _ _ fun e => (pub_ne' r hr).1 e]
    exact h.pub r hr

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .a0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  refine WP.mono (wp_range_flatMap (M := isa) (LdI s) (fun k s' hk h => load_step hp hr0 hrd hwr hk h)
    4 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl⟩)
    fun s₁ h => ⟨?_, h.pub, h.rd, h.wr, h.mem⟩
  have v := h.vars
  rw [hr0] at v
  exact ⟨v 0 (by decide), v 1 (by decide), v 2 (by decide), v 3 (by decide)⟩

/-! ## Adding the MD buffer into the words -/

/-- The first `k` of four words `f` written at `p`. -/
def writeUpTo (m : Mem) (p : Addr) (f : HashValue) (k : Nat) : Mem :=
  (List.range k).foldl (fun m j => m.writeW (p + BitVec.ofNat 64 (4 * j)) f[j]!) m

theorem writeUpTo_succ (m : Mem) (p : Addr) (f : HashValue) (k : Nat) :
    writeUpTo m p f (k + 1) = (writeUpTo m p f k).writeW (p + BitVec.ofNat 64 (4 * k)) f[k]! := by
  simp [writeUpTo, List.range_succ, List.foldl_append]

theorem readW_writeUpTo (m : Mem) (p : Addr) (f : HashValue) {k j : Nat} (hk : k ≤ 4) (hj : j < 4) :
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

theorem frame_writeUpTo {r : Region} {m : Mem} {p : Addr} (f : HashValue) {k : Nat} (hk : k ≤ 4)
    (hc : ∀ j < 4, r.Contains (p + BitVec.ofNat 64 (4 * j)) 4) :
    Frame [r] m (writeUpTo m p f k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    rw [writeUpTo_succ]
    exact (ih (by omega_using [hk])).writeW (List.mem_singleton_self _) _ (hc k (by omega_using [hk]))

/-- The first `k` words are updated, from the state `s₂` after the
operations, whose words are `V`, and the MD buffer `H` it holds. -/
structure UInv (s₀ s₂ : State) (V H : HashValue) (k : Nat) (s : State) : Prop where
  vars : ∀ j, k ≤ j → j < 4 → (s.gpr (var 0 j)).setWidth 32 = V[j]!
  pub : ∀ r ∈ pubRegs, s.gpr r = s₂.gpr r
  mem : s.mem = writeUpTo s₂.mem (st s₀) (Vector.zipWith (· + ·) V H) k
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr

theorem update_step {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hr0 : s₂.gpr .a0 = st s₀)
    (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 4, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!)
    {k : Nat} (hk : k < 4) {s : State} (h : UInv s₀ s₂ V H k s) :
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
  · rw [RegUpd.gpr_write_of_ne _ _ fun e => (pub_ne' r hr).1 e]
    show s₃.gpr r = _
    rw [gr r (var0_pub hk r hr) (fun e => (pub_ne' r hr).1 e) (fun e => (pub_ne' r hr).2.1 e)]
    exact h.pub r hr
  · rw [RegUpd.mem_write]
    show s₃.mem.writeW _ _ = _
    rw [gm, h.mem, writeUpTo_succ, g0, gv]
    congr 1
    rw [getElem!_pos (Vector.zipWith _ V H) k hk, Vector.getElem_zipWith, getElem!_pos V k hk,
      getElem!_pos H k hk]

theorem vars_get {s : State} {V : HashValue} (h : Vars 0 s V) :
    ∀ j, j < 4 → (s.gpr (var 0 j)).setWidth 32 = V[j]! := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro j hj
  rw [getElem!_pos V j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj]) with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem update_ok {s₀ s₂ : State} (hp : Pre s₀) (V H : HashValue) (hv : Vars 0 s₂ V)
    (hr0 : s₂.gpr .a0 = st s₀) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr)
    (hH : ∀ j < 4, s₂.mem.readW (st s₀ + BitVec.ofNat 64 (4 * j)) 32 = H[j]!) :
    WP isa (.block ((List.range 4).flatMap updateW)) s₂ (UInv s₀ s₂ V H 4) :=
  wp_range_flatMap (M := isa) (UInv s₀ s₂ V H) (fun _ _ hk h => update_step hp V H hr0 hrd hwr hH hk h)
    4 (Nat.le_refl _) s₂ ⟨fun j _ hj => vars_get hv j hj, fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## Decoding the block into `scratch` -/

/-- The first `k` words of block `i` are in `scratch`, from the state `s₁`
after loading the MD buffer. -/
structure DcI (s₀ s₁ : State) (i k : Nat) (s : State) : Prop where
  words : ∀ j (hj : j < 16), j < k → s.mem.readW (scr s₀ + BitVec.ofNat 64 (4 * j)) 32 = blk s₀ i ⟨j, hj⟩
  regs : ∀ r, r ≠ T1 → r ≠ T2 → s.gpr r = s₁.gpr r
  frame : Frame [scrR s₀] s₁.mem s.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem decode_step {s₀ s₁ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀)
    (hr1 : s₁.gpr .a1 = blkAddr s₀ i) (hr3 : s₁.gpr .a3 = scr s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr)
    (hX : ∀ k (hk : k < 16), s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩)
    {k : Nat} (hk : k < 16) {s : State} (h : DcI s₀ s₁ i k s) :
    WP isa (.block (loadLE32 T1 T2 .a1 (4 * k) ++ ([.store .w T1 .a3 (4 * k)] : List Instr))) s (DcI s₀ s₁ i (k + 1)) := by
  obtain h1 : s.gpr .a1 = blkAddr s₀ i := (h.regs .a1 (by decide) (by decide)).trans hr1
  obtain h3 : s.gpr .a3 = scr s₀ := (h.regs .a3 (by decide) (by decide)).trans hr3
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega_using [hk])
    (by rw [h.rd, h.wr, hrd, hwr, h1]; exact hp.in_blk hi hk)) fun s' e => ?_
  obtain g1 : s'.gpr T1 = (s.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32).setWidth 64 := by
    rw [e, RegUpd.gpr_write_self, h1]
  obtain gr : ∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := fun r h1 h2 => by
    rw [e, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  obtain gm : s'.mem = s.mem := by rw [e]; rfl
  obtain grd : s'.rd = s.rd := by rw [e]; rfl
  obtain gwr : s'.wr = s.wr := by rw [e]; rfl
  obtain g3 : s'.gpr .a3 = scr s₀ := (gr .a3 (by decide) (by decide)).trans h3
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_w (s := s') (show 4 * k < 2048 by omega_using [hk]) (by rw [g3]; exact word_al hp.al hk)
      (by rw [gwr, h.wr, hwr, g3]; exact hp.out_scr hk), Option.some.injEq, exists_eq_left', g3, g1,
    gm, lo32_ext]
  obtain hb : s.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
    rw [h.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_scr) (by decide)]
    exact hX k hk
  refine ⟨fun j hj hjk => ?_, fun r h1 h2 => by rw [← h.regs r h1 h2]; exact gr r h1 h2,
    h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])),
    grd.trans h.rd, gwr.trans h.wr⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hjk]) (by omega_using [hj]) (by omega_using [hk])) (by decide)]
    exact h.words j hj hjk
  · rw [Mem.readW_writeW_self32, hb]

theorem decode_ok {s₀ s₁ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀)
    (hr1 : s₁.gpr .a1 = blkAddr s₀ i) (hr3 : s₁.gpr .a3 = scr s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr)
    (hX : ∀ k (hk : k < 16), s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩) :
    WP isa (.block decode) s₁ (DcI s₀ s₁ i 16) :=
  wp_range_flatMap (M := isa) (DcI s₀ s₁ i)
    (fun _ _ hk h => decode_step hp hi hr1 hr3 hrd hwr hX hk h) 16 (Nat.le_refl _) s₁
    ⟨fun _ _ h => absurd h (by omega_using []), fun _ _ _ => rfl, Frame.refl _ _, rfl, rfl⟩

/-! ## One block -/

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i k : Nat) (hk : k < 16) :
    s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
  rw [Proof.Md5.readW_bytes]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.reduceAdd]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .a2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .a2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_ok hp hL.a0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_
  obtain hX : ∀ k (hk : k < 16),
      s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hm₁, hL.frame.readW (hp.blk_contains hi hk) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩)
      (by decide)]
    exact blk_word i k hk
  obtain hr1₁ : s₁.gpr .a1 = blkAddr s₀ i := (hpub₁ .a1 (by decide)).trans hL.a1
  obtain hr3₁ : s₁.gpr .a3 = scr s₀ := by
    rw [hpub₁ .a3 (by decide), hL.kept .a3 (by decide) (by decide) (by decide)]
  refine WP.mono (decode_ok hp hi hr1₁ hr3₁ (hrd₁.trans hL.rd) (hwr₁.trans hL.wr) hX)
    fun s₁' hD => ?_
  obtain hpub₁' : ∀ r ∈ pubRegs, s₁'.gpr r = s₁.gpr r := fun r hr =>
    hD.regs r (fun e => (pub_ne' r hr).2.1 e) (fun e => (pub_ne' r hr).2.2 e)
  obtain hv₁' : Vars 0 s₁' (stateAt s.mem (st s₀)) := by
    obtain ⟨v0, v1, v2, v3⟩ := hv₁
    exact ⟨by rw [hD.regs _ (var_ne_T1 0 0) (var_ne_T2 0 0)]; exact v0,
      by rw [hD.regs _ (var_ne_T1 0 1) (var_ne_T2 0 1)]; exact v1,
      by rw [hD.regs _ (var_ne_T1 0 2) (var_ne_T2 0 2)]; exact v2,
      by rw [hD.regs _ (var_ne_T1 0 3) (var_ne_T2 0 3)]; exact v3⟩
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁' ((hpub₁' .a3 (by decide)).trans hr3₁) hp.al
    (fun k hk => by rw [hD.rd, hD.wr, hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_scr hk)
    (fun k hk => hD.words k hk hk) hv₁' 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  obtain pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁' r hr, hpub₁ r hr]
  obtain hr0₂ : s₂.gpr .a0 = st s₀ := by rw [pub₂ .a0 (by decide), hL.a0]
  obtain hrd₂ : s₂.rd = s₀.rd := by rw [hR.rd, hD.rd, hrd₁, hL.rd]
  obtain hwr₂ : s₂.wr = s₀.wr := by rw [hR.wr, hD.wr, hwr₁, hL.wr]
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr0₂ hrd₂ hwr₂ fun k hk => ?_)
    fun s₃ h₃ => ?_
  · rw [hR.mem, hD.frame.readW (r := stR s₀) (Offset.contains_base (st s₀) (by omega_using [hk]) (by omega_using [hk]))
      (by simpa using hp.st_scr) (by decide), hm₁, getElem!_pos _ k hk, stateAt_get _ _ hk]
  obtain hr1₃ : s₃.gpr .a1 = blkAddr s₀ i := by rw [h₃.pub .a1 (by decide), pub₂ .a1 (by decide), hL.a1]
  obtain hr2₃ : s₃.gpr .a2 = BitVec.ofNat 64 (nb s₀ - i) := by
    rw [h₃.pub .a2 (by decide), pub₂ .a2 (by decide), hL.a2]
  obtain hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    obtain f₁ : Frame [stR s₀, scrR s₀] s.mem s₁'.mem := by rw [← hm₁]; exact hD.frame.mono (by simp)
    refine hL.frame.trans (f₁.trans ?_)
    rw [h₃.mem, hR.mem]
    exact (frame_writeUpTo (r := stR s₀) _ (Nat.le_refl _) fun j hj =>
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])).mono (by simp)
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
      fun r hr h1 h2 => ?_, by rw [grd, h₃.rd, hrd₂], by rw [gwr, h₃.wr, hwr₂], by rw [gm]; exact hframe,
      by rw [gm]; exact hstate⟩
    rw [gr r h1 h2, h₃.pub r hr, pub₂ r hr, hL.kept r hr h1 h2]
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

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.Md5.compressRISCV64.post s₀ s' := by
  obtain hc₀ : Common s₀ 0 s₀ := ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc =>
    ⟨fun r hr => hc.kept r (preserved_pub r hr) (by revert r; decide) (by revert r; decide),
      hc.kept _ (by decide) (by decide) (by decide), hc.state⟩
  refine WP.ite (s₀.gpr .a2 == 0) (by simp [eval]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
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
    obtain hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        a1 := by simp [blkAddr]
        a2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

/-! The constant-time analysis of the compression function from its arguments, done once for
every check of code that calls it (`taint_decide_sum [compressSum]`), which keeps what is public
of `s1`–`s11`: it writes none of them. -/
taint_summary compressSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3]) Impl.Md5.RISCV64.compress
  keeping (Taint.ofRegs [.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11])

theorem compress_verified :
    Verified RISCV64.target Impl.Md5.RISCV64.compress Proof.Md5.compressRISCV64 := by
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
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Md5.RISCV64
