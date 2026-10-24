module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Md5.Spec
public import VerifiedGarbage.Impl.Md5.PPC64LE
public import VerifiedGarbage.Proof.Md5.StateMem
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Md5.Spec
meta import VerifiedGarbage.Impl.Md5.PPC64LE
meta import VerifiedGarbage.Proof.Md5.StateMem
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# MD5 compression function on PPC64LE

The same structure as the AArch64 proof (`VG.Proof.Md5.AArch64`): each
operation is the auxiliary function of its round, symbolically executed once
per round (`fn_ok`), followed by the additions and the rotation, symbolically
executed once for all operations (`tail_ok`). The words are the low 32 bits
of the registers (`Vars`).
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE

open VG VG.PPC64LE VG.Impl.Md5.PPC64LE
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the low 32 bits of the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3]

/-- The pointers, the count, `Ones`, `r0` and the registers the ABI requires
us to preserve: never written by the operations. -/
def pubRegs : List Reg := [.r0, .r3, .r4, .r5, .r12, .r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
  .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The words move one register along each operation. -/
theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 4 - t % 4) % 4]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ .r4 ∧ ∀ p ∈ pubRegs, r ≠ p := by decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne' _ (var_mem t k)).1

theorem var_ne_T1 (t k : Nat) : var t k ≠ T1 := (work_ne' _ (var_mem t k)).2.1

theorem var_ne_r4 (t k : Nat) : var t k ≠ .r4 := (work_ne' _ (var_mem t k)).2.2.1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne' _ (var_mem t k)).2.2.2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .r6 ≠ work.getD ((j + 4 - c) % 4) .r6 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (a b c d : Reg) (ha : a ≠ T0) (hb : b ≠ T0) (hc : c ≠ T0)
    (hd : d ≠ T0) (hab : a ≠ b) (had : a ≠ d)
    (s : State) (va vb vc vd : Word) (h₀ : (s.gpr a).setWidth 32 = va) (h₁ : (s.gpr b).setWidth 32 = vb)
    (h₂ : (s.gpr c).setWidth 32 = vc) (h₃ : (s.gpr d).setWidth 32 = vd)
    (h₄ : (s.gpr Ones).setWidth 32 = ones) :
    WP isa (.block (fn r a b c d)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + roundFn r vb vc vd ∧
      (∀ x, x ≠ a → x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  have hda : d ≠ a := fun h => had h.symm
  simp only [T0, Ones] at ha hb hc hd h₄ ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp only [fn, T0, Ones, runBlock_cons, runStep_some, runBlock_nil, exec_logic, exec_add, isa,
    State.write, ha, hb, hc, hd, hba, hda, ↓reduceIte, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx hx' => by simp [hx, hx'], by trivial⟩ <;>
  simp only [lo32_add, BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_or,
    h₀, h₁, h₂, h₃, h₄]
  · rw [show roundFn 0 = F from rfl, Proof.Md5.F_eq]
  · rw [show roundFn 1 = G from rfl, Proof.Md5.G_add, BitVec.add_assoc]; rfl
  · rw [show roundFn 2 = H from rfl, Proof.Md5.H_eq']
  · rw [show roundFn 3 = I from rfl, Proof.Md5.I_eq]; rfl

/-! ## The rest of an operation -/

/-- The instructions of an operation before the auxiliary function. -/
def headI (a : Reg) (k : Nat) (T : Word) : List Instr := [
  .load .w T1 .r4 (4 * k),
  .add a a T1,
  .lis T1 (T.extractLsb' 16 16),
  .ori T1 T1 (T.extractLsb' 0 16),
  .add a a T1]

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (n : Nat) : List Instr := [
  .rotr .w a a n,
  .add a a b]

theorem step_split (t : Nat) :
    step t = headI (var t 0) (ks.getD t 0) (Ts.getD t 0) ++
      (fn (t / 16) (var t 0) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (32 - Proof.Md5.rot t)) := by
  simp only [step, headI, tailI, List.append_assoc]; rfl

theorem head_ok (a : Reg) (k : Nat) (hk : k < 16) (T : Word) (ha₁ : a ≠ T1)
    (s : State) (va x : Word) (bp : Addr) (h₁ : (s.gpr a).setWidth 32 = va)
    (hr4 : s.gpr .r4 = bp) (hin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hx : s.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = x) :
    WP isa (.block (headI a k T)) s fun s' =>
      (s'.gpr a).setWidth 32 = va + x + T ∧
      (∀ r, r ≠ a → r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have ho : 4 * k < 2 ^ 15 := by omega
  simp only [T1] at ha₁ ⊢
  apply WP.of_runBlock
  simp only [headI, T1, runBlock_cons, runStep_some, runBlock_nil, exec_add,
    exec_load_w (show Reg.r4 ≠ .r0 by decide) ho (by rw [hr4]; exact hin), exec_lis, exec_ori, isa,
    State.write, ha₁, hr4, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr hr' => by simp [hr, hr'], by trivial⟩
  simp only [lo32_add, BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Nat.reduceLeDiff, h₁, hx, lis_ori']

theorem tail_ok (a b : Reg) (n : Nat) (hn : n < 32) (hab : a ≠ b)
    (s : State) (va vb : Word) (h₁ : (s.gpr a).setWidth 32 = va) (h₂ : (s.gpr b).setWidth 32 = vb) :
    WP isa (.block (tailI a b n)) s fun s' =>
      (s'.gpr a).setWidth 32 = va.rotateRight n + vb ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hba : b ≠ a := fun h => hab h.symm
  apply WP.of_runBlock
  simp only [tailI, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_rotr_w hn, isa,
    State.write, hba, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp [hr], by trivial⟩
  simp only [lo32_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff, h₁, h₂]

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : Addr)
    (hv : Vars t s v) (hr4 : s.gpr .r4 = bp) (hones : (s.gpr Ones).setWidth 32 = ones)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := Proof.Md5.ks_lt t ht
  have hr := Proof.Md5.rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (head_ok (var t 0) (ks.getD t 0) hk (Ts.getD t 0) (var_ne_T1 t 0)
    s v[0] (X ⟨ks.getD t 0, hk⟩) bp h0 hr4 (hin _ hk) (hX _ hk)) fun s₁ ⟨a₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, 0 < k → k < 4 → s₁.gpr (var t k) = s.gpr (var t k) := fun k h0 h4 =>
    e₁ _ (var_ne t h4 (by omega) (by omega)) (var_ne_T1 t k)
  have hoa : Ones ≠ var t 0 := fun h => var_ne_pub t 0 (p := .r12) (by decide) h.symm
  rw [WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) (var t 0) (var t 1) (var t 2) (var t 3) (var_ne_T0 t 0)
    (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) (var_ne t (by omega) (by omega) (by omega))
    (var_ne t (by omega) (by omega) (by omega)) s₁
    _ v[1] v[2] v[3] a₁ (by rw [e 1 (by omega) (by omega)]; exact h1)
    (by rw [e 2 (by omega) (by omega)]; exact h2) (by rw [e 3 (by omega) (by omega)]; exact h3)
    (by rw [e₁ _ hoa (by decide)]; exact hones)) fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (tail_ok (var t 0) (var t 1) (32 - Proof.Md5.rot t) (by omega)
    (var_ne t (by omega) (by omega) (by omega)) s₂ _ v[1] a₂
    (by rw [e₂ _ (var_ne t (by omega) (by omega) (by omega)).symm (var_ne_T0 t 1),
      e 1 (by omega) (by omega)]; exact h1)) fun s₃ ⟨a₃, e₃, m₃, rd₃, wr₃⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → r ≠ T1 → s₃.gpr r = s.gpr r := fun r h h' h'' => by
    rw [e₃ r h, e₂ r h h', e₁ r h h'']
  refine ⟨?_, by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [pubRegs, T0] at hr)
      (fun h => by subst h; simp [pubRegs, T1] at hr)⟩
  rw [Proof.Md5.step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), Proof.Md5.stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3) (var_ne_T1 t 3), h3]
  · rw [a₃, Proof.Md5.rotateLeft_eq _ hr.1 hr.2, BitVec.add_comm (v[1]), Proof.Md5.add_fn]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1) (var_ne_T1 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2) (var_ne_T1 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : Addr) (sB : State) (hr4 : sB.gpr .r4 = bp)
    (hones : (sB.gpr Ones).setWidth 32 = ones)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (bp + BitVec.ofNat 64 (4 * k)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_r4 : s.gpr .r4 = bp := (hs.pub .r4 (by decide)).trans hr4
    have hs_ones : (s.gpr Ones).setWidth 32 = ones :=
      (congrArg (·.setWidth 32) (hs.pub .r12 (by decide))).trans hones
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_r4 hs_ones
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.PPC64LE

/-!
## MD5: the PPC64LE contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
return address is in the link register, which the target's calling
convention requires to be preserved (`VG.PPC64LE.abiPreserved`); `update`
and `finalize` save it in a 48-byte frame below the stack pointer.
-/

namespace VG.Proof.Md5

open Spec.Md5

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`:
updates the MD buffer at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(16 bytes) and `scratch` (64 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the MD
buffer and the blocks are secret. -/
def compressPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 16⟩
    let blocks : Region := ⟨s.gpr .r4, 64 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 64⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .r3) =
      compressBlocks (stateAt s.mem (s.gpr .r3)) s.mem (s.gpr .r4) (s.gpr .r5).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_md5_init(state: *mut [u8; 80])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (80 bytes). The pointer is public. -/
def initPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 80⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .r3) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (80
bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 48 bytes below the stack pointer
(the frame saving the link register), which do not wrap around. The
pointers, `count` and `len` are public; the state and the data are secret. -/
def updatePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 80⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 112⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .r3) (m ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the MD5 digest of `m` to `out`.

The code may read and write `state` (80 bytes, whose contents on exit are
unspecified), `out` (16 bytes) and `scratch` (112 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 48 bytes
below the stack pointer (the frame saving the link register), which do not
wrap around. The pointers and `count` are public; the state is secret. -/
def finalizePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 80⟩
    let out : Region := ⟨s.gpr .r5, 16⟩
    let scratch : Region := ⟨s.gpr .r6, 112⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .r5) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Md5

namespace VG.Proof.Md5.PPC64LE

open VG VG.PPC64LE VG.Impl.Md5.PPC64LE
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Md5/StateMem.lean`). -/
export VG.Proof.Md5.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep readW_writeW_word
  stateAt_eq stateAt_get writeState stateAt_writeState)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev bp : Addr := s₀.gpr .r4
abbrev nb : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r6
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

theorem pre_of (s₀ : State) (h : Proof.Md5.compressPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 4) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 4) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nb s₀ - i)

/-- The registers `load` does not write. -/
def loadKept : List Reg := [.r0, .r3, .r4, .r5] ++ preserved

theorem loadKept_sub : ∀ r ∈ loadKept, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .load .w .r6 .r3 (4 * 0), .load .w .r7 .r3 (4 * 1), .load .w .r8 .r3 (4 * 2),
    .load .w .r9 .r3 (4 * 3),
    .lis .r12 (ones.extractLsb' 16 16), .ori .r12 .r12 (ones.extractLsb' 0 16)] := by
  decide

theorem update_eq : update ++ advance = [
    .load .w .r10 .r3 (4 * 0), .load .w .r11 .r3 (4 * 1), .load .w .r12 .r3 (4 * 2),
    .load .w .r0 .r3 (4 * 3),
    .add .r6 .r6 .r10, .add .r7 .r7 .r11, .add .r8 .r8 .r12, .add .r9 .r9 .r0,
    .store .w .r6 .r3 (4 * 0), .store .w .r7 .r3 (4 * 1), .store .w .r8 .r3 (4 * 2),
    .store .w .r9 .r3 (4 * 3),
    .addi .r4 .r4 64, .subi .r5 .r5 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    (s.gpr .r6).setWidth 32 = v[0] ∧ (s.gpr .r7).setWidth 32 = v[1] ∧
    (s.gpr .r8).setWidth 32 = v[2] ∧ (s.gpr .r9).setWidth 32 = v[3] := Iff.rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr3 : s.gpr .r3 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (s₁.gpr Ones).setWidth 32 = ones ∧
      (∀ r ∈ loadKept, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 4 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide)
  simp only [Nat.reduceMul] at h0 h1 h2 h3
  apply WP.of_runBlock
  rw [load_eq]
  simp only [vars0, Ones, runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_lis, exec_ori, isa,
    State.write, hr3, h0, h1, h2, h3, Option.some.injEq, exists_eq_left', Nat.reduceMul,
    Nat.reducePow, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    and_true]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lis_ori ones, fun r hr => ?_⟩
  · rw [lo32_ext, stateAt_get _ _ (show 0 < 4 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 1 < 4 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 2 < 4 by decide)]
  · rw [lo32_ext, stateAt_get _ _ (show 3 < 4 by decide)]
  · have : r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by revert r; decide
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 4 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _ (c 3 ?_) <;>
  simp

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr3 : s.gpr .r3 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r4 = s.gpr .r4 + 64 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      s'.gpr .r3 = s.gpr .r3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 4 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 4 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_w, exec_store_w, exec_add,
    exec_addi, exec_subi, State.write, hr3, i0, i1, i2, i3, o0, o1, o2, o3,
    Option.some.injEq, exists_eq_left', Nat.reduceMul, Nat.reducePow,
    Nat.reduceLeDiff, Nat.reduceLT, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, and_self,
    true_and, and_true]
  simp only [lo32_add, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, m0, m1, m2, m3,
    v0, v1, v2, v3, Nat.reduceLeDiff]
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i k : Nat) (hk : k < 16) :
    s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
  rw [Proof.Md5.readW_bytes]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .d .r5) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r3 hL.rd hL.wr)
    fun s₁ ⟨hv₁, hones₁, hkept₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ k (hk : k < 16),
      s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hm₁, hL.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_st) (by decide)]
    exact blk_word i k hk
  have hr4₁ : s₁.gpr .r4 = blkAddr s₀ i := (hkept₁ .r4 (by decide)).trans hL.r4
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁ hr4₁ hones₁
    (fun k hk => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi hk) hX hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have kept₂ : ∀ r ∈ loadKept, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r (loadKept_sub r hr), hkept₁ r hr]
  have hr3₂ : s₂.gpr .r3 = st s₀ := by rw [kept₂ .r3 (by decide), hL.r3]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr3₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.mem, hm₁, stateAt_get _ _ hk]
  obtain ⟨hm₃, hr4₃, hr5₃, hr3₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hr5 : s₂.gpr .r5 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [kept₂ .r5 (by decide), hL.r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀] s₀.mem s₃.mem := by
    rw [hm₃, hR.mem, hm₁]
    exact frame_writeState hL.frame _
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr3₃, hr3₂],
      fun r hr => by
        rw [hkept₃ r hr, kept₂ r (by simp only [loadKept, List.mem_append]; exact .inr hr),
          hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .d .r5) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr5₃, hr5]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r4 := ?_, r5 := ?_ }⟩
    · rw [hr4₃, kept₂ .r4 (by decide), hL.r4]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hr5₃, hr5]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Md5.compressPPC64LE.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .r5 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .d .r5) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        r4 := by simp [blkAddr]
        r5 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified PPC64LE.target Impl.Md5.PPC64LE.compress Proof.Md5.compressPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Md5.PPC64LE
