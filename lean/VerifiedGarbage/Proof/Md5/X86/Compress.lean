import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Md5.Spec
import VerifiedGarbage.Impl.Md5.X86
import VerifiedGarbage.Proof.Md5.X86.Lit
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs

/- Proofs formerly in `VerifiedGarbage.Proof.Md5.X86.Contract`. -/
section

/-!
# MD5: the x86 (32-bit) contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the x86 (32-bit) implementations of the compression function and of
streaming MD5 (`init`/`update`/`finalize`, on the representation `Repr`), in
terms of `Spec/Md5.lean`.

The shared contracts let the streaming functions write their own argument
area (cdecl passes the arguments in the caller's frame, just above the
return address, and the callee owns them). `update` only reads it, and its
contract here says so; `finalize`'s lets it write them. `update` and
`finalize` call the compression function, using the 20 bytes of stack below
the return address.
-/

namespace VG.Proof.Md5

open Spec.Md5

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`,
whose arguments are on the stack (cdecl): updates the MD buffer at `state`
with the `n` 64-byte blocks at `blocks`.

The code may read the arguments (16 bytes above the return address) and
`blocks` (`64 * n` bytes), and read and write `state` (16 bytes) and
`scratch` (64 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the blocks, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers and `n`) are public; the MD buffer and
the blocks are secret. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) =
      compressBlocks (stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

open X86 in
/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := arg s 2 ++ arg s 1

open X86 in
/-- x86 (32-bit) contract for `vg_md5_init(state: *mut [u8; 80])`, whose
argument is on the stack (cdecl): makes the streaming state at `state`
represent the empty message.

The code may read the argument (4 bytes above the return address) and write
`state` (80 bytes), which may not overlap the argument or the return address;
nothing may wrap around the end of the (32-bit) address space. `esp` and the
pointer are public. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := Repr s'.mem ((arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `data`, `len`, `scratch`): if the streaming state at `state`
represents a message `m` of `count` bytes (modulo 2⁶⁴), then afterwards it
represents `m` followed by the `len` bytes at `data`.

The code may read the arguments (24 bytes above the return address) and
`data` (`len` bytes), and read and write `state` (80 bytes) and `scratch`
(112 bytes, whose contents on exit are unspecified). The writable buffers may not
overlap each other, the data or the arguments; none of them may overlap the
return address or the 20 bytes of stack below it; and nothing may wrap
around the end of the (32-bit) address space. `esp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 112 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem ((arg s 0).setWidth 64) m → VG.Proof.Md5.countX86 s = BitVec.ofNat 64 m.length →
    Repr s'.mem ((arg s 0).setWidth 64) (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `out`, `scratch`): if the streaming state at `state` represents a
message `m` of `count` bytes (modulo 2⁶⁴), writes the MD5 digest of `m` to
`out`.

The code may read and write the arguments (20 bytes above the return
address, whose contents on exit are unspecified), `state` (80 bytes, whose
contents on exit are unspecified), `out` (16 bytes) and `scratch` (112
bytes, whose contents on exit are unspecified). These may not overlap each
other or the return address; none of the buffers may overlap the 20 bytes
of stack below the return address; and nothing may wrap around the end of
the (32-bit) address space. `esp`, the pointers and `count` are public; the
state is secret. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 16⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 112 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem ((arg s 0).setWidth 64) m → VG.Proof.Md5.countX86 s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem ((arg s 3).setWidth 64) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Md5

end

/- Proofs formerly in `VerifiedGarbage.Proof.Md5.X86.Compress`. -/
section

/-!
# MD5 compression function on x86 (32-bit): the 64 operations

Each operation is the auxiliary function of its round, symbolically executed
once per round (`fn_ok`), followed by the additions and the rotation,
symbolically executed once for all operations (`tail_ok`).
-/

namespace VG.Proof.Md5.X86

open VG VG.X86 VG.Impl.Md5.X86
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3]

/-- The block pointer, the count and `esp`: never written by the operations. -/
def pubRegs : List Reg := [.esi, .ebp, .esp]

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

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ ∀ p ∈ VG.Proof.Md5.X86.pubRegs, r ≠ p := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (VG.Proof.Md5.X86.work_ne (VG.Proof.Md5.X86.var_mem t k)).1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ VG.Proof.Md5.X86.pubRegs) : var t k ≠ p :=
  (VG.Proof.Md5.X86.work_ne (VG.Proof.Md5.X86.var_mem t k)).2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .eax ≠ work.getD ((j + 4 - c) % 4) .eax := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  VG.Proof.Md5.X86.var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (b c d : Reg) (hb : b ≠ T0) (hc : c ≠ T0) (hd : d ≠ T0)
    (s : State) (vb vc vd : Word) (h₁ : s.gpr b = vb) (h₂ : s.gpr c = vc) (h₃ : s.gpr d = vd) :
    WP isa (.block (fn r b c d)) s fun s' =>
      s'.gpr T0 = roundFn r vb vc vd ∧ (∀ x, x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T0] at hb hc hd ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp only [↓reduceIte, and_self, fn, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hb, hc, hd,
    h₁, h₂, h₃, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx => by simp [hx], trivial⟩
  · rw [show roundFn 0 = F from rfl, F_eq]
  · rw [show roundFn 1 = G from rfl, G_eq]
  · rfl
  · rw [show roundFn 3 = I from rfl, I_eq]

/-! ## The rest of an operation -/

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (k : Nat) (T : Word) (n : Nat) : List Instr := [
  .alu .add a (.reg T0),
  .alu .add a (.mem (at_ .esi (4 * k))),
  .alu .add a (.imm T),
  .shift .ror a n,
  .alu .add a (.reg b)]

theorem step_split (t : Nat) :
    step t = fn (t / 16) (var t 1) (var t 2) (var t 3) ++
      VG.Proof.Md5.X86.tailI (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - Proof.Md5.rot t) := rfl

theorem tail_ok (a b : Reg) (k : Nat) (T : Word) (n : Nat) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 31)
    (hab : a ≠ b) (hsi : a ≠ .esi) (s : State) (va vb f x : Word) (bp : BitVec 32)
    (h₁ : s.gpr a = va) (h₂ : s.gpr b = vb) (h₃ : s.gpr T0 = f)
    (hesi : s.gpr .esi = bp) (hin : InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4)
    (hx : s.mem.readW (addr bp (4 * k)) 32 = x) :
    WP isa (.block (VG.Proof.Md5.X86.tailI a b k T n)) s fun s' =>
      s'.gpr a = (va + f + x + T).rotateRight n + vb ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsi' : Reg.esi ≠ a := fun h => hsi h.symm
  have hba : b ≠ a := fun h => hab h.symm
  simp only [T0] at h₃
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reducePow, VG.Proof.Md5.X86.tailI, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execShift, readSrc, ea_mk, State.load32, at_,
    isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hsi', hba,
    hn₁, hn₂, and_self, h₁, h₂, h₃, hesi, hin, hx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : BitVec 32)
    (hv : VG.Proof.Md5.X86.Vars t s v) (hesi : s.gpr .esi = bp)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (addr bp (4 * k)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      VG.Proof.Md5.X86.Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ VG.Proof.Md5.X86.pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  rw [VG.Proof.Md5.X86.step_split, WP.block_append_iff]
  refine WP.mono (VG.Proof.Md5.X86.fn_ok (t / 16) (by omega) _ _ _ (VG.Proof.Md5.X86.var_ne_T0 t 1) (VG.Proof.Md5.X86.var_ne_T0 t 2) (VG.Proof.Md5.X86.var_ne_T0 t 3) s
    v[1] v[2] v[3] h1 h2 h3) fun s₁ ⟨f₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => e₁ _ (VG.Proof.Md5.X86.var_ne_T0 t k)
  refine WP.mono (VG.Proof.Md5.X86.tail_ok (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - rot t) (by omega)
    (by omega) (VG.Proof.Md5.X86.var_ne t (by omega) (by omega) (by omega))
    (VG.Proof.Md5.X86.var_ne_pub t 0 (by simp [VG.Proof.Md5.X86.pubRegs])) s₁ v[0] v[1] (roundFn (t / 16) v[1] v[2] v[3]) (X ⟨ks.getD t 0, hk⟩) bp
    (by rw [e]; exact h0) (by rw [e]; exact h1) f₁ (by rw [e₁ _ (by decide)]; exact hesi)
    (by rw [rd₁, wr₁]; exact hin _ hk) (by rw [m₁]; exact hX _ hk))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → s₂.gpr r = s.gpr r := fun r h h' => by rw [e₂ r h, e₁ r h']
  refine ⟨?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr =>
    g r (fun h => VG.Proof.Md5.X86.var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [VG.Proof.Md5.X86.pubRegs, T0] at hr)⟩
  rw [step_eq X v ht]
  simp only [VG.Proof.Md5.X86.Vars, VG.Proof.Md5.X86.var_succ_zero, VG.Proof.Md5.X86.var_succ t _ (show 0 < 3 by omega),
    VG.Proof.Md5.X86.var_succ t _ (show 1 < 3 by omega), VG.Proof.Md5.X86.var_succ t _ (show 2 < 3 by omega), stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (VG.Proof.Md5.X86.var_ne t (by omega) (by omega) (by omega)) (VG.Proof.Md5.X86.var_ne_T0 t 3), h3]
  · rw [a₂, rotateLeft_eq _ hr.1 hr.2, BitVec.add_comm (v[1])]
  · rw [g _ (VG.Proof.Md5.X86.var_ne t (by omega) (by omega) (by omega)) (VG.Proof.Md5.X86.var_ne_T0 t 1), h1]
  · rw [g _ (VG.Proof.Md5.X86.var_ne t (by omega) (by omega) (by omega)) (VG.Proof.Md5.X86.var_ne_T0 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : VG.Proof.Md5.X86.Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ VG.Proof.Md5.X86.pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : BitVec 32) (sB : State) (hesi : sB.gpr .esi = bp)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (addr bp (4 * k)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (addr bp (4 * k)) 32 = X ⟨k, hk⟩)
    (h0 : VG.Proof.Md5.X86.Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (VG.Proof.Md5.X86.RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_esi : s.gpr .esi = bp := (hs.pub .esi (by decide)).trans hesi
    refine WP.mono (VG.Proof.Md5.X86.step_ok t (by omega) s _ X bp hs.vars hs_esi (by rw [hs.rd, hs.wr]; exact hin)
      (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.X86

/-!
# MD5 compression function on x86 (32-bit): the whole function
-/

namespace VG.Proof.Md5.X86

open VG VG.X86 VG.Impl.Md5.X86
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact VG.Proof.Md5.X86.contains_offset h ho

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(VG.Proof.Md5.X86.st s₀).setWidth 64, 16⟩
abbrev blR : Region := ⟨(VG.Proof.Md5.X86.bp s₀).setWidth 64, 64 * VG.Proof.Md5.X86.nb s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.Md5.X86.scr s₀).setWidth 64, 64⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.Md5.X86.esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((VG.Proof.Md5.X86.st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Md5.X86.bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((VG.Proof.Md5.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the MD buffer. -/
abbrev stAddr (k : Nat) : Addr := addr (VG.Proof.Md5.X86.st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Md5.X86.blR s₀, VG.Proof.Md5.X86.argR s₀]
  wr : s₀.wr = [VG.Proof.Md5.X86.stR s₀, VG.Proof.Md5.X86.scrR s₀]
  st_scr : (VG.Proof.Md5.X86.stR s₀).Disjoint (VG.Proof.Md5.X86.scrR s₀)
  blk_st : (VG.Proof.Md5.X86.blR s₀).Disjoint (VG.Proof.Md5.X86.stR s₀)
  blk_scr : (VG.Proof.Md5.X86.blR s₀).Disjoint (VG.Proof.Md5.X86.scrR s₀)
  arg_st : (VG.Proof.Md5.X86.argR s₀).Disjoint (VG.Proof.Md5.X86.stR s₀)
  arg_scr : (VG.Proof.Md5.X86.argR s₀).Disjoint (VG.Proof.Md5.X86.scrR s₀)
  ret_st : (VG.Proof.Md5.X86.retR s₀).Disjoint (VG.Proof.Md5.X86.stR s₀)
  ret_scr : (VG.Proof.Md5.X86.retR s₀).Disjoint (VG.Proof.Md5.X86.scrR s₀)
  st_fits : (VG.Proof.Md5.X86.st s₀).toNat + 16 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Md5.X86.bp s₀).toNat + 64 * VG.Proof.Md5.X86.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Md5.X86.scr s₀).toNat + 64 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Md5.X86.esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Md5.compressX86.pre s₀) : VG.Proof.Md5.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Md5.X86.Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 4) :
    VG.Proof.Md5.X86.stAddr s₀ k = (VG.Proof.Md5.X86.st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (VG.Proof.Md5.X86.esp₀ s₀) d = (VG.Proof.Md5.X86.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < VG.Proof.Md5.X86.nb s₀) (ht : t < 16) :
    addr (VG.Proof.Md5.X86.blkAddr s₀ i) (4 * t) =
      (VG.Proof.Md5.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (VG.Proof.Md5.X86.bp s₀).isLt; omega)]
  have e : (VG.Proof.Md5.X86.blkAddr s₀ i).setWidth 64 = (VG.Proof.Md5.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := VG.Proof.Md5.X86.bp s₀) (k := 64 * i) (by omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 64) :
    addr (VG.Proof.Md5.X86.scr s₀) d = (VG.Proof.Md5.X86.scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega)

theorem in_scr {d : Nat} (hd : d + 4 ≤ 64) : InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Md5.X86.scr s₀) d) 4 :=
  ⟨VG.Proof.Md5.X86.scrR s₀, by simp [h.wr], VG.Proof.Md5.X86.contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem out_scr {d : Nat} (hd : d + 4 ≤ 64) : InRegions s₀.wr (addr (VG.Proof.Md5.X86.scr s₀) d) 4 :=
  ⟨VG.Proof.Md5.X86.scrR s₀, by simp [h.wr], VG.Proof.Md5.X86.contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Md5.X86.argR s₀).Contains (addr (VG.Proof.Md5.X86.esp₀ s₀) d) 4 := by
  show (⟨addr (VG.Proof.Md5.X86.esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Md5.X86.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Md5.X86.argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Md5.X86.argR s₀) := by
  show Region.Sub ⟨addr (VG.Proof.Md5.X86.esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (VG.Proof.Md5.X86.esp₀ s₀) 4, 16⟩
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Md5.X86.stR s₀, VG.Proof.Md5.X86.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < VG.Proof.Md5.X86.nb s₀) (ht : t < 16) :
    (VG.Proof.Md5.X86.blR s₀).Contains (addr (VG.Proof.Md5.X86.blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact VG.Proof.Md5.X86.contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < VG.Proof.Md5.X86.nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Md5.X86.blkAddr s₀ i) (4 * t)) 4 :=
  ⟨VG.Proof.Md5.X86.blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {d e : Nat} (hd : d + 4 ≤ 16) (he : e + 4 ≤ 16)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (VG.Proof.Md5.X86.st s₀) d) 4 (addr (VG.Proof.Md5.X86.st s₀) e) 4 := by
  have := hp.st_fits
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ hde (by omega) (by omega)

/-- Reading the MD buffer at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 16) (he : e + 4 ≤ 16) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (VG.Proof.Md5.X86.st s₀) e) v).readW (addr (VG.Proof.Md5.X86.st s₀) d) 32 = m.readW (addr (VG.Proof.Md5.X86.st s₀) d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Md5.X86.st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {d : Nat} (hd : d < 16) :
    addr (VG.Proof.Md5.X86.st s₀) d = (VG.Proof.Md5.X86.st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem in_st {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {d : Nat} (hd : d + 4 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Md5.X86.st s₀) d) 4 :=
  ⟨VG.Proof.Md5.X86.stR s₀, by simp [hp.wr], VG.Proof.Md5.X86.contains_sub hd (by omega) (VG.Proof.Md5.X86.st_eq hp (by omega))⟩

theorem out_st {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {d : Nat} (hd : d + 4 ≤ 16) :
    InRegions s₀.wr (addr (VG.Proof.Md5.X86.st s₀) d) 4 :=
  ⟨VG.Proof.Md5.X86.stR s₀, by simp [hp.wr], VG.Proof.Md5.X86.contains_sub hd (by omega) (VG.Proof.Md5.X86.st_eq hp (by omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 4) → m.readW (VG.Proof.Md5.X86.stAddr s₀ k) 32 = v[k]) :
    stateAt m ((VG.Proof.Md5.X86.st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) (m : Mem) {k : Nat} (hk : k < 4) :
    (stateAt m ((VG.Proof.Md5.X86.st s₀).setWidth 64))[k] = m.readW (VG.Proof.Md5.X86.stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers and their slots in the scratch buffer. -/
def compressSaved : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem compressSaved_fits : Spill.Fits 64 VG.Proof.Md5.X86.compressSaved := by decide

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (VG.Proof.Md5.X86.scr s₀)) s₀.gpr VG.Proof.Md5.X86.compressSaved

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Md5.X86.stR s₀, VG.Proof.Md5.X86.scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((VG.Proof.Md5.X86.st s₀).setWidth 64) =
    compressBlocks (VG.Proof.Md5.X86.H₀ s₀) s₀.mem ((VG.Proof.Md5.X86.bp s₀).setWidth 64) i
  saved : VG.Proof.Md5.X86.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Md5.X86.Common s₀ i s where
  esi : s.gpr .esi = VG.Proof.Md5.X86.blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Md5.X86.nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [.mov .edi (.mem ⟨.esp, 4⟩), .mov .eax (.mem ⟨.edi, 0⟩),
    .mov .ebx (.mem ⟨.edi, 4⟩), .mov .ecx (.mem ⟨.edi, 8⟩), .mov .edx (.mem ⟨.edi, 12⟩)] := by
  decide

theorem update_eq : update ++ advance = [.mov .edi (.mem ⟨.esp, 4⟩),
    .alu .add .eax (.mem ⟨.edi, 0⟩), .alu .add .ebx (.mem ⟨.edi, 4⟩),
    .alu .add .ecx (.mem ⟨.edi, 8⟩), .alu .add .edx (.mem ⟨.edi, 12⟩),
    .store ⟨.edi, 0⟩ .eax, .store ⟨.edi, 4⟩ .ebx, .store ⟨.edi, 8⟩ .ecx, .store ⟨.edi, 12⟩ .edx,
    .alu .add .esi (.imm 64), .alu .sub .ebp (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : VG.Proof.Md5.X86.Vars 0 s v ↔
    s.gpr .eax = v[0] ∧ s.gpr .ebx = v[1] ∧ s.gpr .ecx = v[2] ∧ s.gpr .edx = v[3] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {s : State} (hesp : s.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) 4) 32 = VG.Proof.Md5.X86.st s₀) :
    WP isa (.block load) s fun s₁ =>
      VG.Proof.Md5.X86.Vars 0 s₁ (stateAt s.mem ((VG.Proof.Md5.X86.st s₀).setWidth 64)) ∧ (∀ r ∈ VG.Proof.Md5.X86.pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have ia : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Md5.X86.esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (addr (VG.Proof.Md5.X86.st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => VG.Proof.Md5.X86.in_st hp hd
  have h0 := hin 0 (by decide); have h1 := hin 4 (by decide); have h2 := hin 8 (by decide)
  have h3 := hin 12 (by decide)
  apply WP.of_runBlock
  rw [VG.Proof.Md5.X86.load_eq]
  simp (config := {decide := true}) only [VG.Proof.Md5.X86.vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_mk,
    State.load32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hesp, ia, harg, h0, h1, h2, h3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [VG.Proof.Md5.X86.stateAt_get hp _ (show 0 < 4 by decide), VG.Proof.Md5.X86.stateAt_get hp _ (show 1 < 4 by decide),
    VG.Proof.Md5.X86.stateAt_get hp _ (show 2 < 4 by decide), VG.Proof.Md5.X86.stateAt_get hp _ (show 3 < 4 by decide), VG.Proof.Md5.X86.stAddr]
  simp (config := {decide := true}) [VG.Proof.Md5.X86.pubRegs]

/-- Four words written in order to the MD buffer. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (VG.Proof.Md5.X86.st s₀)
  ((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (VG.Proof.Md5.X86.writeState s₀ m v) ((VG.Proof.Md5.X86.st s₀).setWidth 64) = v := by
  apply VG.Proof.Md5.X86.stateAt_eq hp
  intro k hk
  simp only [VG.Proof.Md5.X86.writeState, VG.Proof.Md5.X86.stAddr]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with h | h | h | h <;> subst h <;>
  simp (disch := decide) only [Mem.readW_writeW_self32,
    VG.Proof.Md5.X86.readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {m m' : Mem} (h : Frame [VG.Proof.Md5.X86.stR s₀] m m')
    (v : HashValue) : Frame [VG.Proof.Md5.X86.stR s₀] m (VG.Proof.Md5.X86.writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 16 → (VG.Proof.Md5.X86.stR s₀).Contains (addr (VG.Proof.Md5.X86.st s₀) d) (32 / 8) :=
    fun d hd => VG.Proof.Md5.X86.contains_sub hd (by omega) (VG.Proof.Md5.X86.st_eq hp (by omega))
  simp only [VG.Proof.Md5.X86.writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _ (c 12 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {s : State} (V H : HashValue) (hv : VG.Proof.Md5.X86.Vars 0 s V)
    (hesp : s.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) 4) 32 = VG.Proof.Md5.X86.st s₀)
    (hH : ∀ k : Nat, (hk : k < 4) → s.mem.readW (VG.Proof.Md5.X86.stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = VG.Proof.Md5.X86.writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .esi = s.gpr .esi + 64 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
      s'.zf = some (s.gpr .ebp - 1 == 0) ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Md5.X86.esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (addr (VG.Proof.Md5.X86.st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => VG.Proof.Md5.X86.in_st hp hd
  have hout : ∀ d, d + 4 ≤ 16 → InRegions s.wr (addr (VG.Proof.Md5.X86.st s₀) d) 4 := by
    rw [hwr]; exact fun d hd => VG.Proof.Md5.X86.out_st hp hd
  have i0 := hin 0 (by decide); have i1 := hin 4 (by decide); have i2 := hin 8 (by decide)
  have i3 := hin 12 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 4 (by decide); have o2 := hout 8 (by decide)
  have o3 := hout 12 (by decide)
  have m0 : s.mem.readW (addr (VG.Proof.Md5.X86.st s₀) 0) 32 = H[0] := hH 0 (by decide)
  have m1 : s.mem.readW (addr (VG.Proof.Md5.X86.st s₀) 4) 32 = H[1] := hH 1 (by decide)
  have m2 : s.mem.readW (addr (VG.Proof.Md5.X86.st s₀) 8) 32 = H[2] := hH 2 (by decide)
  have m3 : s.mem.readW (addr (VG.Proof.Md5.X86.st s₀) 12) 32 = H[3] := hH 3 (by decide)
  rw [VG.Proof.Md5.X86.vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  rw [VG.Proof.Md5.X86.update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.cf_arithFlags,
    hesp, ia, harg, i0, i1, i2, i3, o0, o1, o2, o3,
    m0, m1, m2, m3, v0, v1, v2, v3, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial⟩
  simp only [VG.Proof.Md5.X86.writeState, Vector.getElem_zipWith]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {i t : Nat} (hi : i < VG.Proof.Md5.X86.nb s₀) (ht : t < 16) :
    s₀.mem.readW (addr (VG.Proof.Md5.X86.blkAddr s₀ i) (4 * t)) 32 = VG.Proof.Md5.X86.blk s₀ i ⟨t, ht⟩ := by
  rw [hp.blkAddr_eq hi ht, readW_bytes]
  simp only [VG.Proof.Md5.X86.blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem harg_of {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Md5.X86.stR s₀, VG.Proof.Md5.X86.scrR s₀] s₀.mem m) :
    m.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) 4) 32 = VG.Proof.Md5.X86.st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem saved_frame {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {m m' : Mem} (h : VG.Proof.Md5.X86.Saved s₀ m) (hf : Frame [VG.Proof.Md5.X86.stR s₀] m m') :
    VG.Proof.Md5.X86.Saved s₀ m' :=
  h.of_frame hf (Spill.contains_of_fits hp.scr_fits VG.Proof.Md5.X86.compressSaved_fits) (by simpa using hp.st_scr.symm)

theorem body_ok {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {i : Nat} (hi : i < VG.Proof.Md5.X86.nb s₀) {s : State}
    (hL : VG.Proof.Md5.X86.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Md5.X86.Common s₀ (VG.Proof.Md5.X86.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Md5.X86.nb s₀ ∧ VG.Proof.Md5.X86.LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (VG.Proof.Md5.X86.load_ok hp hL.esp hL.rd hL.wr (VG.Proof.Md5.X86.harg_of hp hL.frame))
    fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ t (ht : t < 16), s₁.mem.readW (addr (VG.Proof.Md5.X86.blkAddr s₀ i) (4 * t)) 32 = VG.Proof.Md5.X86.blk s₀ i ⟨t, ht⟩ := by
    intro t ht
    rw [hm₁, hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact VG.Proof.Md5.X86.blk_word hp hi ht
  have hesi₁ : s₁.gpr .esi = VG.Proof.Md5.X86.blkAddr s₀ i := (hpub₁ .esi (by decide)).trans hL.esi
  refine WP.seq (WP.mono (VG.Proof.Md5.X86.steps_ok _ (VG.Proof.Md5.X86.blk s₀ i) _ s₁ hesi₁
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hX hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have pub₂ : ∀ r ∈ VG.Proof.Md5.X86.pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hm₂ : s₂.mem = s.mem := by rw [hR.mem, hm₁]
  refine WP.mono (VG.Proof.Md5.X86.update_ok hp _ (stateAt s.mem ((VG.Proof.Md5.X86.st s₀).setWidth 64)) hR.vars
    (by rw [pub₂ .esp (by decide), hL.esp]) (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr])
    (by rw [hm₂]; exact VG.Proof.Md5.X86.harg_of hp hL.frame) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hm₂, VG.Proof.Md5.X86.stateAt_get hp _ hk]
  obtain ⟨hm₃, hesi₃, hebp₃, hz₃, hesp₃, hrd₃, hwr₃⟩ := h₃
  have hnb : VG.Proof.Md5.X86.nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (VG.Proof.Md5.X86.nb s₀ - (i + 1)) := by
    rw [pub₂ .ebp (by decide), hL.ebp, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hfw : Frame [VG.Proof.Md5.X86.stR s₀] s.mem s₃.mem := by
    rw [hm₃, hm₂]; exact VG.Proof.Md5.X86.frame_writeState hp (Frame.refl _ _) _
  have hframe : Frame [VG.Proof.Md5.X86.stR s₀, VG.Proof.Md5.X86.scrR s₀] s₀.mem s₃.mem :=
    hL.frame.trans (hfw.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  have hcommon : ∀ j, j = i + 1 → VG.Proof.Md5.X86.Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hesp₃, pub₂ .esp (by decide), hL.esp],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_,
      VG.Proof.Md5.X86.saved_frame hp hL.saved hfw⟩
    rw [hm₃, VG.Proof.Md5.X86.stateAt_writeState hp, VG.Proof.Md5.X86.compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (VG.Proof.Md5.X86.nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hebp, Option.map_some]
  by_cases hlast : i + 1 = VG.Proof.Md5.X86.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : VG.Proof.Md5.X86.nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Md5.X86.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with esi := ?_, ebp := ?_ }⟩
    · rw [hesi₃, pub₂ .esi (by decide), hL.esi]
      simp only [VG.Proof.Md5.X86.blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hebp₃, hebp]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.saveCode .eax VG.Proof.Md5.X86.compressSaved ++
    ([.mov .esi (.mem ⟨.esp, 8⟩), .mov .ebp (.mem ⟨.esp, 12⟩), .alu .test .ebp (.reg .ebp)] : List Instr)) :=
  rfl

theorem epilogue_eq : epilogue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.restoreCode .eax VG.Proof.Md5.X86.compressSaved ++ []) := rfl

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (VG.Proof.Md5.X86.scr s₀)) s₀.gpr VG.Proof.Md5.X86.compressSaved

/-- Reading an argument after saving the registers. -/
theorem saveMem_arg {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Md5.X86.saveMem s₀).readW (addr (VG.Proof.Md5.X86.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) d) 32 :=
  Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
    hp.arg_scr.sep (hp.arg_contains hd hd') (Spill.contains_of_fits hp.scr_fits VG.Proof.Md5.X86.compressSaved_fits p h)

theorem save_ok {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = VG.Proof.Md5.X86.bp s₀ ∧ s₁.gpr .ebp = arg s₀ 2 ∧
      s₁.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Md5.X86.saveMem s₀ ∧
      s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  rw [VG.Proof.Md5.X86.prologue_eq]
  refine Wp.wp_ldm rfl (hp.in_arg (d := 16) (by omega) (by omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok VG.Proof.Md5.X86.compressSaved (fun p h => by rw [u₁.gpr, u₁.wr]; exact hp.out_scr (compressSaved_fits.1 p h))
    fun s₂ u₂ => ?_
  have hm : s₂.mem = VG.Proof.Md5.X86.saveMem s₀ := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have hesp : s₂.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  refine Wp.wp_ldm hesp (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hp.in_arg (d := 8) (by omega) (by omega))
    fun s₃ u₃ => Wp.wp_ldm (by rw [u₃.other _ (by decide), hesp])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hp.in_arg (d := 12) (by omega) (by omega))
    fun s₄ u₄ => Wp.wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, hm, VG.Proof.Md5.X86.saveMem_arg hp (by omega) (by omega)]; rfl
  · rw [f₅.gpr, u₄.gpr, u₃.mem, hm, VG.Proof.Md5.X86.saveMem_arg hp (by omega) (by omega)]; rfl
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hesp]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm]
  · rw [z₅, u₄.gpr, u₃.mem, hm, VG.Proof.Md5.X86.saveMem_arg hp (by omega) (by omega)]; rfl

theorem saveMem_saved {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) : VG.Proof.Md5.X86.Saved s₀ (VG.Proof.Md5.X86.saveMem s₀) :=
  Spill.saveMem_saved_addr _ _ VG.Proof.Md5.X86.compressSaved_fits hp.scr_fits

theorem saveMem_frame {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) : Frame [VG.Proof.Md5.X86.scrR s₀] s₀.mem (VG.Proof.Md5.X86.saveMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ (Spill.contains_of_fits hp.scr_fits VG.Proof.Md5.X86.compressSaved_fits)

theorem common_zero {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {s₁ : State}
    (hesp : s₁.gpr .esp = VG.Proof.Md5.X86.esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = VG.Proof.Md5.X86.saveMem s₀) : VG.Proof.Md5.X86.Common s₀ 0 s₁ := by
  refine ⟨hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact VG.Proof.Md5.X86.saveMem_saved hp⟩
  · rw [hm]; exact (VG.Proof.Md5.X86.saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply VG.Proof.Md5.X86.stateAt_eq hp
    intro k hk
    rw [(VG.Proof.Md5.X86.saveMem_frame hp).readW (VG.Proof.Md5.X86.contains_sub (len := 16) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← VG.Proof.Md5.X86.stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) {s : State} (hc : VG.Proof.Md5.X86.Common s₀ (VG.Proof.Md5.X86.nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have harg : s.mem.readW (addr (VG.Proof.Md5.X86.esp₀ s₀) 16) 32 = VG.Proof.Md5.X86.scr s₀ := hp.arg_frame hc.frame (i := 3) (by decide)
  rw [VG.Proof.Md5.X86.epilogue_eq]
  refine Wp.wp_ldm hc.esp (by rw [hc.rd, hc.wr]; exact hp.in_arg (by omega) (by omega)) fun s₁ u₁ => ?_
  rw [harg] at u₁
  refine Spill.restore_ok VG.Proof.Md5.X86.compressSaved (by decide)
    (fun p h => by rw [u₁.gpr, u₁.rd, u₁.wr, hc.rd, hc.wr]; exact hp.in_scr (compressSaved_fits.1 p h))
    (by rw [u₁.gpr, u₁.mem]; exact hc.saved) fun s' u => WP.block_nil ⟨u.abi (by decide) (by decide)
      (by rw [u₁.other _ (by decide), hc.esp]), by rw [u.mem, u₁.mem]⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Md5.X86.Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Md5.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Md5.X86.save_ok hp) fun s₁ ⟨hesi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Md5.X86.Common s₀ (VG.Proof.Md5.X86.nb s₀)) ?_ fun s₂ hc =>
    WP.mono (VG.Proof.Md5.X86.restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := VG.Proof.Md5.X86.common_zero hp hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Md5.X86.nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [VG.Proof.Md5.X86.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Md5.X86.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Md5.X86.nb s₀ - i ∧ i < VG.Proof.Md5.X86.nb s₀ ∧ VG.Proof.Md5.X86.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Md5.X86.Common s₀ (VG.Proof.Md5.X86.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Md5.X86.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Md5.X86.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Md5.X86.LInv s₀ 0 s₁ :=
      { hc₀ with
        esi := by rw [hesi]; simp [VG.Proof.Md5.X86.blkAddr]
        ebp := by rw [hebp]; simp [VG.Proof.Md5.X86.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Md5.X86.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Md5.X86.satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem sat_pre : Proof.Md5.compressX86.pre VG.Proof.Md5.X86.satState := by
  have a0 : arg VG.Proof.Md5.X86.satState 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Md5.X86.satState 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Md5.X86.satState 2 = 0 := by decide
  have a3 : arg VG.Proof.Md5.X86.satState 3 = 0x3000 := by decide
  have e : argAddr VG.Proof.Md5.X86.satState 0 = 0x4004 := by decide
  simp only [Proof.Md5.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 64], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Md5.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.Md5.X86.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Md5.X86.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Md5.X86.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Md5.compressX86.pre s₁)
    (h₂ : Proof.Md5.compressX86.pre s₂) (hpub : Proof.Md5.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Md5.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := VG.Proof.Md5.X86.pre_of _ h₁; have hp₂ := VG.Proof.Md5.X86.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Md5.X86.wf₀ hp₁, VG.Proof.Md5.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Md5.X86.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Md5.X86.stR, VG.Proof.Md5.X86.scrR, VG.Proof.Md5.X86.st, VG.Proof.Md5.X86.scr, a0, a3]
  · simp only [VG.Proof.Md5.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Md5.X86.compress Proof.Md5.compressX86 :=
  ⟨fun s hs => VG.Proof.Md5.X86.correct (VG.Proof.Md5.X86.pre_of s hs),
    VG.Taint.constantTime (A := taint) VG.Proof.Md5.X86.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Md5.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Md5.X86.satState, VG.Proof.Md5.X86.sat_pre⟩⟩

end VG.Proof.Md5.X86

end
