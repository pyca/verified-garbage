import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha256.X86.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.Contract`. -/
section

/-!
# SHA-256: the x86 (32-bit) contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the x86 (32-bit) implementations of the compression function and of
streaming SHA-256 (`init`/`update`/`finalize`, on the representation
`ReprFrom`), in terms of `Spec/Sha256.lean`.

The shared contracts let the streaming functions write their own argument
area (cdecl passes the arguments in the caller's frame, just above the
return address, and the callee owns them). `update` only reads it, and its
contract here says so; `finalize` may write it, as HMAC's `finalize`, which
reuses its code, does. `update` and `finalize` call the compression
function, using the 20 bytes of stack below the return address.
-/

namespace VG.Proof.Sha256

open Spec.Sha256

open X86 in
/-- x86 (32-bit) contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl): updates the hash value at `state`
with the `n` 64-byte blocks at `blocks`.

The code may read the arguments (16 bytes above the return address) and
`blocks` (`64 * n` bytes), and read and write `state` (32 bytes) and
`scratch` (112 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the blocks, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers and `n`) are public; the hash value
and the blocks are secret. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 112 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
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
/-- x86 (32-bit) contract for `vg_sha256_init(state: *mut [u8; 96])` and
`vg_sha224_init`, which store the initial hash value `iv`, whose
argument is on the stack (cdecl): makes the streaming state at `state`
represent the empty message, hashed from `iv`.

The code may read the argument (4 bytes above the return address) and write
`state` (96 bytes), which may not overlap the argument or the return address;
nothing may wrap around the end of the (32-bit) address space. `esp` and the
pointer are public. -/
def initX86 (iv : HashValue) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := ReprFrom iv s'.mem ((arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

open X86 in
/-- x86 (32-bit) contract for
`vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `data`, `len`, `scratch`): if the streaming state at `state`
represents a message `m` of `count` bytes (modulo 2⁶⁴), hashed from any
initial hash value `iv`, then afterwards it represents `m` followed by the
`len` bytes at `data`, from `iv`.

The code may read the arguments (24 bytes above the return address) and
`data` (`len` bytes), and read and write `state` (96 bytes) and `scratch`
(160 bytes, whose contents on exit are unspecified). The writable buffers
may not overlap each other, the data or the arguments; none of them may
overlap the return address or the 20 bytes of stack below it; and nothing
may wrap around the end of the (32-bit) address space. `esp`, the pointers,
`count` and `len` are public; the state and the data are secret. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 160⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 160 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ iv m, ReprFrom iv s.mem ((arg s 0).setWidth 64) m → VG.Proof.Sha256.countX86 s = BitVec.ofNat 64 m.length →
    ReprFrom iv s'.mem ((arg s 0).setWidth 64)
      (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for
`vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 20])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `out`, `scratch`): if the streaming state at `state` represents a
message `m` of `count` bytes (modulo 2⁶⁴), hashed from the initial hash value
`iv`, writes the final hash value of `m` from `iv` to `out` (the SHA-256
digest if `iv` is `H0`).

The code may read and write the arguments (20 bytes above the return
address, whose contents on exit are unspecified), `state` (96 bytes, whose
contents on exit are unspecified), `out` (32 bytes) and `scratch` (160
bytes, whose contents on exit are unspecified). These may not overlap each
other or the return address; none of the buffers may overlap the 20 bytes
of stack below the return address; and nothing may wrap around the end of
the (32-bit) address space. `esp`, the pointers and `count` are public; the
state is secret. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 160⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 160 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ iv m, ReprFrom iv s.mem ((arg s 0).setWidth 64) m → VG.Proof.Sha256.countX86 s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem ((arg s 3).setWidth 64) 32 = Spec.Sha256.finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Sha256

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.Lit`. -/
section

/-!
# SHA-256 on X86: the code as literals
-/

namespace VG

materialize_code Impl.Sha256.X86.compress
materialize_code Impl.Sha256.X86.Stream.update
materialize_code Impl.Sha256.X86.Stream.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.Compress`. -/
section

/-!
# SHA-256 compression function on x86 (32-bit): the message schedule and the rounds
-/

namespace VG.Proof.Sha256.X86

open VG VG.X86 VG.Impl.Sha256.X86
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The working variables `v` are in the scratch buffer `scr` of memory `m`, at
the offsets of round `t`. -/
def Vars (t : Nat) (scr : BitVec 32) (m : Mem) (v : HashValue) : Prop :=
  m.readW (addr scr (var t 0)) 32 = v[0] ∧ m.readW (addr scr (var t 1)) 32 = v[1] ∧
  m.readW (addr scr (var t 2)) 32 = v[2] ∧ m.readW (addr scr (var t 3)) 32 = v[3] ∧
  m.readW (addr scr (var t 4)) 32 = v[4] ∧ m.readW (addr scr (var t 5)) 32 = v[5] ∧
  m.readW (addr scr (var t 6)) 32 = v[6] ∧ m.readW (addr scr (var t 7)) 32 = v[7]

/-- The pointers, the count and `esp`: never written by the rounds. -/
def pubRegs : List Reg := [.esi, .edi, .ebp, .esp]

/-- Facts about the scratch buffer at `scr`, for a memory access `[scr + d]`. -/
structure Scratch (s : State) (scr : BitVec 32) : Prop where
  fits : scr.toNat + 112 ≤ 2 ^ 32
  rd : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr scr d) 4
  wr : ∀ d, d + 4 ≤ 112 → InRegions s.wr (addr scr d) 4

theorem scr_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d e : Nat} (hd : d + 4 ≤ 112)
    (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr scr e) 4 (addr scr d) 4 := by
  rw [addr_eq (by bdd_omega), addr_eq (by bdd_omega)]
  exact Offset.sep _ (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr d) x).readW (addr scr e) 32 = m.readW (addr scr e) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Sha256.X86.scr_sep h hd he hde) (by decide)

theorem slot_lt (j : Nat) : slot j + 4 ≤ 64 := by simp only [slot]; omega

/-- The working variables move one slot along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; omega

/-- The working variables of a round are in the scratch buffer, in separate words (stated
for each pair in both orders, for rewriting). -/
theorem round_sep (t : Nat) :
    (∀ x ∈ [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7], x + 4 ≤ 112) ∧
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7].Pairwise
      (fun x y => x + 4 ≤ y ∨ y + 4 ≤ x) ∧
    [var t 7, var t 6, var t 5, var t 4, var t 3, var t 2, var t 1, var t 0].Pairwise
      fun x y => x + 4 ≤ y ∨ y + 4 ≤ x := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by bdd_omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any offsets `a … h` of the
working variables (which `round_sep` says are in separate words). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hS : VG.Proof.Sha256.X86.Scratch s scr) (hv : VG.Proof.Sha256.X86.Vars t scr s.mem v) (hesi : s.gpr .esi = scr)
    (hw : s.mem.readW (addr scr (slot t)) 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      VG.Proof.Sha256.X86.Vars (t + 1) scr s'.mem (roundKW v (K t) w) ∧
      (∃ x y : Word, s'.mem = (s.mem.writeW (addr scr (var t 3)) x).writeW (addr scr (var t 7)) y) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ VG.Proof.Sha256.X86.pubRegs, s'.gpr r = s.gpr r := by
  have hin := hS.rd; have hout := hS.wr
  have hrw := VG.Proof.Sha256.X86.readW_writeW_scr hS.fits
  have hs := hin (slot t) (by have := VG.Proof.Sha256.X86.slot_lt t; omega)
  have hsep := VG.Proof.Sha256.X86.round_sep t
  simp only [VG.Proof.Sha256.X86.Vars, VG.Proof.Sha256.X86.var_succ_zero, VG.Proof.Sha256.X86.var_succ t _ (show 0 < 7 by bdd_omega),
    VG.Proof.Sha256.X86.var_succ t _ (show 1 < 7 by bdd_omega), VG.Proof.Sha256.X86.var_succ t _ (show 2 < 7 by bdd_omega),
    VG.Proof.Sha256.X86.var_succ t _ (show 3 < 7 by bdd_omega), VG.Proof.Sha256.X86.var_succ t _ (show 4 < 7 by bdd_omega),
    VG.Proof.Sha256.X86.var_succ t _ (show 5 < 7 by bdd_omega), VG.Proof.Sha256.X86.var_succ t _ (show 6 < 7 by bdd_omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, List.Pairwise.nil, and_true, or_false,
    forall_eq] at hsep
  simp only
    [hsep, runBlock_cons, runBlock_nil, runStep_some, exec, execAlu, execShift, readSrc, VG.Proof.Sha256.X86.ea_at, sc,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, not_false_eq_true,
    reduceCtorEq,
    State.load32, State.store32, ite_true, ite_false,
    hesi, hin, hout, hs, hrw, Mem.readW_writeW_self32, h0, h1, h2, h3, h4, h5, h6, h7, hw,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨_, _, rfl⟩, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · simp only [VG.Proof.Sha256.X86.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        not_false_eq_true, reduceCtorEq]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32) (hS : VG.Proof.Sha256.X86.Scratch s scr)
    (hedi : s.gpr .edi = bp) (hesi : s.gpr .esi = scr)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (addr bp (4 * t)) 4)
    (hblk : t < 16 → bswap (s.mem.readW (addr bp (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (addr scr (slot t)) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ VG.Proof.Sha256.X86.pubRegs, s'.gpr r = s.gpr r := by
  have hin : ∀ j, InRegions (s.rd ++ s.wr) (addr scr (slot j)) 4 :=
    fun j => hS.rd _ (by have := VG.Proof.Sha256.X86.slot_lt j; omega)
  have hout : ∀ j, InRegions s.wr (addr scr (slot j)) 4 :=
    fun j => hS.wr _ (by have := VG.Proof.Sha256.X86.slot_lt j; omega)
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.X86.schedule, ht, ite_true]
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec, readSrc,
      VG.Proof.Sha256.X86.ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq,
      State.load32, State.store32, hedi, hesi, hi, hout, ite_true, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, fun r hr => ?_⟩
    simp only [VG.Proof.Sha256.X86.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_setReg_of_ne, not_false_eq_true, reduceCtorEq]
  · have hw := hwin (by bdd_omega)
    have e2 := hw (t - 2) (by bdd_omega) (by bdd_omega)
    have e7 := hw (t - 7) (by bdd_omega) (by bdd_omega)
    have e15 := hw (t - 15) (by bdd_omega) (by bdd_omega)
    have e16 := hw (t - 16) (by bdd_omega) (by bdd_omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha256.X86.schedule, ht, ite_false, sc]
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec, execAlu,
      execShift, readSrc, VG.Proof.Sha256.X86.ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
      RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self,
      not_false_eq_true, reduceCtorEq, State.load32, State.store32, hesi, hin, hout,
      ite_true, ite_false, e2, e7, e15, e16, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, trivial, trivial, fun r hr => ?_⟩
    rotate_right
    · simp only [VG.Proof.Sha256.X86.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
          not_false_eq_true, reduceCtorEq]
    rw [W_ge M (t := t) (by bdd_omega), ssig1_eq, ssig0_eq]

/-! ## The 64 rounds -/

/-- The part of the scratch buffer the rounds write: the window and the working variables. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 96⟩

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem work_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 96) :
    (VG.Proof.Sha256.X86.workRegion scr).Contains (addr scr d) (32 / 8) := by
  rw [addr_eq (by bdd_omega)]; exact VG.Proof.Sha256.X86.contains_offset hd (by bdd_omega)

theorem var_lt (t k : Nat) : 64 ≤ var t k ∧ var t k + 4 ≤ 96 := by
  simp only [var]; omega

/-- The variables are unaffected by a write elsewhere in the scratch buffer. -/
theorem Vars.write {t : Nat} {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {m : Mem}
    {v : HashValue} (hv : VG.Proof.Sha256.X86.Vars t scr m v) {d : Nat} (hd : d + 4 ≤ 112)
    (hsep : ∀ k, d + 4 ≤ var t k ∨ var t k + 4 ≤ d) (x : Word) :
    VG.Proof.Sha256.X86.Vars t scr (m.writeW (addr scr d) x) v := by
  have e : ∀ k, (m.writeW (addr scr d) x).readW (addr scr (var t k)) 32 =
      m.readW (addr scr (var t k)) 32 := fun k =>
    VG.Proof.Sha256.X86.readW_writeW_scr h m x hd (by have := VG.Proof.Sha256.X86.var_lt t k; omega) (hsep k)
  simp only [VG.Proof.Sha256.X86.Vars, e]
  exact hv

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : VG.Proof.Sha256.X86.Vars t scr s.mem (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ VG.Proof.Sha256.X86.pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [VG.Proof.Sha256.X86.workRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j

theorem Scratch.congr {s s' : State} {scr : BitVec 32} (h : VG.Proof.Sha256.X86.Scratch s scr) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.Sha256.X86.Scratch s' scr :=
  ⟨h.fits, by rw [hrd, hwr]; exact h.rd, by rw [hwr]; exact h.wr⟩

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hS : VG.Proof.Sha256.X86.Scratch sB scr) (hedi : sB.gpr .edi = bp) (hesi : sB.gpr .esi = scr)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (addr bp (4 * t)) 4)
    (hblk : ∀ m, Frame [VG.Proof.Sha256.X86.workRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap (m.readW (addr bp (4 * t)) 32) = W M t)
    (h0 : VG.Proof.Sha256.X86.Vars 0 scr sB.mem H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (VG.Proof.Sha256.X86.RInv H M scr sB t) := by
  have hfits := hS.fits
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by bdd_omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_edi : s.gpr .edi = bp := (hs.pub .edi (by decide)).trans hedi
    have hs_esi : s.gpr .esi = scr := (hs.pub .esi (by decide)).trans hesi
    refine WP.mono (VG.Proof.Sha256.X86.schedule_ok t s M bp scr (hS.congr hs.rd hs.wr) hs_edi hs_esi
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hslot := VG.Proof.Sha256.X86.slot_lt t
    have hframe₁ : Frame [VG.Proof.Sha256.X86.workRegion scr] sB.mem s₁.mem := by
      rw [hm₁]; exact hs.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86.work_contains hfits (by bdd_omega))
    have hself : s₁.mem.readW (addr scr (slot t)) 32 = W M t := by
      rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    have hv₁ : VG.Proof.Sha256.X86.Vars t scr s₁.mem (VG.Spec.Sha256.rounds H M t) := by
      rw [hm₁]
      exact hs.vars.write hfits (by bdd_omega) (fun k => .inl (by have := VG.Proof.Sha256.X86.var_lt t k; omega)) _
    have hesi₁ : s₁.gpr .esi = scr := by rw [hr₁ .esi (by decide), hs_esi]
    refine WP.mono (VG.Proof.Sha256.X86.round_ok t s₁ _ _ scr (hS.congr (by rw [hrd₁, hs.rd]) (by rw [hwr₁, hs.wr]))
      hv₁ hesi₁ hself) fun s₂ ⟨hv₂, ⟨x, y, hm₂⟩, hrd₂, hwr₂, hr₂⟩ => ?_
    have h3 := VG.Proof.Sha256.X86.var_lt t 3
    have h7 := VG.Proof.Sha256.X86.var_lt t 7
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · rw [hr₂ r hr, hr₁ r hr, hs.pub r hr]
    · rw [hm₂]
      exact (hframe₁.writeW (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86.work_contains hfits (by bdd_omega))).writeW
        (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86.work_contains hfits (by bdd_omega))
    · intro j hj hj'
      have hsj := VG.Proof.Sha256.X86.slot_lt j
      rw [hm₂, VG.Proof.Sha256.X86.readW_writeW_scr hfits _ _ (by bdd_omega) (by bdd_omega) (.inr (by bdd_omega)),
        VG.Proof.Sha256.X86.readW_writeW_scr hfits _ _ (by bdd_omega) (by bdd_omega) (.inr (by bdd_omega))]
      by_cases hjt : j = t
      · subst hjt; exact hself
      · rw [hm₁, VG.Proof.Sha256.X86.readW_writeW_scr hfits _ _ (by bdd_omega) (by bdd_omega) ?_]
        · exact hs.win j (by bdd_omega) (by bdd_omega)
        · simp only [slot] at hsj hslot ⊢; omega

end VG.Proof.Sha256.X86

/-!
# SHA-256 compression function on x86 (32-bit): the whole function
-/

namespace VG.Proof.Sha256.X86

open VG VG.X86 VG.Impl.Sha256.X86
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(VG.Proof.Sha256.X86.st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(VG.Proof.Sha256.X86.bp s₀).setWidth 64, 64 * VG.Proof.Sha256.X86.nb s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.Sha256.X86.scr s₀).setWidth 64, 112⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.Sha256.X86.esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((VG.Proof.Sha256.X86.st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Sha256.X86.bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := addr (VG.Proof.Sha256.X86.st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Sha256.X86.blR s₀, VG.Proof.Sha256.X86.argR s₀]
  wr : s₀.wr = [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀]
  st_scr : (VG.Proof.Sha256.X86.stR s₀).Disjoint (VG.Proof.Sha256.X86.scrR s₀)
  blk_st : (VG.Proof.Sha256.X86.blR s₀).Disjoint (VG.Proof.Sha256.X86.stR s₀)
  blk_scr : (VG.Proof.Sha256.X86.blR s₀).Disjoint (VG.Proof.Sha256.X86.scrR s₀)
  arg_st : (VG.Proof.Sha256.X86.argR s₀).Disjoint (VG.Proof.Sha256.X86.stR s₀)
  arg_scr : (VG.Proof.Sha256.X86.argR s₀).Disjoint (VG.Proof.Sha256.X86.scrR s₀)
  ret_st : (VG.Proof.Sha256.X86.retR s₀).Disjoint (VG.Proof.Sha256.X86.stR s₀)
  ret_scr : (VG.Proof.Sha256.X86.retR s₀).Disjoint (VG.Proof.Sha256.X86.scrR s₀)
  st_fits : (VG.Proof.Sha256.X86.st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Sha256.X86.bp s₀).toNat + 64 * VG.Proof.Sha256.X86.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Sha256.X86.scr s₀).toNat + 112 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Sha256.X86.esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressX86.pre s₀) : VG.Proof.Sha256.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact VG.Proof.Sha256.X86.contains_offset h ho

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 :=
  rfl

namespace Pre
variable {s₀ : State} (h : VG.Proof.Sha256.X86.Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 8) :
    VG.Proof.Sha256.X86.stAddr s₀ k = (VG.Proof.Sha256.X86.st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (VG.Proof.Sha256.X86.esp₀ s₀) d = (VG.Proof.Sha256.X86.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < VG.Proof.Sha256.X86.nb s₀) (ht : t < 16) :
    addr (VG.Proof.Sha256.X86.blkAddr s₀ i) (4 * t) =
      (VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (VG.Proof.Sha256.X86.bp s₀).isLt; omega)]
  have e : (VG.Proof.Sha256.X86.blkAddr s₀ i).setWidth 64 = (VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := VG.Proof.Sha256.X86.bp s₀) (k := 64 * i) (by bdd_omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 112) :
    addr (VG.Proof.Sha256.X86.scr s₀) d = (VG.Proof.Sha256.X86.scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega)

theorem scratch : VG.Proof.Sha256.X86.Scratch s₀ (VG.Proof.Sha256.X86.scr s₀) :=
  ⟨h.scr_fits, fun d hd => ⟨VG.Proof.Sha256.X86.scrR s₀, by simp [h.wr], VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (h.scr_eq (by bdd_omega))⟩,
    fun d hd => ⟨VG.Proof.Sha256.X86.scrR s₀, by simp [h.wr], VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (h.scr_eq (by bdd_omega))⟩⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Sha256.X86.argR s₀).Contains (addr (VG.Proof.Sha256.X86.esp₀ s₀) d) 4 := by
  simp only [Region.Contains, argAddr]
  rw [show (VG.Proof.Sha256.X86.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Sha256.X86.esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by bdd_omega), h.argAddr_eq (by bdd_omega)]
  have := h.esp_fits
  rw [Offset.add_sub_add _ hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)]
  omega

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Sha256.X86.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Sha256.X86.argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Sha256.X86.argR s₀) := by
  simp only [VG.Proof.Sha256.X86.argR, argAddr]
  rw [show (VG.Proof.Sha256.X86.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Sha256.X86.esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by bdd_omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (VG.Proof.Sha256.X86.esp₀ s₀) (4 + 4 * i)
    from rfl, h.argAddr_eq (by bdd_omega)]
  exact Offset.sub _ (by bdd_omega) (by bdd_omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < VG.Proof.Sha256.X86.nb s₀) (ht : t < 16) :
    (VG.Proof.Sha256.X86.blR s₀).Contains (addr (VG.Proof.Sha256.X86.blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show (VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    (VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact VG.Proof.Sha256.X86.contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < VG.Proof.Sha256.X86.nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Sha256.X86.blkAddr s₀ i) (4 * t)) 4 :=
  ⟨VG.Proof.Sha256.X86.blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {d e : Nat} (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (VG.Proof.Sha256.X86.st s₀) d) 4 (addr (VG.Proof.Sha256.X86.st s₀) e) 4 := by
  rw [addr_eq (by have := hp.st_fits; omega), addr_eq (by have := hp.st_fits; omega)]
  exact Offset.sep _ hde (by bdd_omega) (by bdd_omega)

/-- Reading the hash value at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (VG.Proof.Sha256.X86.st s₀) e) v).readW (addr (VG.Proof.Sha256.X86.st s₀) d) 32 = m.readW (addr (VG.Proof.Sha256.X86.st s₀) d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Sha256.X86.st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {d : Nat} (hd : d < 32) :
    addr (VG.Proof.Sha256.X86.st s₀) d = (VG.Proof.Sha256.X86.st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem st_scr_sep {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {e d : Nat} (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    Mem.Sep (addr (VG.Proof.Sha256.X86.st s₀) e) 4 (addr (VG.Proof.Sha256.X86.scr s₀) d) 4 :=
  hp.st_scr.sep (VG.Proof.Sha256.X86.contains_sub he (by bdd_omega) (VG.Proof.Sha256.X86.st_eq hp (by bdd_omega)))
    (VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (hp.scr_eq (by bdd_omega)))

/-- Reading the hash value after writing the scratch buffer. -/
theorem readW_writeW_scr_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (VG.Proof.Sha256.X86.scr s₀) d) v).readW (addr (VG.Proof.Sha256.X86.st s₀) e) 32 = m.readW (addr (VG.Proof.Sha256.X86.st s₀) e) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Sha256.X86.st_scr_sep hp he hd) (by decide)

/-- Reading the scratch buffer after writing the hash value. -/
theorem readW_writeW_st_scr {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (VG.Proof.Sha256.X86.st s₀) e) v).readW (addr (VG.Proof.Sha256.X86.scr s₀) d) 32 = m.readW (addr (VG.Proof.Sha256.X86.scr s₀) d) 32 :=
  Mem.readW_writeW_sep (fun x h₁ h₂ => VG.Proof.Sha256.X86.st_scr_sep hp he hd x h₂ h₁) (by decide)

theorem in_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Sha256.X86.st s₀) d) 4 :=
  ⟨VG.Proof.Sha256.X86.stR s₀, by simp [hp.wr], VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (VG.Proof.Sha256.X86.st_eq hp (by bdd_omega))⟩

theorem out_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s₀.wr (addr (VG.Proof.Sha256.X86.st s₀) d) 4 :=
  ⟨VG.Proof.Sha256.X86.stR s₀, by simp [hp.wr], VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (VG.Proof.Sha256.X86.st_eq hp (by bdd_omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (VG.Proof.Sha256.X86.stAddr s₀ k) 32 = v[k]) :
    stateAt m ((VG.Proof.Sha256.X86.st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m ((VG.Proof.Sha256.X86.st s₀).setWidth 64))[k] = m.readW (VG.Proof.Sha256.X86.stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers and their slots in the scratch buffer. -/
def compressSaved : Spill.Slots := [(.ebx, 96), (.esi, 100), (.edi, 104), (.ebp, 108)]

theorem compressSaved_fits : Spill.Fits 112 VG.Proof.Sha256.X86.compressSaved := by decide

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (VG.Proof.Sha256.X86.scr s₀)) s₀.gpr VG.Proof.Sha256.X86.compressSaved

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.Sha256.X86.scr s₀
  esp : s.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((VG.Proof.Sha256.X86.st s₀).setWidth 64) =
    compressBlocks (VG.Proof.Sha256.X86.H₀ s₀) s₀.mem ((VG.Proof.Sha256.X86.bp s₀).setWidth 64) i
  saved : VG.Proof.Sha256.X86.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86.Common s₀ i s where
  edi : s.gpr .edi = VG.Proof.Sha256.X86.blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.Sha256.X86.nb s₀ - i)

/-! ## One block -/

/-- Word `k` of the load: copy `state[k]` to its working variable. -/
def ld (k : Nat) : List Instr :=
  [.mov .ebx (.mem ⟨.eax, 4 * k⟩), .store ⟨.esi, 64 + 4 * k⟩ .ebx]

/-- Words `0 … j-1` of the load. -/
def ldTo (j : Nat) : List Instr := (List.range j).flatMap VG.Proof.Sha256.X86.ld

theorem ldTo_succ (j : Nat) : VG.Proof.Sha256.X86.ldTo (j + 1) = VG.Proof.Sha256.X86.ldTo j ++ VG.Proof.Sha256.X86.ld j := by
  simp [VG.Proof.Sha256.X86.ldTo, List.range_succ, List.flatMap_append]

theorem load_eq : load = ([.mov .eax (.mem ⟨.esp, 4⟩)] : List Instr) ++ VG.Proof.Sha256.X86.ldTo 8 := by
  decide

/-- Word `k` of the update: `state[k] := var k + state[k]`. -/
def upd (k : Nat) : List Instr :=
  [.mov .ebx (.mem ⟨.esi, 64 + 4 * k⟩), .alu .add .ebx (.mem ⟨.eax, 4 * k⟩),
   .store ⟨.eax, 4 * k⟩ .ebx]

/-- Words `0 … j-1` of the update. -/
def updTo (j : Nat) : List Instr := (List.range j).flatMap VG.Proof.Sha256.X86.upd

theorem updTo_succ (j : Nat) : VG.Proof.Sha256.X86.updTo (j + 1) = VG.Proof.Sha256.X86.updTo j ++ VG.Proof.Sha256.X86.upd j := by
  simp [VG.Proof.Sha256.X86.updTo, List.range_succ, List.flatMap_append]

theorem update_eq : update ++ advance = ([.mov .eax (.mem ⟨.esp, 4⟩)] : List Instr) ++ (VG.Proof.Sha256.X86.updTo 8 ++ advance) := by
  decide

theorem vars0 (scr : BitVec 32) (m : Mem) (v : HashValue) : VG.Proof.Sha256.X86.Vars 0 scr m v ↔
    m.readW (addr scr 64) 32 = v[0] ∧ m.readW (addr scr 68) 32 = v[1] ∧
    m.readW (addr scr 72) 32 = v[2] ∧ m.readW (addr scr 76) 32 = v[3] ∧
    m.readW (addr scr 80) 32 = v[4] ∧ m.readW (addr scr 84) 32 = v[5] ∧
    m.readW (addr scr 88) 32 = v[6] ∧ m.readW (addr scr 92) 32 = v[7] := Iff.rfl

/-- Eight words written in order to the working variables. -/
def writeVars (scr : BitVec 32) (m : Mem) (v : HashValue) : Mem :=
  ((((((((m.writeW (addr scr 64) v[0]).writeW (addr scr 68) v[1]).writeW (addr scr 72) v[2]).writeW
    (addr scr 76) v[3]).writeW (addr scr 80) v[4]).writeW (addr scr 84) v[5]).writeW
    (addr scr 88) v[6]).writeW (addr scr 92) v[7])

set_option simprocs false in
theorem vars_writeVars {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (v : HashValue) :
    VG.Proof.Sha256.X86.Vars 0 scr (VG.Proof.Sha256.X86.writeVars scr m v) v := by
  have hrw := VG.Proof.Sha256.X86.readW_writeW_scr h
  rw [VG.Proof.Sha256.X86.vars0]
  simp only [VG.Proof.Sha256.X86.writeVars]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (disch := decide) only [Mem.readW_writeW_self32, hrw]

theorem frame_writeVars {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (v : HashValue) :
    Frame [VG.Proof.Sha256.X86.workRegion scr] m (VG.Proof.Sha256.X86.writeVars scr m v) := by
  have c : ∀ d, d + 4 ≤ 96 → (VG.Proof.Sha256.X86.workRegion scr).Contains (addr scr d) (32 / 8) :=
    fun d hd => VG.Proof.Sha256.X86.work_contains h hd
  have mm := List.mem_singleton_self (VG.Proof.Sha256.X86.workRegion scr)
  simp only [VG.Proof.Sha256.X86.writeVars]
  exact ((((((((Frame.refl _ _).writeW mm _ (c 64 (by bdd_omega))).writeW mm _ (c 68 (by bdd_omega))).writeW
    mm _ (c 72 (by bdd_omega))).writeW mm _ (c 76 (by bdd_omega))).writeW mm _ (c 80 (by bdd_omega))).writeW
    mm _ (c 84 (by bdd_omega))).writeW mm _ (c 88 (by bdd_omega))).writeW mm _ (c 92 (by bdd_omega))

theorem ld_ok (k : Nat) {s : State} {p q : BitVec 32} (heax : s.gpr .eax = p)
    (hesi : s.gpr .esi = q) (hi : InRegions (s.rd ++ s.wr) (addr p (4 * k)) 4)
    (ho : InRegions s.wr (addr q (64 + 4 * k)) 4) :
    WP isa (.block (VG.Proof.Sha256.X86.ld k)) s fun s' =>
      s'.mem = s.mem.writeW (addr q (64 + 4 * k)) (s.mem.readW (addr p (4 * k)) 32) ∧
      (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, and_self, VG.Proof.Sha256.X86.ld, runBlock_cons, runBlock_nil, runStep_some, exec,
    readSrc, ea_mk, State.setReg, State.load32, State.store32, heax, hesi, hi, ho,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The working variables at `q` after loading words `0 … j-1` of the hash value at `p`. -/
def copyWords (p q : BitVec 32) (m : Mem) : Nat → Mem
  | 0 => m
  | j + 1 => (VG.Proof.Sha256.X86.copyWords p q m j).writeW (addr q (64 + 4 * j)) (m.readW (addr p (4 * j)) 32)

theorem copyWords_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ 8, (VG.Proof.Sha256.X86.copyWords (VG.Proof.Sha256.X86.st s₀) (VG.Proof.Sha256.X86.scr s₀) m j).readW (addr (VG.Proof.Sha256.X86.st s₀) (4 * i)) 32 =
      m.readW (addr (VG.Proof.Sha256.X86.st s₀) (4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [VG.Proof.Sha256.X86.copyWords, VG.Proof.Sha256.X86.readW_writeW_scr_st hp _ _ (by bdd_omega) (by bdd_omega)]
    exact VG.Proof.Sha256.X86.copyWords_st hp m hi j (by bdd_omega)

theorem ldTo_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s : State} (heax : s.gpr .eax = VG.Proof.Sha256.X86.st s₀)
    (hesi : s.gpr .esi = VG.Proof.Sha256.X86.scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∀ j ≤ 8, WP isa (.block (VG.Proof.Sha256.X86.ldTo j)) s fun s' =>
      s'.mem = VG.Proof.Sha256.X86.copyWords (VG.Proof.Sha256.X86.st s₀) (VG.Proof.Sha256.X86.scr s₀) s.mem j ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil (M := isa) ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | j + 1, hj => by
    rw [VG.Proof.Sha256.X86.ldTo_succ, WP.block_append_iff]
    refine WP.mono (VG.Proof.Sha256.X86.ldTo_ok hp heax hesi hrd hwr j (by bdd_omega))
      fun s₁ ⟨hm₁, hr₁, hrd₁, hwr₁⟩ => ?_
    refine WP.mono (VG.Proof.Sha256.X86.ld_ok j (p := VG.Proof.Sha256.X86.st s₀) (q := VG.Proof.Sha256.X86.scr s₀)
      (by rw [hr₁ .eax (by decide), heax]) (by rw [hr₁ .esi (by decide), hesi])
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact VG.Proof.Sha256.X86.in_st hp (by bdd_omega))
      (by rw [hwr₁, hwr]; exact hp.scratch.wr _ (by bdd_omega))) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, hr₁ r hr], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
    rw [hm₂, hm₁, VG.Proof.Sha256.X86.copyWords_st hp _ (by bdd_omega) j (by bdd_omega)]
    rfl

theorem load_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s : State} (hesp : s.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀)
    (hesi : s.gpr .esi = VG.Proof.Sha256.X86.scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) 4) 32 = VG.Proof.Sha256.X86.st s₀) :
    WP isa (.block load) s fun s₁ =>
      s₁.mem = VG.Proof.Sha256.X86.writeVars (VG.Proof.Sha256.X86.scr s₀) s.mem (stateAt s.mem ((VG.Proof.Sha256.X86.st s₀).setWidth 64)) ∧
      (∀ r ∈ VG.Proof.Sha256.X86.pubRegs, s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha256.X86.esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by bdd_omega) (by bdd_omega)
  -- `mov eax, [esp + 4]`
  have h₁ : WP isa (.block [.mov .eax (.mem ⟨.esp, 4⟩)]) s fun s₁ =>
      s₁.gpr .eax = VG.Proof.Sha256.X86.st s₀ ∧ (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [↓reduceIte, and_self, runBlock_cons, runBlock_nil, runStep_some, exec,
      readSrc, ea_mk, State.setReg, State.load32, hesp, ia, harg, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  rw [VG.Proof.Sha256.X86.load_eq, WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨he₁, hr₁, hm₁, hrd₁, hwr₁⟩ => ?_
  refine WP.mono (VG.Proof.Sha256.X86.ldTo_ok hp he₁ (by rw [hr₁ .esi (by decide), hesi]) (hrd₁.trans hrd)
    (hwr₁.trans hwr) 8 (Nat.le_refl _)) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁]
    simp only [VG.Proof.Sha256.X86.copyWords, VG.Proof.Sha256.X86.writeVars, VG.Proof.Sha256.X86.stateAt_get hp _ (show 0 < 8 by decide),
      VG.Proof.Sha256.X86.stateAt_get hp _ (show 1 < 8 by decide), VG.Proof.Sha256.X86.stateAt_get hp _ (show 2 < 8 by decide),
      VG.Proof.Sha256.X86.stateAt_get hp _ (show 3 < 8 by decide), VG.Proof.Sha256.X86.stateAt_get hp _ (show 4 < 8 by decide),
      VG.Proof.Sha256.X86.stateAt_get hp _ (show 5 < 8 by decide), VG.Proof.Sha256.X86.stateAt_get hp _ (show 6 < 8 by decide),
      VG.Proof.Sha256.X86.stateAt_get hp _ (show 7 < 8 by decide), VG.Proof.Sha256.X86.stAddr, Nat.reduceMul, Nat.reduceAdd]
  · simp only [VG.Proof.Sha256.X86.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [hr₂ _ (by decide), hr₁ _ (by decide)]

/-- Eight words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (VG.Proof.Sha256.X86.st s₀)
  ((((((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3]).writeW
    (a 16) v[4]).writeW (a 20) v[5]).writeW (a 24) v[6]).writeW (a 28) v[7])

theorem stateAt_writeState {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (VG.Proof.Sha256.X86.writeState s₀ m v) ((VG.Proof.Sha256.X86.st s₀).setWidth 64) = v := by
  apply VG.Proof.Sha256.X86.stateAt_eq hp
  intro k hk
  simp only [VG.Proof.Sha256.X86.writeState, VG.Proof.Sha256.X86.stAddr]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := decide) only [Nat.reduceMul, Mem.readW_writeW_self32,
    VG.Proof.Sha256.X86.readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {m m' : Mem} (h : Frame [VG.Proof.Sha256.X86.stR s₀] m m')
    (v : HashValue) : Frame [VG.Proof.Sha256.X86.stR s₀] m (VG.Proof.Sha256.X86.writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 32 → (VG.Proof.Sha256.X86.stR s₀).Contains (addr (VG.Proof.Sha256.X86.st s₀) d) (32 / 8) :=
    fun d hd => VG.Proof.Sha256.X86.contains_sub hd (by bdd_omega) (VG.Proof.Sha256.X86.st_eq hp (by bdd_omega))
  simp only [VG.Proof.Sha256.X86.writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _
    (c 12 ?_)).writeW ?_ _ (c 16 ?_)).writeW ?_ _ (c 20 ?_)).writeW ?_ _ (c 24 ?_)).writeW ?_ _
    (c 28 ?_) <;>
  simp

theorem upd_ok (k : Nat) {s : State} {p q : BitVec 32} (heax : s.gpr .eax = p)
    (hesi : s.gpr .esi = q) (hv : InRegions (s.rd ++ s.wr) (addr q (64 + 4 * k)) 4)
    (hh : InRegions (s.rd ++ s.wr) (addr p (4 * k)) 4) (ho : InRegions s.wr (addr p (4 * k)) 4) :
    WP isa (.block (VG.Proof.Sha256.X86.upd k)) s fun s' =>
      s'.mem = s.mem.writeW (addr p (4 * k))
        (s.mem.readW (addr q (64 + 4 * k)) 32 + s.mem.readW (addr p (4 * k)) 32) ∧
      (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, and_self, VG.Proof.Sha256.X86.upd, runBlock_cons, runBlock_nil, runStep_some, exec,
    execAlu, readSrc, ea_mk, State.setReg, arithFlags, State.setFlags, State.load32, State.store32,
    heax, hesi, hv, hh, ho, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The hash value at `p` after updating words `0 … j-1` from the variables at `q`. -/
def writeWords (p q : BitVec 32) (m : Mem) : Nat → Mem
  | 0 => m
  | j + 1 => (VG.Proof.Sha256.X86.writeWords p q m j).writeW (addr p (4 * j))
      (m.readW (addr q (64 + 4 * j)) 32 + m.readW (addr p (4 * j)) 32)

theorem writeWords_scr {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ 8, (VG.Proof.Sha256.X86.writeWords (VG.Proof.Sha256.X86.st s₀) (VG.Proof.Sha256.X86.scr s₀) m j).readW (addr (VG.Proof.Sha256.X86.scr s₀) (64 + 4 * i)) 32 =
      m.readW (addr (VG.Proof.Sha256.X86.scr s₀) (64 + 4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [VG.Proof.Sha256.X86.writeWords, VG.Proof.Sha256.X86.readW_writeW_st_scr hp _ _ (by bdd_omega) (by bdd_omega)]
    exact VG.Proof.Sha256.X86.writeWords_scr hp m hi j (by bdd_omega)

theorem writeWords_st {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ i, (VG.Proof.Sha256.X86.writeWords (VG.Proof.Sha256.X86.st s₀) (VG.Proof.Sha256.X86.scr s₀) m j).readW (addr (VG.Proof.Sha256.X86.st s₀) (4 * i)) 32 =
      m.readW (addr (VG.Proof.Sha256.X86.st s₀) (4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [VG.Proof.Sha256.X86.writeWords, VG.Proof.Sha256.X86.readW_writeW_st hp _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
    exact VG.Proof.Sha256.X86.writeWords_st hp m hi j (by bdd_omega)

theorem updTo_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s : State} (heax : s.gpr .eax = VG.Proof.Sha256.X86.st s₀)
    (hesi : s.gpr .esi = VG.Proof.Sha256.X86.scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∀ j ≤ 8, WP isa (.block (VG.Proof.Sha256.X86.updTo j)) s fun s' =>
      s'.mem = VG.Proof.Sha256.X86.writeWords (VG.Proof.Sha256.X86.st s₀) (VG.Proof.Sha256.X86.scr s₀) s.mem j ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil (M := isa) ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | j + 1, hj => by
    rw [VG.Proof.Sha256.X86.updTo_succ, WP.block_append_iff]
    refine WP.mono (VG.Proof.Sha256.X86.updTo_ok hp heax hesi hrd hwr j (by bdd_omega))
      fun s₁ ⟨hm₁, hr₁, hrd₁, hwr₁⟩ => ?_
    refine WP.mono (VG.Proof.Sha256.X86.upd_ok j (p := VG.Proof.Sha256.X86.st s₀) (q := VG.Proof.Sha256.X86.scr s₀)
      (by rw [hr₁ .eax (by decide), heax]) (by rw [hr₁ .esi (by decide), hesi])
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact hp.scratch.rd _ (by bdd_omega))
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact VG.Proof.Sha256.X86.in_st hp (by bdd_omega))
      (by rw [hwr₁, hwr]; exact VG.Proof.Sha256.X86.out_st hp (by bdd_omega))) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, hr₁ r hr], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
    rw [hm₂, hm₁, VG.Proof.Sha256.X86.writeWords_scr hp _ (by bdd_omega) j (by bdd_omega),
      VG.Proof.Sha256.X86.writeWords_st hp _ (by bdd_omega) j (by bdd_omega)]
    rfl

theorem update_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s : State} (V H : HashValue)
    (hv : VG.Proof.Sha256.X86.Vars 0 (VG.Proof.Sha256.X86.scr s₀) s.mem V) (hesp : s.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀) (hesi : s.gpr .esi = VG.Proof.Sha256.X86.scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) 4) 32 = VG.Proof.Sha256.X86.st s₀)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (VG.Proof.Sha256.X86.stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = VG.Proof.Sha256.X86.writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
      s'.zf = some (s.gpr .ebp - 1 == 0) ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha256.X86.esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by bdd_omega) (by bdd_omega)
  -- `mov eax, [esp + 4]`
  have h₁ : WP isa (.block [.mov .eax (.mem ⟨.esp, 4⟩)]) s fun s₁ =>
      s₁.gpr .eax = VG.Proof.Sha256.X86.st s₀ ∧ (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec,
      readSrc, ea_mk, State.setReg, State.load32, hesp, ia, harg, ite_true, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  rw [VG.Proof.Sha256.X86.update_eq, WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨he₁, hr₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86.updTo_ok hp he₁ (by rw [hr₁ .esi (by decide), hesi]) (hrd₁.trans hrd)
    (hwr₁.trans hwr) 8 (Nat.le_refl _)) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
  have hr : ∀ r, r ≠ .eax → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [hr₂ r h2, hr₁ r h1]
  -- `add edi, 64; sub ebp, 1`
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runBlock_nil, runStep_some, exec,
    execAlu, readSrc, State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁]
    rw [VG.Proof.Sha256.X86.vars0] at hv
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
    have m0 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 0) 32 = H[0]'(by decide) := hH 0 (by decide)
    have m1 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 4) 32 = H[1]'(by decide) := hH 1 (by decide)
    have m2 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 8) 32 = H[2]'(by decide) := hH 2 (by decide)
    have m3 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 12) 32 = H[3]'(by decide) := hH 3 (by decide)
    have m4 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 16) 32 = H[4]'(by decide) := hH 4 (by decide)
    have m5 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 20) 32 = H[5]'(by decide) := hH 5 (by decide)
    have m6 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 24) 32 = H[6]'(by decide) := hH 6 (by decide)
    have m7 : s.mem.readW (addr (VG.Proof.Sha256.X86.st s₀) 28) 32 = H[7]'(by decide) := hH 7 (by decide)
    simp only [VG.Proof.Sha256.X86.writeWords, VG.Proof.Sha256.X86.writeState, Nat.reduceMul, Nat.reduceAdd, v0, v1, v2, v3, v4, v5, v6,
      v7, m0, m1, m2, m3, m4, m5, m6, m7, Vector.getElem_zipWith]
  all_goals simp (config := {decide := true}) [hr]

theorem saved_frame {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {m m' : Mem} (h : VG.Proof.Sha256.X86.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)] m m' ∨ Frame [VG.Proof.Sha256.X86.stR s₀] m m') : VG.Proof.Sha256.X86.Saved s₀ m' := by
  have key : ∀ d : Nat, 96 ≤ d → d + 4 ≤ 112 →
      m'.readW (addr (VG.Proof.Sha256.X86.scr s₀) d) 32 = m.readW (addr (VG.Proof.Sha256.X86.scr s₀) d) 32 := by
    intro d hd hd'
    have hc : (⟨addr (VG.Proof.Sha256.X86.scr s₀) d, 4⟩ : Region).Contains (addr (VG.Proof.Sha256.X86.scr s₀) d) (32 / 8) :=
      Region.contains_self _ _
    rcases hf with hf | hf
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      rw [hp.scr_eq (by bdd_omega)]
      exact Offset.disjoint_base _ (by bdd_omega) (by bdd_omega)
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      refine Region.Disjoint.sub_left hp.st_scr.symm ?_
      rw [hp.scr_eq (by bdd_omega)]
      exact Offset.sub_base _ (by bdd_omega)
  exact h.of_readW fun p hp' => key _ (by revert p hp'; decide) (compressSaved_fits.1 p hp')

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {i t : Nat} (hi : i < VG.Proof.Sha256.X86.nb s₀) (ht : t < 16) :
    bswap (s₀.mem.readW (addr (VG.Proof.Sha256.X86.blkAddr s₀ i) (4 * t)) 32) = W (VG.Proof.Sha256.X86.blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, bswap_readW]
  simp only [VG.Proof.Sha256.X86.blk, blockAt, parseBlock]
  generalize (VG.Proof.Sha256.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) from Offset.add_add _ _ 1]

theorem work_sub (p : BitVec 32) : Region.Sub (VG.Proof.Sha256.X86.workRegion p) ⟨p.setWidth 64, 112⟩ :=
  Region.sub_prefix (by bdd_omega)

theorem harg_of {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀] s₀.mem m) :
    m.readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) 4) 32 = VG.Proof.Sha256.X86.st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem body_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {i : Nat} (hi : i < VG.Proof.Sha256.X86.nb s₀) {s : State}
    (hL : VG.Proof.Sha256.X86.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha256.X86.Common s₀ (VG.Proof.Sha256.X86.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Sha256.X86.nb s₀ ∧ VG.Proof.Sha256.X86.LInv s₀ (i + 1) s') := by
  have hfits := hp.scr_fits
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.load_ok hp hL.esp hL.esi hL.rd hL.wr (VG.Proof.Sha256.X86.harg_of hp hL.frame))
    fun s₁ ⟨hm₁, hpub₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)] s.mem s₁.mem := by rw [hm₁]; exact VG.Proof.Sha256.X86.frame_writeVars hfits _ _
  have hwin : ∀ r' ∈ [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)], (VG.Proof.Sha256.X86.blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (VG.Proof.Sha256.X86.work_sub _)
  have hblk : ∀ m, Frame [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (VG.Proof.Sha256.X86.blkAddr s₀ i) (4 * t)) 32) = W (VG.Proof.Sha256.X86.blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide),
      hf₁.readW (hp.blk_contains hi ht) hwin (by decide),
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact VG.Proof.Sha256.X86.blk_word hp hi ht
  have hedi₁ : s₁.gpr .edi = VG.Proof.Sha256.X86.blkAddr s₀ i := (hpub₁ .edi (by decide)).trans hL.edi
  have hesi₁ : s₁.gpr .esi = VG.Proof.Sha256.X86.scr s₀ := (hpub₁ .esi (by decide)).trans hL.esi
  have hv₁ : VG.Proof.Sha256.X86.Vars 0 (VG.Proof.Sha256.X86.scr s₀) s₁.mem (stateAt s.mem ((VG.Proof.Sha256.X86.st s₀).setWidth 64)) := by
    rw [hm₁]; exact VG.Proof.Sha256.X86.vars_writeVars hfits _ _
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.rounds_ok _ (VG.Proof.Sha256.X86.blk s₀ i) _ (VG.Proof.Sha256.X86.scr s₀) s₁
    (hp.scratch.congr (by rw [hrd₁, hL.rd]) (by rw [hwr₁, hL.wr])) hedi₁ hesi₁
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)], (VG.Proof.Sha256.X86.stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (VG.Proof.Sha256.X86.work_sub _)
  have pub₂ : ∀ r ∈ VG.Proof.Sha256.X86.pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hf₂ : Frame [VG.Proof.Sha256.X86.workRegion (VG.Proof.Sha256.X86.scr s₀)] s.mem s₂.mem := hf₁.trans hR.frame
  have hframe₂ : Frame [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀] s₀.mem s₂.mem :=
    hL.frame.trans (hf₂.sub fun r hr => ⟨VG.Proof.Sha256.X86.scrR s₀, by simp, by simp at hr; subst hr; exact VG.Proof.Sha256.X86.work_sub _⟩)
  refine WP.mono (VG.Proof.Sha256.X86.update_ok hp _ (stateAt s.mem ((VG.Proof.Sha256.X86.st s₀).setWidth 64)) hR.vars
    (by rw [pub₂ .esp (by decide), hL.esp]) (by rw [pub₂ .esi (by decide), hL.esi])
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) (VG.Proof.Sha256.X86.harg_of hp hframe₂) fun k hk => ?_)
    fun s₃ h₃ => ?_
  · rw [hf₂.readW (VG.Proof.Sha256.X86.contains_sub (by bdd_omega) (by bdd_omega) (hp.stAddr_eq hk)) hst (by decide),
      VG.Proof.Sha256.X86.stateAt_get hp _ hk]
  obtain ⟨hm₃, hedi₃, hebp₃, hz₃, hesi₃, hesp₃, hrd₃, hwr₃⟩ := h₃
  have hnb : VG.Proof.Sha256.X86.nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (VG.Proof.Sha256.X86.nb s₀ - (i + 1)) := by
    rw [pub₂ .ebp (by decide), hL.ebp, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  have hframe : Frame [VG.Proof.Sha256.X86.stR s₀, VG.Proof.Sha256.X86.scrR s₀] s₀.mem s₃.mem := by
    refine hframe₂.trans ?_
    rw [hm₃]
    exact (VG.Proof.Sha256.X86.frame_writeState hp (Frame.refl _ _) _).sub
      fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → VG.Proof.Sha256.X86.Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hesi₃, pub₂ .esi (by decide), hL.esi],
      by rw [hesp₃, pub₂ .esp (by decide), hL.esp],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, VG.Proof.Sha256.X86.stateAt_writeState hp, VG.Proof.Sha256.X86.compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine VG.Proof.Sha256.X86.saved_frame hp ?_ (.inr (VG.Proof.Sha256.X86.frame_writeState hp (Frame.refl _ _) _))
      exact VG.Proof.Sha256.X86.saved_frame hp hL.saved (.inl hf₂)
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (VG.Proof.Sha256.X86.nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hebp, Option.map_some]
  by_cases hlast : i + 1 = VG.Proof.Sha256.X86.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : VG.Proof.Sha256.X86.nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Sha256.X86.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by bdd_omega, { hcommon _ rfl with edi := ?_, ebp := ?_ }⟩
    · rw [hedi₃, pub₂ .edi (by decide), hL.edi]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (VG.Proof.Sha256.X86.bp s₀ + ·) (congrArg (BitVec.ofNat _) (by bdd_omega)))
    · rw [hebp₃, hebp]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.saveCode .eax VG.Proof.Sha256.X86.compressSaved ++
    ([.mov .esi (.reg .eax), .mov .edi (.mem ⟨.esp, 8⟩), .mov .ebp (.mem ⟨.esp, 12⟩),
      .alu .test .ebp (.reg .ebp)] : List Instr)) := rfl

theorem epilogue_eq :
    epilogue = Spill.restoreCode .esi ([(.ebx, 96), (.edi, 104), (.ebp, 108)] ++ [(.esi, 100)]) ++ [] :=
  rfl

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (VG.Proof.Sha256.X86.scr s₀)) s₀.gpr VG.Proof.Sha256.X86.compressSaved

theorem compressSaved_contains {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) : ∀ p ∈ VG.Proof.Sha256.X86.compressSaved, (VG.Proof.Sha256.X86.scrR s₀).Contains (addr (VG.Proof.Sha256.X86.scr s₀) p.2) 4 :=
  fun p h => have := compressSaved_fits.1 p h; VG.Proof.Sha256.X86.contains_sub (by bdd_omega) (by bdd_omega) (hp.scr_eq (by bdd_omega))

/-- Reading an argument after saving the registers. -/
theorem saveMem_arg {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Sha256.X86.saveMem s₀).readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Sha256.X86.esp₀ s₀) d) 32 :=
  Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
    hp.arg_scr.sep (hp.arg_contains hd hd') (VG.Proof.Sha256.X86.compressSaved_contains hp p h)

theorem save_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = VG.Proof.Sha256.X86.scr s₀ ∧ s₁.gpr .edi = VG.Proof.Sha256.X86.bp s₀ ∧ s₁.gpr .ebp = arg s₀ 2 ∧
      s₁.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Sha256.X86.saveMem s₀ ∧
      s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  rw [VG.Proof.Sha256.X86.prologue_eq]
  refine Wp.wp_ldm rfl (hp.in_arg (d := 16) (by bdd_omega) (by bdd_omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok VG.Proof.Sha256.X86.compressSaved (fun p h => by rw [u₁.gpr, u₁.wr]; exact hp.scratch.wr _ (compressSaved_fits.1 p h))
    fun s₂ u₂ => ?_
  have hm : s₂.mem = VG.Proof.Sha256.X86.saveMem s₀ := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have hesp : s₂.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  refine Wp.wp_mov fun s₃ u₃ => Wp.wp_ldm (by rw [u₃.other _ (by decide), hesp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hp.in_arg (d := 8) (by bdd_omega) (by bdd_omega))
    fun s₄ u₄ => Wp.wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), hesp])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
          exact hp.in_arg (d := 12) (by bdd_omega) (by bdd_omega))
    fun s₅ u₅ => Wp.wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]; rfl
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.mem, hm, VG.Proof.Sha256.X86.saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl
  · rw [f₆.gpr, u₅.gpr, u₄.mem, u₃.mem, hm, VG.Proof.Sha256.X86.saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hesp]
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, hm]
  · rw [z₆, u₅.gpr, u₄.mem, u₃.mem, hm, VG.Proof.Sha256.X86.saveMem_arg hp (by bdd_omega) (by bdd_omega)]; rfl

theorem saveMem_saved {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) : VG.Proof.Sha256.X86.Saved s₀ (VG.Proof.Sha256.X86.saveMem s₀) :=
  Spill.saveMem_saved_addr _ _ VG.Proof.Sha256.X86.compressSaved_fits hp.scr_fits

theorem saveMem_frame {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) : Frame [VG.Proof.Sha256.X86.scrR s₀] s₀.mem (VG.Proof.Sha256.X86.saveMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ (VG.Proof.Sha256.X86.compressSaved_contains hp)

theorem common_zero {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = VG.Proof.Sha256.X86.scr s₀)
    (hesp : s₁.gpr .esp = VG.Proof.Sha256.X86.esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = VG.Proof.Sha256.X86.saveMem s₀) : VG.Proof.Sha256.X86.Common s₀ 0 s₁ := by
  refine ⟨hesi, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact VG.Proof.Sha256.X86.saveMem_saved hp⟩
  · rw [hm]; exact (VG.Proof.Sha256.X86.saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply VG.Proof.Sha256.X86.stateAt_eq hp
    intro k hk
    rw [(VG.Proof.Sha256.X86.saveMem_frame hp).readW (VG.Proof.Sha256.X86.contains_sub (len := 32) (off := 4 * k) (by bdd_omega) (by bdd_omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← VG.Proof.Sha256.X86.stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) {s : State} (hc : VG.Proof.Sha256.X86.Common s₀ (VG.Proof.Sha256.X86.nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [VG.Proof.Sha256.X86.epilogue_eq]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => by rw [hc.esi, hc.rd, hc.wr]; exact hp.scratch.rd _ (compressSaved_fits.1 p (by revert p h; decide)))
    (by rw [hc.esi]; exact hc.saved.sub (by decide)) fun s' u =>
      WP.block_nil ⟨u.abi (by decide) (by decide) hc.esp, u.mem⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha256.X86.Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha256.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.save_ok hp) fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha256.X86.Common s₀ (VG.Proof.Sha256.X86.nb s₀)) ?_ fun s₂ hc =>
    WP.mono (VG.Proof.Sha256.X86.restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := VG.Proof.Sha256.X86.common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Sha256.X86.nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [VG.Proof.Sha256.X86.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Sha256.X86.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Sha256.X86.nb s₀ - i ∧ i < VG.Proof.Sha256.X86.nb s₀ ∧ VG.Proof.Sha256.X86.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Sha256.X86.Common s₀ (VG.Proof.Sha256.X86.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Sha256.X86.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Sha256.X86.nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Sha256.X86.LInv s₀ 0 s₁ :=
      { hc₀ with
        edi := by rw [hedi]; simp [VG.Proof.Sha256.X86.blkAddr]
        ebp := by rw [hebp]; simp [VG.Proof.Sha256.X86.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Sha256.X86.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

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
  mem := VG.Proof.Sha256.X86.satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem sat_pre : Proof.Sha256.compressX86.pre VG.Proof.Sha256.X86.satState := by
  have a0 : arg VG.Proof.Sha256.X86.satState 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Sha256.X86.satState 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Sha256.X86.satState 2 = 0 := by decide
  have a3 : arg VG.Proof.Sha256.X86.satState 3 = 0x3000 := by decide
  have e : argAddr VG.Proof.Sha256.X86.satState 0 = 0x4004 := by decide
  simp only [Proof.Sha256.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  first
  | exact Offset.disjoint_of_le (by decide) (by decide)
  | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 112], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Sha256.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.Sha256.X86.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Sha256.X86.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Sha256.X86.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha256.compressX86.pre s₁)
    (h₂ : Proof.Sha256.compressX86.pre s₂) (hpub : Proof.Sha256.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Sha256.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := VG.Proof.Sha256.X86.pre_of _ h₁; have hp₂ := VG.Proof.Sha256.X86.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Sha256.X86.wf₀ hp₁, VG.Proof.Sha256.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Sha256.X86.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Sha256.X86.stR, VG.Proof.Sha256.X86.scrR, VG.Proof.Sha256.X86.st, VG.Proof.Sha256.X86.scr, a0, a3]
  · simp only [VG.Proof.Sha256.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by bdd_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by bdd_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by bdd_omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha256.X86.compress Proof.Sha256.compressX86 :=
  ⟨fun s hs => VG.Proof.Sha256.X86.correct (VG.Proof.Sha256.X86.pre_of s hs),
    VG.Taint.constantTime (A := taint) VG.Proof.Sha256.X86.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Sha256.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Sha256.X86.satState, VG.Proof.Sha256.X86.sat_pre⟩⟩

end VG.Proof.Sha256.X86

end
