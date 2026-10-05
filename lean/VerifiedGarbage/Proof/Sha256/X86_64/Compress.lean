import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Lit`. -/
section

/-!
# SHA-256 on X86_64: the code as literals
-/

namespace VG

materialize_code Impl.Sha256.X86_64.compress

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Contract`. -/
section

/-!
# SHA-256: the x86-64 contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the x86-64 implementations of the compression function and the
streaming interface, in terms of `Spec/Sha256.lean`.
-/

namespace VG.Proof.Sha256

open Spec.Sha256

open X86_64 in
/-- x86-64 contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 70])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (560 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack.
The pointers and `n` are public; the hash value and the blocks are secret. -/
def compressX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 32⟩
    let blocks : Region := ⟨s.gpr .rsi, 64 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .rdi) =
      compressBlocks (stateAt s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

open X86_64 in
/-- x86-64 contract for `vg_sha256_init(state: *mut [u8; 96])` and
`vg_sha224_init`, which store the initial hash value `iv`: makes the
streaming state at `state` represent the empty message, hashed from `iv`.

The code may write `state` (96 bytes), which may not overlap the return
address on the stack. The pointer is public. -/
def initX86_64 (iv : HashValue) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := ReprFrom iv s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

open X86_64 in
/-- x86-64 contract for
`vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 76])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value `iv`, then afterwards it
represents `m` followed by the `len` bytes at `data`, from `iv`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes) and `scratch` (608 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, nor
the 8 bytes below it (where the call of `vg_sha256_compress` stores its
return address).
The pointers, `count` and `len` are public; the state and the data are
secret. -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 608⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, ReprFrom iv s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    ReprFrom iv s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open X86_64 in
/-- x86-64 contract for
`vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], scratch: *mut [u64; 76])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from the initial hash value `iv`, writes the final hash
value of `m` from `iv` to `out` (the SHA-256 digest if `iv` is `H0`).

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified), `out` (32 bytes) and `scratch` (608 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack, nor the 8 bytes below it (where the call of
`vg_sha256_compress` stores its return address). The pointers and `count`
are public; the state is secret. -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let out : Region := ⟨s.gpr .rdx, 32⟩
    let scratch : Region := ⟨s.gpr .rcx, 608⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, ReprFrom iv s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .rdx) 32 = Spec.Sha256.finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sha256

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Compress`. -/
section

/-!
# SHA-256 compression function on x86-64: the message schedule and the rounds
-/

namespace VG.Proof.Sha256.X86_64

open VG VG.X86_64 VG.Impl.Sha256.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64 ∧ s.gpr (var t 5) = v[5].setWidth 64 ∧
  s.gpr (var t 6) = v[6].setWidth 64 ∧ s.gpr (var t 7) = v[7].setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers a round reads are not those it writes after them (`T1`,
`T2`, `d`, `h`), nor are the others it keeps. In three parts: `decide` cannot
synthesize the instance of one long conjunction. -/
theorem round_ne₁ (t : Nat) :
    (¬var t 0 = .r14 ∧ ¬var t 0 = .r15 ∧ ¬var t 1 = .r14 ∧ ¬var t 1 = .r15 ∧
      ¬var t 2 = .r14 ∧ ¬var t 2 = .r15 ∧ ¬var t 3 = .r14 ∧ ¬var t 3 = .r15) ∧
    (¬var t 4 = .r14 ∧ ¬var t 4 = .r15 ∧ ¬var t 5 = .r14 ∧ ¬var t 5 = .r15 ∧
      ¬var t 6 = .r14 ∧ ¬var t 6 = .r15 ∧ ¬var t 7 = .r14 ∧ ¬var t 7 = .r15) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by bdd_omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem round_ne₂ (t : Nat) :
    (¬var t 0 = var t 3 ∧ ¬var t 0 = var t 7 ∧ ¬var t 1 = var t 3 ∧ ¬var t 1 = var t 7 ∧
      ¬var t 2 = var t 3 ∧ ¬var t 2 = var t 7 ∧ ¬var t 3 = var t 7 ∧ ¬var t 4 = var t 3) ∧
    (¬var t 4 = var t 7 ∧ ¬var t 5 = var t 3 ∧ ¬var t 5 = var t 7 ∧ ¬var t 6 = var t 3 ∧
      ¬var t 6 = var t 7 ∧ ¬var t 7 = var t 3 ∧ ¬Reg.r13 = var t 7) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by bdd_omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem round_ne₃ (t : Nat) :
    (¬Reg.rdi = var t 3 ∧ ¬Reg.rdi = var t 7 ∧ ¬Reg.rsi = var t 3 ∧ ¬Reg.rsi = var t 7) ∧
    (¬Reg.rdx = var t 3 ∧ ¬Reg.rdx = var t 7 ∧ ¬Reg.rcx = var t 3 ∧ ¬Reg.rcx = var t 7 ∧
      ¬Reg.rsp = var t 3 ∧ ¬Reg.rsp = var t 7) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by bdd_omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_ne₁ … round_ne₃` say are different where it matters), with
the register writes kept folded (`VG.X86_64.RegUpd`). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : VG.Proof.Sha256.X86_64.Vars t s v) (hw : s.gpr T0 = w.setWidth 64) :
    WP isa (.block (round t)) s fun s' =>
      VG.Proof.Sha256.X86_64.Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ VG.Proof.Sha256.X86_64.pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨⟨n0, n1, n2, n3, n4, n5, n6, n7⟩, ⟨n8, n9, n10, n11, n12, n13, n14, n15⟩⟩ := VG.Proof.Sha256.X86_64.round_ne₁ t
  obtain ⟨⟨m0, m1, m2, m3, m4, m5, m6, m7⟩, ⟨m8, m9, m10, m11, m12, m13, m14⟩⟩ := VG.Proof.Sha256.X86_64.round_ne₂ t
  obtain ⟨⟨p2, p3, p4, p5⟩, ⟨p6, p7, p8, p9, p10, p11⟩⟩ := VG.Proof.Sha256.X86_64.round_ne₃ t
  simp only [VG.Proof.Sha256.X86_64.Vars, VG.Proof.Sha256.X86_64.var_succ_zero, VG.Proof.Sha256.X86_64.var_succ t _ (show 0 < 7 by bdd_omega),
    VG.Proof.Sha256.X86_64.var_succ t _ (show 1 < 7 by bdd_omega), VG.Proof.Sha256.X86_64.var_succ t _ (show 2 < 7 by bdd_omega),
    VG.Proof.Sha256.X86_64.var_succ t _ (show 3 < 7 by bdd_omega), VG.Proof.Sha256.X86_64.var_succ t _ (show 4 < 7 by bdd_omega),
    VG.Proof.Sha256.X86_64.var_succ t _ (show 5 < 7 by bdd_omega), VG.Proof.Sha256.X86_64.var_succ t _ (show 6 < 7 by bdd_omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86_64.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2] at hw ⊢
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, execShift32, readSrc32, isa,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, and_self, Nat.reduceLeDiff,
    Nat.reduceEqDiff, not_false_eq_true, reduceCtorEq,
    n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
    m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14,
    h0, h1, h2, h3, h4, h5, h6, h7, hw, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · have n : ¬r = .r14 ∧ ¬r = .r15 ∧ ¬r = d ∧ ¬r = h := by
      simp only [VG.Proof.Sha256.X86_64.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp only [p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, not_false_eq_true, and_self,
          reduceCtorEq]
    simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, n,
      not_false_eq_true]
  all_goals
    refine congrArg (BitVec.setWidth 64) ?_
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofInt 64 ↑(4 * (j % 16))

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hrsi : s.gpr .rsi = bp) (hrcx : s.gpr .rcx = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (VG.Proof.Sha256.X86_64.slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (VG.Proof.Sha256.X86_64.slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ↑(4 * t)) 4)
    (hblk : t < 16 → bswap32 (s.mem.readW (bp + BitVec.ofInt 64 ↑(4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (VG.Proof.Sha256.X86_64.slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = (W M t).setWidth 64 ∧
      s'.mem = s.mem.writeW (VG.Proof.Sha256.X86_64.slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [VG.Proof.Sha256.X86_64.slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.X86_64.schedule, ht, ite_true, slot, at_, T0, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc32, isa, State.ea,
      State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq,
      Nat.reduceLeDiff, hrsi, hrcx, hi, hout, ite_true,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 _ _ => ?_⟩
    simp only [RegUpd.gpr_setReg_of_ne, h0, not_false_eq_true]
  · have hw := hwin (by bdd_omega)
    have e2 := hw (t - 2) (by bdd_omega) (by bdd_omega)
    have e7 := hw (t - 7) (by bdd_omega) (by bdd_omega)
    have e15 := hw (t - 15) (by bdd_omega) (by bdd_omega)
    have e16 := hw (t - 16) (by bdd_omega) (by bdd_omega)
    rw [show (t - 2) % 16 = (t + 14) % 16 by bdd_omega] at e2
    rw [show (t - 7) % 16 = (t + 9) % 16 by bdd_omega] at e7
    rw [show (t - 15) % 16 = (t + 1) % 16 by bdd_omega] at e15
    rw [show (t - 16) % 16 = t % 16 by bdd_omega] at e16
    simp only [Impl.Sha256.X86_64.schedule, ht, ite_false, slot, at_, T0, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu32, execShift32, readSrc32,
      isa, State.ea, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, Nat.reduceLeDiff,
      Nat.reduceEqDiff, and_self, not_false_eq_true, reduceCtorEq, hrcx, hin, hout, ite_true,
      ite_false, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq, e2, e7, e15, e16,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by bdd_omega)
    rw [ssig0_eq, ssig1_eq] at hW
    refine ⟨by rw [hW], by rw [hW], trivial, trivial, fun r h0 h1 h2 => ?_⟩
    simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, h0,
      h1, h2, not_false_eq_true]

/-! ## The 64 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pubRegs_ne {r : Reg} (h : r ∈ VG.Proof.Sha256.X86_64.pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 := by
  simp only [VG.Proof.Sha256.X86_64.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (VG.Proof.Sha256.X86_64.winRegion scr).Contains (VG.Proof.Sha256.X86_64.slotAddr scr j) 4 := by
  simp only [Region.Contains, VG.Proof.Sha256.X86_64.slotAddr, VG.Proof.Sha256.X86_64.ofInt_natCast]
  have : j % 16 < 16 := Nat.mod_lt _ (by bdd_omega)
  generalize j % 16 = p at *
  rw [Offset.add_sub_cancel_left]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (VG.Proof.Sha256.X86_64.slotAddr scr i) 4 (VG.Proof.Sha256.X86_64.slotAddr scr j) 4 := by
  simp only [VG.Proof.Sha256.X86_64.slotAddr, VG.Proof.Sha256.X86_64.ofInt_natCast]
  exact Offset.sep _ (by bdd_omega) (by bdd_omega) (by bdd_omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : VG.Proof.Sha256.X86_64.Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ VG.Proof.Sha256.X86_64.pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [VG.Proof.Sha256.X86_64.winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (VG.Proof.Sha256.X86_64.slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hrcx : sB.gpr .rcx = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (VG.Proof.Sha256.X86_64.slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (VG.Proof.Sha256.X86_64.slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4)
    (hblk : ∀ m, Frame [VG.Proof.Sha256.X86_64.winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap32 (m.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t)
    (h0 : VG.Proof.Sha256.X86_64.Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (VG.Proof.Sha256.X86_64.RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by bdd_omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by bdd_omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    have hs_rcx : s.gpr .rcx = scr := (hs.pub .rcx (by decide)).trans hrcx
    refine WP.mono (VG.Proof.Sha256.X86_64.schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : VG.Proof.Sha256.X86_64.Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := VG.Proof.Sha256.X86_64.work_ne (VG.Proof.Sha256.X86_64.var_mem t k); hr₁ _ this.1 this.2.1 this.2.2
      simp only [VG.Proof.Sha256.X86_64.Vars, e] at hv ⊢
      exact hv
    refine WP.mono (VG.Proof.Sha256.X86_64.round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := VG.Proof.Sha256.X86_64.pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86_64.win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (VG.Proof.Sha256.X86_64.slot_sep scr (by bdd_omega)) (by decide)]
        exact hs.win j (by bdd_omega) (by bdd_omega)

end VG.Proof.Sha256.X86_64

/-!
# SHA-256 compression function on x86-64: the whole function
-/

namespace VG.Proof.Sha256.X86_64

open VG VG.X86_64 VG.Impl.Sha256.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [VG.Proof.Sha256.X86_64.ofInt_natCast]; exact VG.Proof.Sha256.X86_64.contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 4 (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
  rw [VG.Proof.Sha256.X86_64.ofInt_natCast, VG.Proof.Sha256.X86_64.ofInt_natCast]
  exact Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 =
    m.readW (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Sha256.X86_64.word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← VG.Proof.Sha256.X86_64.ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, VG.Proof.Sha256.X86_64.ofInt_natCast]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨VG.Proof.Sha256.X86_64.st s₀, 32⟩
abbrev blR : Region := ⟨VG.Proof.Sha256.X86_64.bp s₀, 64 * VG.Proof.Sha256.X86_64.nb s₀⟩
abbrev scrR : Region := ⟨VG.Proof.Sha256.X86_64.scr s₀, 560⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (VG.Proof.Sha256.X86_64.st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := VG.Proof.Sha256.X86_64.bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (VG.Proof.Sha256.X86_64.blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Sha256.X86_64.blR s₀]
  wr : s₀.wr = [VG.Proof.Sha256.X86_64.stR s₀, VG.Proof.Sha256.X86_64.scrR s₀]
  st_scr : (VG.Proof.Sha256.X86_64.stR s₀).Disjoint (VG.Proof.Sha256.X86_64.scrR s₀)
  blk_st : (VG.Proof.Sha256.X86_64.blR s₀).Disjoint (VG.Proof.Sha256.X86_64.stR s₀)
  blk_scr : (VG.Proof.Sha256.X86_64.blR s₀).Disjoint (VG.Proof.Sha256.X86_64.scrR s₀)
  ret_st : (VG.Proof.Sha256.X86_64.retR s₀).Disjoint (VG.Proof.Sha256.X86_64.stR s₀)
  ret_scr : (VG.Proof.Sha256.X86_64.retR s₀).Disjoint (VG.Proof.Sha256.X86_64.scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressX86_64.pre s₀) : VG.Proof.Sha256.X86_64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Sha256.X86_64.Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * VG.Proof.Sha256.X86_64.nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (VG.Proof.Sha256.X86_64.st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (VG.Proof.Sha256.X86_64.st s₀ - VG.Proof.Sha256.X86_64.bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨VG.Proof.Sha256.X86_64.stR s₀, by simp [h.wr], VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨VG.Proof.Sha256.X86_64.stR s₀, by simp [h.wr], VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Sha256.X86_64.slotAddr (VG.Proof.Sha256.X86_64.scr s₀) j) 4 :=
  ⟨VG.Proof.Sha256.X86_64.scrR s₀, by simp [h.wr], VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (VG.Proof.Sha256.X86_64.slotAddr (VG.Proof.Sha256.X86_64.scr s₀) j) 4 :=
  ⟨VG.Proof.Sha256.X86_64.scrR s₀, by simp [h.wr], VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)⟩

theorem blk_contains {i t : Nat} (hi : i < VG.Proof.Sha256.X86_64.nb s₀) (ht : t < 16) :
    (VG.Proof.Sha256.X86_64.blR s₀).Contains (VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 := by
  have := h.nb_lt
  rw [VG.Proof.Sha256.X86_64.ofInt_natCast, show VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    VG.Proof.Sha256.X86_64.bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact VG.Proof.Sha256.X86_64.contains_offset (by bdd_omega) (by bdd_omega)

theorem in_blk {i t : Nat} (hi : i < VG.Proof.Sha256.X86_64.nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 :=
  ⟨VG.Proof.Sha256.X86_64.blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.Sha256.X86_64.scr s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.Sha256.X86_64.st s₀
  rcx : s.gpr .rcx = VG.Proof.Sha256.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Sha256.X86_64.stR s₀, VG.Proof.Sha256.X86_64.scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (VG.Proof.Sha256.X86_64.st s₀) = compressBlocks (VG.Proof.Sha256.X86_64.H₀ s₀) s₀.mem (VG.Proof.Sha256.X86_64.bp s₀) i
  saved : VG.Proof.Sha256.X86_64.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86_64.Common s₀ i s where
  rsi : s.gpr .rsi = VG.Proof.Sha256.X86_64.blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.Sha256.X86_64.nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .rbx (.mem (at_ .rdi (4 * 1))),
    .mov32 .rbp (.mem (at_ .rdi (4 * 2))), .mov32 .r8 (.mem (at_ .rdi (4 * 3))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 4))), .mov32 .r10 (.mem (at_ .rdi (4 * 5))),
    .mov32 .r11 (.mem (at_ .rdi (4 * 6))), .mov32 .r12 (.mem (at_ .rdi (4 * 7)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .rbx (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .rbp (.mem (at_ .rdi (4 * 2))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 3))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 4))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 5))),
    .alu32 .add .r11 (.mem (at_ .rdi (4 * 6))), .alu32 .add .r12 (.mem (at_ .rdi (4 * 7))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .rbx,
    .store32 (at_ .rdi (4 * 2)) .rbp, .store32 (at_ .rdi (4 * 3)) .r8,
    .store32 (at_ .rdi (4 * 4)) .r9, .store32 (at_ .rdi (4 * 5)) .r10,
    .store32 (at_ .rdi (4 * 6)) .r11, .store32 (at_ .rdi (4 * 7)) .r12,
    .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : VG.Proof.Sha256.X86_64.Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
    s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
    s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
    s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64 := Iff.rfl

theorem load_ok {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {s : State} (hrdi : s.gpr .rdi = VG.Proof.Sha256.X86_64.st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      VG.Proof.Sha256.X86_64.Vars 0 s₁ (stateAt s.mem (VG.Proof.Sha256.X86_64.st s₀)) ∧ (∀ r ∈ VG.Proof.Sha256.X86_64.pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [VG.Proof.Sha256.X86_64.load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp only [VG.Proof.Sha256.X86_64.vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, VG.Proof.Sha256.X86_64.ea_at,
    State.load32, State.setReg32, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg,
    not_false_eq_true, reduceCtorEq, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 0 < 8 by decide), VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 1 < 8 by decide),
    VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 2 < 8 by decide), VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 3 < 8 by decide),
    VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 4 < 8 by decide), VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 5 < 8 by decide),
    VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 6 < 8 by decide), VG.Proof.Sha256.X86_64.stateAt_get _ _ (show 7 < 8 by decide)]
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, fun r hr => ?_,
    trivial, trivial, trivial⟩
  simp only [VG.Proof.Sha256.X86_64.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.gpr_setReg_of_ne, not_false_eq_true, reduceCtorEq]

/-- Eight 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofInt 64 ((4 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((4 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((4 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((4 * 3 : Nat) : Int)) v[3]).writeW
    (p + BitVec.ofInt 64 ((4 * 4 : Nat) : Int)) v[4]).writeW
    (p + BitVec.ofInt 64 ((4 * 5 : Nat) : Int)) v[5]).writeW
    (p + BitVec.ofInt 64 ((4 * 6 : Nat) : Int)) v[6]).writeW
    (p + BitVec.ofInt 64 ((4 * 7 : Nat) : Int)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (VG.Proof.Sha256.X86_64.writeState m p v) p = v := by
  apply VG.Proof.Sha256.X86_64.stateAt_eq
  intro k hk
  simp only [VG.Proof.Sha256.X86_64.writeState]
  rcases (by bdd_omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, VG.Proof.Sha256.X86_64.readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [VG.Proof.Sha256.X86_64.stR s₀] m m') (v : HashValue) :
    Frame [VG.Proof.Sha256.X86_64.stR s₀] m (VG.Proof.Sha256.X86_64.writeState m' (VG.Proof.Sha256.X86_64.st s₀) v) := by
  have c : ∀ k, k < 8 → (VG.Proof.Sha256.X86_64.stR s₀).Contains (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)
  simp only [VG.Proof.Sha256.X86_64.writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

theorem update_ok {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {s : State} (V H : HashValue) (hv : VG.Proof.Sha256.X86_64.Vars 0 s V)
    (hrdi : s.gpr .rdi = VG.Proof.Sha256.X86_64.st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = VG.Proof.Sha256.X86_64.writeState s.mem (VG.Proof.Sha256.X86_64.st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (VG.Proof.Sha256.X86_64.st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  rw [VG.Proof.Sha256.X86_64.vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [VG.Proof.Sha256.X86_64.update_eq]
  simp only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, VG.Proof.Sha256.X86_64.ea_at, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_setReg, RegUpd.zf_arithFlags, not_false_eq_true, reduceCtorEq, hrdi, i0, i1, i2, i3,
    i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true,
    RegUpd.setWidth_setWidth_32,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], trivial, trivial, trivial, trivial, trivial⟩
  simp only [VG.Proof.Sha256.X86_64.writeState, Vector.getElem_zipWith]

theorem saved_frame {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {m m' : Mem} (h : VG.Proof.Sha256.X86_64.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha256.X86_64.winRegion (VG.Proof.Sha256.X86_64.scr s₀)] m m' ∨ Frame [VG.Proof.Sha256.X86_64.stR s₀] m m') : VG.Proof.Sha256.X86_64.Saved s₀ m' := by
  rcases hf with hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := VG.Proof.Sha256.X86_64.saved_bound p hp'
  · exact Offset.disjoint_base _ (by bdd_omega) (by bdd_omega)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by bdd_omega))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    bswap32 (s₀.mem.readW (VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) =
      W (VG.Proof.Sha256.X86_64.blk s₀ i) t := by
  rw [W_lt _ ht, bswap32_readW, VG.Proof.Sha256.X86_64.ofInt_natCast]
  simp only [VG.Proof.Sha256.X86_64.blk, blockAt, parseBlock]
  rw [show VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) from
      Offset.add_add _ _ 1,
    show VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) from
      Offset.add_add _ _ 1,
    show VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) from
      Offset.add_add _ _ 1]

theorem win_sub (p : Addr) : Region.Sub (VG.Proof.Sha256.X86_64.winRegion p) ⟨p, 560⟩ := Region.sub_prefix (by bdd_omega)

theorem body_ok {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {i : Nat} (hi : i < VG.Proof.Sha256.X86_64.nb s₀) {s : State}
    (hL : VG.Proof.Sha256.X86_64.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha256.X86_64.Common s₀ (VG.Proof.Sha256.X86_64.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Sha256.X86_64.nb s₀ ∧ VG.Proof.Sha256.X86_64.LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [VG.Proof.Sha256.X86_64.winRegion (VG.Proof.Sha256.X86_64.scr s₀)], (VG.Proof.Sha256.X86_64.blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (VG.Proof.Sha256.X86_64.win_sub _)
  have hblk : ∀ m, Frame [VG.Proof.Sha256.X86_64.winRegion (VG.Proof.Sha256.X86_64.scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap32 (m.readW (VG.Proof.Sha256.X86_64.blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W (VG.Proof.Sha256.X86_64.blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact VG.Proof.Sha256.X86_64.blk_word i t ht
  have hrsi₁ : s₁.gpr .rsi = VG.Proof.Sha256.X86_64.blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  have hrcx₁ : s₁.gpr .rcx = VG.Proof.Sha256.X86_64.scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.rounds_ok _ (VG.Proof.Sha256.X86_64.blk s₀ i) _ (VG.Proof.Sha256.X86_64.scr s₀) s₁ hrsi₁ hrcx₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [VG.Proof.Sha256.X86_64.winRegion (VG.Proof.Sha256.X86_64.scr s₀)], (VG.Proof.Sha256.X86_64.stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (VG.Proof.Sha256.X86_64.win_sub _)
  have hrdi₂ : s₂.gpr .rdi = VG.Proof.Sha256.X86_64.st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (VG.Proof.Sha256.X86_64.update_ok hp _ (stateAt s.mem (VG.Proof.Sha256.X86_64.st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (VG.Proof.Sha256.X86_64.contains_offset' (by bdd_omega) (by bdd_omega)) hst (by decide), hm₁,
      VG.Proof.Sha256.X86_64.stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrcx₃, hrsp₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ VG.Proof.Sha256.X86_64.pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (VG.Proof.Sha256.X86_64.nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by bdd_omega), Nat.sub_sub]
  have hframe : Frame [VG.Proof.Sha256.X86_64.stR s₀, VG.Proof.Sha256.X86_64.scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨VG.Proof.Sha256.X86_64.scrR s₀, by simp, by simp at hr; subst hr; exact VG.Proof.Sha256.X86_64.win_sub _⟩) ?_
    rw [hm₃]
    exact (VG.Proof.Sha256.X86_64.frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → VG.Proof.Sha256.X86_64.Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrcx₃, pub₂ .rcx (by decide), hL.rcx],
      by rw [hrsp₃, pub₂ .rsp (by decide), hL.rsp], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, VG.Proof.Sha256.X86_64.stateAt_writeState, VG.Proof.Sha256.X86_64.compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine VG.Proof.Sha256.X86_64.saved_frame hp ?_ (.inr (VG.Proof.Sha256.X86_64.frame_writeState (Frame.refl _ _) _))
      refine VG.Proof.Sha256.X86_64.saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₃]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = VG.Proof.Sha256.X86_64.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : VG.Proof.Sha256.X86_64.nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    refine ⟨?_, by bdd_omega, { hcommon _ rfl with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (VG.Proof.Sha256.X86_64.nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₃, pub₂ .rsi (by decide), hL.rsi]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (VG.Proof.Sha256.X86_64.bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by bdd_omega)))
    · rw [hrdx₃, hrdx]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.Sha256.X86_64.scr s₀) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) :
    WP isa (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Sha256.X86_64.saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rcx saved s₀ fun p hp' => ?_) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  · have := VG.Proof.Sha256.X86_64.saved_bound p hp'
    exact ⟨VG.Proof.Sha256.X86_64.scrR s₀, by simp [hp.wr], Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
      State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hg, hrd, hwr, hm, by rw [hg]⟩

theorem saveMem_saved {s₀ : State} : VG.Proof.Sha256.X86_64.Saved s₀ (VG.Proof.Sha256.X86_64.saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame {s₀ : State} : Frame [VG.Proof.Sha256.X86_64.scrR s₀] s₀.mem (VG.Proof.Sha256.X86_64.saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := VG.Proof.Sha256.X86_64.saved_bound p hp; omega) (by decide)

theorem common_zero {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = VG.Proof.Sha256.X86_64.saveMem s₀) : VG.Proof.Sha256.X86_64.Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact VG.Proof.Sha256.X86_64.saveMem_saved⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply VG.Proof.Sha256.X86_64.stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (VG.Proof.Sha256.X86_64.contains_offset' (off := 4 * k) (len := 32) (by bdd_omega) (by bdd_omega))
      (by simpa using hp.st_scr)
      (by decide), ← VG.Proof.Sha256.X86_64.stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) {s : State} (hc : VG.Proof.Sha256.X86_64.Common s₀ (VG.Proof.Sha256.X86_64.nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  refine WP.mono (Spill.restore_ok .rcx saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := VG.Proof.Sha256.X86_64.saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨VG.Proof.Sha256.X86_64.scrR s₀, by simp [hp.wr], Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩
  · exact ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hc.rsp, by rw [hm]; exact hret⟩,
      by show stateAt _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha256.X86_64.Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha256.X86_64.Common s₀ (VG.Proof.Sha256.X86_64.nb s₀)) ?_ fun s₂ hc => VG.Proof.Sha256.X86_64.restore_ok hp hc)
  have hc₀ := VG.Proof.Sha256.X86_64.common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Sha256.X86_64.nb s₀ = 0 := by simp at h; simp [VG.Proof.Sha256.X86_64.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Sha256.X86_64.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Sha256.X86_64.nb s₀ - i ∧ i < VG.Proof.Sha256.X86_64.nb s₀ ∧ VG.Proof.Sha256.X86_64.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Sha256.X86_64.Common s₀ (VG.Proof.Sha256.X86_64.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Sha256.X86_64.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Sha256.X86_64.nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Sha256.X86_64.LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [VG.Proof.Sha256.X86_64.blkAddr]
        rdx := by rw [hg]; simp [VG.Proof.Sha256.X86_64.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Sha256.X86_64.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Sha256.X86_64.compress Proof.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.Sha256.X86_64.correct (VG.Proof.Sha256.X86_64.pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨VG.Proof.Sha256.X86_64.satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sha256.X86_64

end
