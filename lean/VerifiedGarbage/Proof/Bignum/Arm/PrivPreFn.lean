module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFrame
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Sig

/-! # The callable private precomputation

The caller's frame is saved and `pre` cleared; a second frame pushes the
private CRT's stack arguments, and the CRT's own frame runs the body.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg op2_imm op2_lsl)

/-- The private CRT's arguments: the input and the coefficient are `pre`, the
exponents the factors. -/
def ppGeometry (s : State) : CrtGeometry where
  base := stackArg s 4
  output := s.gpr .r0
  modulus := s.gpr .r2
  input := s.gpr .r0
  p := stackArg s 0
  q := stackArg s 2
  dp := stackArg s 0
  dq := stackArg s 2
  qi := s.gpr .r0
  size := (stackArg s 5).toNat * 8
  length := (s.gpr .r3).toNat
  pLength := (stackArg s 1).toNat
  qLength := (stackArg s 3).toNat

/-- The sources' bytes when the CRT runs: the input and the coefficient cleared. -/
def ppBytes (s : State) (i : Fin 7) : List Byte :=
  if i = 1 ∨ i = 6 then List.replicate ((ppGeometry s).sourceLength i) 0
  else Spec.Rsa.bytesAt s.mem (State.addr ((ppGeometry s).source i)) ((ppGeometry s).sourceLength i)

theorem ppBytes_other (s : State) (i : Fin 7) (h1 : i ≠ 1) (h6 : i ≠ 6) :
    ppBytes s i = Spec.Rsa.bytesAt s.mem (State.addr ((ppGeometry s).source i)) ((ppGeometry s).sourceLength i) := by
  unfold ppBytes
  split
  · next hc => rcases hc with hc | hc <;> contradiction
  · rfl

theorem ppBytes_zero (s : State) (i : Fin 7) (h : i = 1 ∨ i = 6) :
    ppBytes s i = List.replicate ((ppGeometry s).sourceLength i) 0 := by
  unfold ppBytes
  split
  · rfl
  · next hc => exact absurd h hc

/-- The contract's precondition, named. -/
structure PpFnInput (s : State) : Prop where
  stackFit : 168 ≤ s.sp.toNat
  argFit : s.sp.toNat + 24 ≤ 2 ^ 32
  argRead : (⟨State.addr s.sp, 24⟩ : Region) ∈ s.rd
  preW : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ : Region) ∈ s.wr
  wsW : (⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩ : Region) ∈ s.wr
  nR : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd
  pR : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.rd
  qR : (⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ : Region) ∈ s.rd
  preN : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  preP : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  preQ : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  preWs : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
    ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  preArgs : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr s.sp, 24⟩
  nWs : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  pWs : Region.Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  qWs : Region.Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  stPre : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  stN : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  stP : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  stQ : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  stWs : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  stArgs : (FrameStack.belowA s.sp 168).Disjoint ⟨State.addr s.sp, 24⟩
  preFit : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  nFit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  pFit : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  qFit : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  wsFit : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (s.gpr .r3).toNat
  pPositive : 1 ≤ (stackArg s 1).toNat
  pShort : (stackArg s 1).toNat < (s.gpr .r3).toNat
  qPositive : 1 ≤ (stackArg s 3).toNat
  qShort : (stackArg s 3).toNat < (s.gpr .r3).toNat
  preLen : (s.gpr .r1).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r3).toNat (stackArg s 1).toNat (stackArg s 3).toNat
  space : Spec.Rsa.scratchWords (s.gpr .r3).toNat ≤ (stackArg s 5).toNat

theorem pp_contract_pre (s : State) (h : (Spec.Rsa.privatePrecomputeContract abi 168).pre s) :
    PpFnInput s := by
  sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, preN, preP, preQ, preWs, preArgs, nWs, pWs, qWs, _,
    stPre, stN, stP, stQ, stWs, stArgs, preFit, nFit, pFit, qFit, wsFit,
    valid, pPositive, pShort, qPositive, qShort, preLen, space⟩ := h
  have below : FrameStack.belowA s.sp 168 = ⟨State.addr s.sp - BitVec.ofNat 64 168, 168⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨stackFit, argFit, by rw [rd]; simp [State.addr], by rw [wr]; simp [State.addr], by rw [wr]; simp [State.addr],
    by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr],
    preN, preP, preQ, preWs, preArgs, nWs, pWs, qWs, by rw [below]; exact stPre, by rw [below]; exact stN,
    by rw [below]; exact stP, by rw [below]; exact stQ, by rw [below]; exact stWs, by rw [below]; exact stArgs,
    preFit, nFit, pFit, qFit, wsFit, valid, pPositive, pShort, qPositive, qShort, preLen, space⟩

/-! ## Helpers -/

/-- Bytes read as zero are zero. -/
theorem byte_zero_of_read {m : Mem} {a : Addr} {n i : Nat} (h : (m.read a n).toNat = 0) (hi : i < n) :
    m (a + BitVec.ofNat 64 i) = 0 := by
  have split := read_toNat_add m (n - i) i a
  rw [show n - i + i = n by omega, h] at split
  have high : (m.read (a + BitVec.ofNat 64 i) (n - i)).toNat = 0 := by
    have := Nat.two_pow_pos (8 * i)
    rcases Nat.eq_zero_of_add_eq_zero split.symm with ⟨_, h2⟩
    exact (Nat.mul_eq_zero.mp h2).resolve_left (by omega)
  rw [show n - i = n - i - 1 + 1 by omega, read_toNat_succ] at high
  apply BitVec.eq_of_toNat_eq
  have := Nat.eq_zero_of_add_eq_zero high
  exact this.1

theorem bytesAt_zero_of_read {m : Mem} {a : Addr} {n k : Nat} (h : (m.read a n).toNat = 0) (hk : k ≤ n) :
    Spec.Rsa.bytesAt m a k = List.replicate k 0 := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, List.length_replicate]
  · intro i hi _
    have hi' : i < k := by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact byte_zero_of_read h (by omega)

/-- The three frames below the caller's stack pointer: the caller's
registers', the CRT's arguments' and the CRT's own, at `112`, `56` and `0`
bytes above `sp - 168`. -/
theorem pp_stack_addrs {sp : BitVec 32} (fit : 168 ≤ sp.toNat) :
    FrameStack.belowA sp 168 = ⟨State.addr sp - BitVec.ofNat 64 168, 168⟩ ∧
    State.addr (sp - BitVec.ofNat 32 56) = State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 112 ∧
    State.addr (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) =
      State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 56 ∧
    State.addr (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) =
      State.addr sp - BitVec.ofNat 64 168 := by
  have a1 : (sp - BitVec.ofNat 32 56).toNat = sp.toNat - 56 := FrameStack.sub_toNat' (by omega)
  have a2 : (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56).toNat = sp.toNat - 112 := by
    rw [FrameStack.sub_toNat' (by omega), a1]; omega
  have lt := sp.isLt
  have eq (x : BitVec 32) (k : Nat) (hx : x.toNat = sp.toNat - k) (hk : k ≤ 168) :
      State.addr x = State.addr sp - BitVec.ofNat 64 168 + BitVec.ofNat 64 (168 - k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hx]
    omega
  refine ⟨?_, eq _ 56 a1 (by decide), eq _ 112 a2 (by decide), ?_⟩
  · unfold FrameStack.belowA; rw [FrameStack.addr_sub' fit]
  · have := eq (sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) 168
      (by rw [FrameStack.sub_toNat' (by omega), a2]; omega) (by decide)
    simpa only [Nat.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem pp_loadArgs_ok (x : State) (fit : x.sp.toNat + 76 ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ 56 ∨ 56 ≤ d ∧ d + 4 ≤ 76 → InRegions (x.rd ++ x.wr) (off (State.addr x.sp) d) 4) :
    WP isa (.block loadArgs) x fun t =>
      let v := fun d => x.mem.readW (off (State.addr x.sp) d) 32
      t.gpr .r0 = v 0 ∧ t.gpr .r1 = v 12 ∧ t.gpr .r2 = v 56 ∧ t.gpr .r3 = v 60 ∧ t.gpr .r4 = v 64 ∧
      t.gpr .r5 = v 68 ∧ t.gpr .r6 = v 56 ∧ t.gpr .r7 = v 60 ∧ t.gpr .r8 = v 64 ∧ t.gpr .r9 = v 68 ∧
      t.gpr .r10 = v 0 ∧ t.gpr .r11 = v 60 ∧ t.gpr .r12 = v 72 ∧ t.mem = x.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] x t := by
  unfold loadArgs
  have ld (d : Nat) (hd : d + 4 ≤ 76) := addr_add (a := x.sp) (k := d) (by omega)
  refine wp_loadStack (a := off (State.addr x.sp) 0) (by decide) (ld 0 (by decide)) (read 0 (Or.inl (by decide))) fun a1 h1 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 12) (by decide) (by rw [h1.sp]; exact ld 12 (by decide))
    (by rw [h1.rd, h1.wr]; exact read 12 (Or.inl (by decide))) fun a2 h2 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 56) (by decide) (by rw [h2.sp, h1.sp]; exact ld 56 (by decide))
    (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact read 56 (Or.inr ⟨by decide, by decide⟩)) fun a3 h3 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 60) (by decide) (by rw [h3.sp, h2.sp, h1.sp]; exact ld 60 (by decide))
    (by rw [h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 60 (Or.inr ⟨by decide, by decide⟩)) fun a4 h4 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 64) (by decide)
    (by rw [h4.sp, h3.sp, h2.sp, h1.sp]; exact ld 64 (by decide))
    (by rw [h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 64 (Or.inr ⟨by decide, by decide⟩)) fun a5 h5 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 68) (by decide)
    (by rw [h5.sp, h4.sp, h3.sp, h2.sp, h1.sp]; exact ld 68 (by decide))
    (by rw [h5.rd, h5.wr, h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact read 68 (Or.inr ⟨by decide, by decide⟩))
    fun a6 h6 => ?_
  refine wp_mov (op2_reg _ _) fun a7 h7 => ?_
  refine wp_mov (op2_reg _ _) fun a8 h8 => ?_
  refine wp_mov (op2_reg _ _) fun a9 h9 => ?_
  refine wp_mov (op2_reg _ _) fun a10 h10 => ?_
  refine wp_mov (op2_reg _ _) fun a11 h11 => ?_
  refine wp_mov (op2_reg _ _) fun a12 h12 => ?_
  refine wp_loadStack (a := off (State.addr x.sp) 72) (by decide)
    (by rw [h12.sp, h11.sp, h10.sp, h9.sp, h8.sp, h7.sp, h6.sp, h5.sp, h4.sp, h3.sp, h2.sp, h1.sp]
        exact ld 72 (by decide))
    (by rw [h12.rd, h12.wr, h11.rd, h11.wr, h10.rd, h10.wr, h9.rd, h9.wr, h8.rd, h8.wr, h7.rd, h7.wr,
          h6.rd, h6.wr, h5.rd, h5.wr, h4.rd, h4.wr, h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]
        exact read 72 (Or.inr ⟨by decide, by decide⟩)) fun t h13 => WP.block_nil ?_
  have m12 : a12.mem = x.mem := by
    rw [h12.mem, h11.mem, h10.mem, h9.mem, h8.mem, h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  have g6 : a6.gpr .r0 = x.mem.readW (off (State.addr x.sp) 0) 32 ∧ a6.gpr .r1 = x.mem.readW (off (State.addr x.sp) 12) 32 ∧
      a6.gpr .r2 = x.mem.readW (off (State.addr x.sp) 56) 32 ∧ a6.gpr .r3 = x.mem.readW (off (State.addr x.sp) 60) 32 ∧
      a6.gpr .r4 = x.mem.readW (off (State.addr x.sp) 64) 32 ∧ a6.gpr .r5 = x.mem.readW (off (State.addr x.sp) 68) 32 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h6.other .r0 (by decide), h5.other .r0 (by decide), h4.other .r0 (by decide), h3.other .r0 (by decide),
        h2.other .r0 (by decide), h1.gpr]
    · rw [h6.other .r1 (by decide), h5.other .r1 (by decide), h4.other .r1 (by decide), h3.other .r1 (by decide),
        h2.gpr, h1.mem]
    · rw [h6.other .r2 (by decide), h5.other .r2 (by decide), h4.other .r2 (by decide), h3.gpr, h2.mem, h1.mem]
    · rw [h6.other .r3 (by decide), h5.other .r3 (by decide), h4.gpr, h3.mem, h2.mem, h1.mem]
    · rw [h6.other .r4 (by decide), h5.gpr, h4.mem, h3.mem, h2.mem, h1.mem]
    · rw [h6.gpr, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := g6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h13.mem, m12], ?_⟩
  · rw [h13.other .r0 (by decide), h12.other .r0 (by decide), h11.other .r0 (by decide), h10.other .r0 (by decide),
      h9.other .r0 (by decide), h8.other .r0 (by decide), h7.other .r0 (by decide), r0]
  · rw [h13.other .r1 (by decide), h12.other .r1 (by decide), h11.other .r1 (by decide), h10.other .r1 (by decide),
      h9.other .r1 (by decide), h8.other .r1 (by decide), h7.other .r1 (by decide), r1]
  · rw [h13.other .r2 (by decide), h12.other .r2 (by decide), h11.other .r2 (by decide), h10.other .r2 (by decide),
      h9.other .r2 (by decide), h8.other .r2 (by decide), h7.other .r2 (by decide), r2]
  · rw [h13.other .r3 (by decide), h12.other .r3 (by decide), h11.other .r3 (by decide), h10.other .r3 (by decide),
      h9.other .r3 (by decide), h8.other .r3 (by decide), h7.other .r3 (by decide), r3]
  · rw [h13.other .r4 (by decide), h12.other .r4 (by decide), h11.other .r4 (by decide), h10.other .r4 (by decide),
      h9.other .r4 (by decide), h8.other .r4 (by decide), h7.other .r4 (by decide), r4]
  · rw [h13.other .r5 (by decide), h12.other .r5 (by decide), h11.other .r5 (by decide), h10.other .r5 (by decide),
      h9.other .r5 (by decide), h8.other .r5 (by decide), h7.other .r5 (by decide), r5]
  · rw [h13.other .r6 (by decide), h12.other .r6 (by decide), h11.other .r6 (by decide), h10.other .r6 (by decide),
      h9.other .r6 (by decide), h8.other .r6 (by decide), h7.gpr, r2]
  · rw [h13.other .r7 (by decide), h12.other .r7 (by decide), h11.other .r7 (by decide), h10.other .r7 (by decide),
      h9.other .r7 (by decide), h8.gpr, h7.other .r3 (by decide), r3]
  · rw [h13.other .r8 (by decide), h12.other .r8 (by decide), h11.other .r8 (by decide), h10.other .r8 (by decide),
      h9.gpr, h8.other .r4 (by decide), h7.other .r4 (by decide), r4]
  · rw [h13.other .r9 (by decide), h12.other .r9 (by decide), h11.other .r9 (by decide), h10.gpr,
      h9.other .r5 (by decide), h8.other .r5 (by decide), h7.other .r5 (by decide), r5]
  · rw [h13.other .r10 (by decide), h12.other .r10 (by decide), h11.gpr, h10.other .r0 (by decide),
      h9.other .r0 (by decide), h8.other .r0 (by decide), h7.other .r0 (by decide), r0]
  · rw [h13.other .r11 (by decide), h12.gpr, h11.other .r3 (by decide), h10.other .r3 (by decide),
      h9.other .r3 (by decide), h8.other .r3 (by decide), h7.other .r3 (by decide), r3]
  · rw [h13.gpr, m12]
  · have r1' : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] x a6 :=
      (h1.rest (by decide)).trans ((h2.rest (by decide)).trans ((h3.rest (by decide)).trans
        ((h4.rest (by decide)).trans ((h5.rest (by decide)).trans (h6.rest (by decide))))))
    have r2' : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] a6 a12 :=
      (h7.rest (by decide)).trans ((h8.rest (by decide)).trans ((h9.rest (by decide)).trans
        ((h10.rest (by decide)).trans ((h11.rest (by decide)).trans (h12.rest (by decide))))))
    exact r1'.trans (r2'.trans (h13.rest (by decide)))

theorem pp_preWords {s : State} (h : PpFnInput s) : (s.gpr .r1).toNat = ppPreWords (ppGeometry s) := by
  rw [h.preLen]; rfl

/-- The facts of `PpFnInput` its steps share: `pre`'s `P` words, and the
`168` bytes of stack from `B`, apart from every buffer. -/
structure PpLayout (s : State) (B : Addr) (P : Nat) : Prop where
  hPw : ppPreWords (ppGeometry s) = P
  hP : (s.gpr .r1).toNat = P
  lenP : (s.gpr .r1).toNat * 8 = 8 * P
  preFit : (s.gpr .r0).toNat + 8 * P ≤ 2 ^ 32
  a1 : State.addr (s.sp - BitVec.ofNat 32 56) = B + BitVec.ofNat 64 112
  a2 : State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) = B + BitVec.ofNat 64 56
  a3 : State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 - BitVec.ofNat 32 56) = B
  Bnat : B.toNat = s.sp.toNat - 168
  spB : State.addr s.sp = B + BitVec.ofNat 64 168
  preD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (s.gpr .r0), 8 * P⟩
  nD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  pD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  qD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  wsD : Region.Disjoint ⟨B, 168⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩
  preW : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region) ∈ s.wr

theorem pp_layout (s : State) (h : PpFnInput s) :
    PpLayout s (State.addr s.sp - BitVec.ofNat 64 168) (ppPreWords (ppGeometry s)) := by
  have hP := pp_preWords h
  have lenP : (s.gpr .r1).toNat * 8 = 8 * ppPreWords (ppGeometry s) := by rw [hP]; omega
  obtain ⟨below168, a1, a2, a3⟩ := pp_stack_addrs h.stackFit
  refine ⟨rfl, hP, lenP, by have := h.preFit; omega, a1, a2, a3, ?_, (BitVec.sub_add_cancel _ _).symm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.stackFit
    simp only [State.addr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · have := h.stPre; rw [below168, lenP] at this; exact this
  · have := h.stN; rw [below168] at this; exact this
  · have := h.stP; rw [below168] at this; exact this
  · have := h.stQ; rw [below168] at this; exact this
  · have := h.stWs; rw [below168] at this; exact this
  · have := h.preW; rw [lenP] at this; exact this

theorem PpLayout.stackSub {s : State} {B : Addr} {P : Nat} (_L : PpLayout s B P) (k : Nat) (hk : k + 56 ≤ 168) :
    Region.Sub ⟨B + BitVec.ofNat 64 k, 56⟩ ⟨B, 168⟩ := Offset.sub_base _ hk

/-- The frame that saves the caller's registers. -/
theorem PpLayout.frame1 {s : State} {B : Addr} {P : Nat} (L : PpLayout s B P) (h : PpFnInput s) :
    Frame [⟨B + BitVec.ofNat 64 112, 56⟩] s.mem (pcPushed s).mem := by
  have := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (s := s)
    (by show 56 ≤ _; have := h.stackFit; omega)
  unfold FrameStack.belowA at this
  rw [show 4 * List.length [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] = 56
    from rfl, L.a1] at this
  exact this

/-! ### `pre` cleared -/

def PpZeroReady (s : State) (P : Nat) (v : State) : Prop :=
  v.gpr .r0 = s.gpr .r0 ∧ v.gpr .lr = BitVec.ofNat 32 (2 * P) ∧ v.gpr .r3 = 0 ∧ v.mem = (pcPushed s).mem ∧
    Rest [.lr, .r3] (pcPushed s) v

theorem pp_zeroArgs_ok (s : State) {B : Addr} {P : Nat} (L : PpLayout s B P) :
    WP isa (.block zeroArgs) (pcPushed s) (PpZeroReady s P) := by
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => WP.block_nil ?_
  refine ⟨?_, ?_, by rw [b.gpr], by rw [b.mem, a.mem], (a.rest (by decide)).trans (b.rest (by decide))⟩
  · rw [b.other .r0 (by decide), a.other .r0 (by decide)]; simp
  · rw [b.other .lr (by decide), a.gpr]
    change s.gpr .r1 <<< 1 = _
    have e : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by simp
    rw [e, shl_ofNat, L.hP]

structure PpZeroed (s : State) (P : Nat) (w : State) : Prop where
  rest : Rest [.r0, .lr, .r3] (pcPushed s) w
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩] (pcPushed s).mem w.mem
  zero : (w.mem.read (State.addr (s.gpr .r0)) (8 * P)).toNat = 0

theorem pp_zero_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (v : State)
    (hv : PpZeroReady s P v) : WP isa zero v (PpZeroed s P) := by
  obtain ⟨r0, lr, r3, memV, restV⟩ := hv
  refine WP.mono (zero_ok v (base := s.gpr .r0) (size := 8 * P) (o := 0) (n := 2 * P)
    ⟨L.preFit, by omega, ?_⟩ (by have := h.pPositive; rw [← L.hPw]; simp only [ppPreWords, ppWords]; omega)
    (by rw [r0]; simp) lr r3) ?_
  · rw [restV.wr]; exact ⟨_, List.mem_cons_of_mem _ L.preW, Region.contains_self _ _⟩
  rintro w ⟨_, _, _, outside, value, restW⟩
  refine ⟨(restV.mono (by decide)).trans (restW.mono (by decide)), ?_, ?_⟩
  · have := outside_frame outside (by have := L.preFit; omega)
    rw [memV, show 4 * (2 * P) = 8 * P by omega] at this
    simpa only [off, BitVec.add_zero] using this
  · have := read_eq_val32 w.mem (State.addr (s.gpr .r0)) (2 * P) 0
    rw [value, show 4 * (2 * P) = 8 * P by omega] at this
    simpa only [off, BitVec.add_zero] using this

/-! ### The CRT's stack arguments in registers -/

structure PpLoaded (s : State) (P : Nat) (x : State) : Prop where
  rest : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] (pcPushed s) x
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩] (pcPushed s).mem x.mem
  zero : (x.mem.read (State.addr (s.gpr .r0)) (8 * P)).toNat = 0
  saved : Spill.Saved x.mem (State.addr x.sp) s.gpr pcAllSaved
  r0 : x.gpr .r0 = s.gpr .r0
  r1 : x.gpr .r1 = s.gpr .r3
  r2 : x.gpr .r2 = stackArg s 0
  r3 : x.gpr .r3 = stackArg s 1
  r4 : x.gpr .r4 = stackArg s 2
  r5 : x.gpr .r5 = stackArg s 3
  r6 : x.gpr .r6 = stackArg s 0
  r7 : x.gpr .r7 = stackArg s 1
  r8 : x.gpr .r8 = stackArg s 2
  r9 : x.gpr .r9 = stackArg s 3
  r10 : x.gpr .r10 = s.gpr .r0
  r11 : x.gpr .r11 = stackArg s 1
  r12 : x.gpr .r12 = stackArg s 4

theorem pp_load_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (w : State)
    (hw : PpZeroed s P w) : WP isa (.block loadArgs) w (PpLoaded s P) := by
  have stackFit := h.stackFit
  have argFit := h.argFit
  have restW := hw.rest
  have spW : w.sp = s.sp - BitVec.ofNat 32 56 := by rw [restW.sp]; rfl
  have argAddr (d : Nat) (hd : d + 4 ≤ 24) :
      off (State.addr w.sp) (56 + d) = off (State.addr s.sp) d := by
    rw [spW]; exact public_push_argOffset (s := s) (by omega) d
  have savedW : Spill.Saved w.mem (State.addr w.sp) s.gpr pcAllSaved := by
    rw [spW]
    refine (pc_push_saved s (by omega)).frame (lo := 0) (hi := 56) (by decide) hw.frame ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [BitVec.add_zero]
    have e : State.addr (s.sp - 56) = B + BitVec.ofNat 64 112 := L.a1
    rw [e]
    exact L.preD.sub_left (L.stackSub 112 (by decide))
  have argW (i : Nat) (hi : 4 * i + 4 ≤ 24) :
      w.mem.readW (off (State.addr w.sp) (56 + 4 * i)) 32 = stackArg s i := by
    rw [argAddr (4 * i) hi]
    have keep1 : w.mem.readW (off (State.addr s.sp) (4 * i)) 32 = (pcPushed s).mem.readW (off (State.addr s.sp) (4 * i)) 32 :=
      hw.frame.readW (r := ⟨off (State.addr s.sp) (4 * i), 4⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          have := h.preArgs; rw [L.lenP] at this
          exact (this.symm.sub_left (Offset.sub_base _ hi))) (by decide)
    have keep2 : (pcPushed s).mem.readW (off (State.addr s.sp) (4 * i)) 32 = s.mem.readW (off (State.addr s.sp) (4 * i)) 32 :=
      (L.frame1 h).readW (r := ⟨off (State.addr s.sp) (4 * i), 4⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          have := L.Bnat
          simp only [off]; rw [L.spB, BitVec.add_assoc, ← BitVec.ofNat_add]
          exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)) (by decide)
    rw [keep1, keep2]
    unfold stackArg stackArgAddr
    rw [addr_add (by omega)]
  refine WP.mono (pp_loadArgs_ok w (by rw [spW, FrameStack.sub_toNat' (by omega)]; omega) ?_) ?_
  · intro d hd
    rcases hd with low | ⟨high, hd⟩
    · refine ⟨_, List.mem_append_right _ ?_, Offset.contains_base _ low (by omega)⟩
      rw [restW.wr, spW]; exact List.mem_cons_self
    · have e := argAddr (d - 56) (by omega)
      rw [show 56 + (d - 56) = d by omega] at e
      rw [e, restW.rd]
      exact ⟨_, List.mem_append_left _ h.argRead, Offset.contains_base _ (by omega) (by omega)⟩
  rintro x ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, memX, restX⟩
  dsimp only at x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
  have sv (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      w.mem.readW (off (State.addr w.sp) d) 32 = s.gpr r := savedW (r, d) hr
  rw [sv .r0 0 (by decide)] at x0 x10
  rw [sv .r3 12 (by decide)] at x1
  rw [show (56 : Nat) = 56 + 4 * 0 from rfl, argW 0 (by decide)] at x2 x6
  rw [show (60 : Nat) = 56 + 4 * 1 from rfl, argW 1 (by decide)] at x3 x7 x11
  rw [show (64 : Nat) = 56 + 4 * 2 from rfl, argW 2 (by decide)] at x4 x8
  rw [show (68 : Nat) = 56 + 4 * 3 from rfl, argW 3 (by decide)] at x5 x9
  rw [show (72 : Nat) = 56 + 4 * 4 from rfl, argW 4 (by decide)] at x12
  refine ⟨(restW.mono (by decide)).trans (restX.mono (by decide)), by rw [memX]; exact hw.frame, by rw [memX]; exact hw.zero,
    by rw [memX, restX.sp]; exact savedW, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩

/-! ### The CRT's stack arguments pushed, and its register arguments -/

structure PpCalled (s : State) (B : Addr) (P : Nat) (y : State) : Prop where
  input : CrtFnInput (ppGeometry s) (ppBytes s) y
  call : PpCall (ppGeometry s) y
  sp : y.sp = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56
  wr : y.wr = ⟨State.addr y.sp, 56⟩ :: ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr
  frame : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩] (pcPushed s).mem y.mem

theorem pp_call_ok (s : State) (h : PpFnInput s) {B : Addr} {P : Nat} (L : PpLayout s B P) (x : State)
    (hx : PpLoaded s P x) : WP isa (.block callArgs) (pcPushed x) (PpCalled s B P) := by
  have stackFit := h.stackFit
  have argFit := h.argFit
  have hPw := L.hPw
  have preFit := L.preFit
  have Bnat := L.Bnat
  have preD := L.preD
  have nD := L.nD
  have pD := L.pD
  have qD := L.qD
  have wsD := L.wsD
  have preW := L.preW
  have lenP := L.lenP
  have stackSub := L.stackSub
  have restX := hx.rest
  have spX : x.sp = s.sp - BitVec.ofNat 32 56 := by rw [restX.sp]; rfl
  have spXnat : x.sp.toNat = s.sp.toNat - 56 := by rw [spX, FrameStack.sub_toNat' (by omega)]
  have frameY0 : Frame [⟨B + BitVec.ofNat 64 56, 56⟩] x.mem (pcPushed x).mem := by
    have := FrameStack.pushed_frameA
      (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (s := x) (by show 56 ≤ _; omega)
    unfold FrameStack.belowA at this
    rw [show 4 * List.length [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr] = 56
      from rfl, spX, L.a2] at this
    exact this
  have outerY0 (d : Nat) (hd : d + 4 ≤ 56) :
      (pcPushed x).mem.readW (off (State.addr (pcPushed x).sp) (56 + d)) 32 = x.mem.readW (off (State.addr x.sp) d) 32 := by
    rw [public_push_argOffset (by omega) d]
    refine frameY0.readW (r := ⟨off (State.addr x.sp) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    simp only [off]; rw [spX, L.a1, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
  have outerW (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      x.mem.readW (off (State.addr x.sp) d) 32 = s.gpr r := hx.saved (r, d) hr
  unfold callArgs
  have rd0 (d : Nat) (hd : 56 + d + 4 ≤ 112) : InRegions ((pcPushed x).rd ++ (pcPushed x).wr)
      (off (State.addr (pcPushed x).sp) (56 + d)) 4 := by
    rw [public_push_argOffset (by omega) d]
    refine ⟨⟨State.addr x.sp, 56⟩, List.mem_append_right _ (List.mem_cons_of_mem _ ?_),
      Offset.contains_base _ (by omega) (by omega)⟩
    rw [restX.wr, spX]; exact List.mem_cons_self
  have sp0 : (pcPushed x).sp.toNat + 112 ≤ 2 ^ 32 := by
    change (x.sp - BitVec.ofNat 32 56).toNat + 112 ≤ _; rw [FrameStack.sub_toNat' (by omega)]; omega
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 0)) (by decide) (addr_add (by omega)) (rd0 0 (by decide))
    fun y1 c1 => ?_
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 8)) (by decide)
    (by rw [c1.sp]; exact addr_add (by omega)) (by rw [c1.rd, c1.wr]; exact rd0 8 (by decide)) fun y2 c2 => ?_
  refine wp_loadStack (a := off (State.addr (pcPushed x).sp) (56 + 12)) (by decide)
    (by rw [c2.sp, c1.sp]; exact addr_add (by omega)) (by rw [c2.rd, c2.wr, c1.rd, c1.wr]; exact rd0 12 (by decide))
    fun y c3 => WP.block_nil ?_
  have memY : y.mem = (pcPushed x).mem := by rw [c3.mem, c2.mem, c1.mem]
  have spY : y.sp = (pcPushed x).sp := by rw [c3.sp, c2.sp, c1.sp]
  have y0 : y.gpr .r0 = s.gpr .r0 := by
    rw [c3.other .r0 (by decide), c2.other .r0 (by decide), c1.gpr, outerY0 0 (by decide)]
    exact outerW .r0 0 (by decide)
  have y2 : y.gpr .r2 = s.gpr .r2 := by
    rw [c3.other .r2 (by decide), c2.gpr, c1.mem, outerY0 8 (by decide)]
    exact outerW .r2 8 (by decide)
  have y3 : y.gpr .r3 = s.gpr .r3 := by
    rw [c3.gpr, c2.mem, c1.mem, outerY0 12 (by decide)]
    exact outerW .r3 12 (by decide)
  have spY' : y.sp = s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56 := by rw [spY, ← spX]; rfl
  have addrY : State.addr y.sp = B + BitVec.ofNat 64 56 := by rw [spY', L.a2]
  have belowY : FrameStack.belowA y.sp 56 = ⟨B, 56⟩ := by
    unfold FrameStack.belowA; rw [spY', L.a3]
  have ySpNat : y.sp.toNat = s.sp.toNat - 112 := by
    rw [spY', FrameStack.sub_toNat' (by rw [FrameStack.sub_toNat' (by omega)]; omega),
      FrameStack.sub_toNat' (by omega)]; omega
  have wrY : y.wr = ⟨State.addr y.sp, 56⟩ :: ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ :: s.wr := by
    rw [c3.wr, c2.wr, c1.wr, spY]; change ⟨_, 56⟩ :: x.wr = _; rw [restX.wr]; rfl
  have rdY : y.rd = s.rd := by rw [c3.rd, c2.rd, c1.rd]; change x.rd = _; rw [restX.rd]; rfl
  have slotY (r : Reg) (d : Nat) (hr : (r, d) ∈ pcAllSaved) :
      y.mem.readW (off (State.addr y.sp) d) 32 = x.gpr r := by
    rw [memY, spY]; exact pc_push_saved x (by omega) (r, d) hr
  have frameSY : Frame [⟨B + BitVec.ofNat 64 112, 56⟩, ⟨State.addr (s.gpr .r0), 8 * P⟩,
      ⟨B + BitVec.ofNat 64 56, 56⟩] s.mem y.mem := by
    have f2 : Frame [⟨B + BitVec.ofNat 64 112, 56⟩, ⟨State.addr (s.gpr .r0), 8 * P⟩,
      ⟨B + BitVec.ofNat 64 56, 56⟩] (pcPushed s).mem x.mem := hx.frame.mono (by simp)
    rw [memY]
    exact ((L.frame1 h).mono (by simp)).trans (f2.trans (frameY0.mono (by simp)))
  have nLe : (s.gpr .r3).toNat ≤ 8 * P := by
    rw [← hPw]; simp only [ppPreWords, ppGeometry, CrtGeometry.words, Spec.Rsa.modulusWords]; omega
  have pLe : (stackArg s 1).toNat ≤ 8 * P := by have := h.pShort; omega
  have preCont (k : Nat) (hk : k ≤ 8 * P) : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region).Contains (State.addr (s.gpr .r0)) k := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have zeroBytesY (k : Nat) (hk : k ≤ 8 * P) :
      Spec.Rsa.bytesAt y.mem (State.addr (s.gpr .r0)) k = List.replicate k 0 := by
    rw [memY, Proof.Rsa.rsa_bytes_frame frameY0 (by omega)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact ((preD.sub_left (stackSub 56 (by decide))).sub_right (Region.sub_prefix hk)).symm)]
    exact bytesAt_zero_of_read hx.zero hk
  have keptBytes {a : BitVec 32} {k : Nat} (fit : k < 2 ^ 64)
      (stack : Region.Disjoint ⟨B, 168⟩ ⟨State.addr a, k⟩)
      (pre : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr a, k⟩) :
      Spec.Rsa.bytesAt y.mem (State.addr a) k = Spec.Rsa.bytesAt s.mem (State.addr a) k := by
    refine Proof.Rsa.rsa_bytes_frame frameSY fit fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (stack.sub_left (stackSub 112 (by decide))).symm
    · exact pre.symm
    · exact (stack.sub_left (stackSub 56 (by decide))).symm
  have preN : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ := by
    have := h.preN; rw [lenP] at this; exact this
  have preP' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
    have := h.preP; rw [lenP] at this; exact this
  have preQ' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ := by
    have := h.preQ; rw [lenP] at this; exact this
  have preWs' : Region.Disjoint ⟨State.addr (s.gpr .r0), 8 * P⟩ ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩ := by
    have := h.preWs; rw [lenP] at this; exact this
  have preMem : (⟨State.addr (s.gpr .r0), 8 * P⟩ : Region) ∈ y.wr := by
    rw [wrY]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ preW)
  have hIn : CrtFnInput (ppGeometry s) (ppBytes s) y := by
    refine {
      workspace := ⟨h.wsFit, by rw [wrY]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h.wsW)⟩
      lengthValid := h.valid
      storageFits := by
        have := crt_layout_fits h.valid; have := h.space
        change Impl.Bignum.Arm.Crt.totalBytes (Spec.Rsa.modulusWords (s.gpr .r3).toNat) ≤ (stackArg s 5).toNat * 8
        omega
      pPositive := by have := h.pPositive; change 0 < (stackArg s 1).toNat; omega
      pShort := h.pShort
      qPositive := by have := h.qPositive; change 0 < (stackArg s 3).toNat; omega
      qShort := h.qShort
      source := ?_
      sourceSeparate := ?_
      outputFits := by change (s.gpr .r0).toNat + (s.gpr .r3).toNat ≤ _; omega
      write := ⟨_, preMem, preCont _ nLe⟩
      outputSeparate := (preWs'.symm.sub_right (Region.sub_prefix nLe))
      output := y0
      modulus := y2
      count := by rw [y3]; change s.gpr .r3 = BitVec.ofNat 32 (s.gpr .r3).toNat; simp
      stackFit := by omega
      argFit := by omega
      argRead := ⟨⟨State.addr y.sp, 56⟩, List.mem_append_right _ (by rw [wrY]; exact List.mem_cons_self),
        Region.contains_self _ _⟩
      pointer := ?_
      length := ?_
      workspaceArg := by rw [slotY .r12 48 (by decide), hx.r12]; rfl
      stackWorkspace := by rw [belowY]; exact wsD.sub_left (Region.sub_prefix (by decide))
      argsWorkspace := by rw [addrY]; exact wsD.sub_left (stackSub 56 (by decide))
      stackSource := ?_
      stackOutput := by rw [belowY]; exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix nLe)
      stackArgs := by
        rw [belowY, addrY]
        exact (Offset.disjoint_base B (Nat.le_refl 56) (by omega)).symm }
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨h.nFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.nR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := s.gpr .r2) (by omega) nD preN).trans (ppBytes_other s 0 (by decide) (by decide)).symm
      · refine ⟨by change (s.gpr .r0).toNat + (s.gpr .r3).toNat ≤ _; omega,
          ⟨_, List.mem_append_right _ preMem, preCont _ nLe⟩, ?_⟩
        exact (zeroBytesY _ nLe).trans (ppBytes_zero s 1 (Or.inl rfl)).symm
      · refine ⟨h.pFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.pR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 0) (by omega) pD preP').trans (ppBytes_other s 2 (by decide) (by decide)).symm
      · refine ⟨h.qFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.qR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 2) (by omega) qD preQ').trans (ppBytes_other s 3 (by decide) (by decide)).symm
      · refine ⟨h.pFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.pR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 0) (by omega) pD preP').trans (ppBytes_other s 4 (by decide) (by decide)).symm
      · refine ⟨h.qFit, ⟨_, List.mem_append_left _ (by rw [rdY]; exact h.qR), Region.contains_self _ _⟩, ?_⟩
        exact (keptBytes (a := stackArg s 2) (by omega) qD preQ').trans (ppBytes_other s 5 (by decide) (by decide)).symm
      · refine ⟨by change (s.gpr .r0).toNat + (stackArg s 1).toNat ≤ _; omega,
          ⟨_, List.mem_append_right _ preMem, preCont _ pLe⟩, ?_⟩
        exact (zeroBytesY _ pLe).trans (ppBytes_zero s 6 (Or.inr rfl)).symm
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.nWs
      · exact preWs'.sub_left (Region.sub_prefix nLe)
      · exact h.pWs
      · exact h.qWs
      · exact h.pWs
      · exact h.qWs
      · exact preWs'.sub_left (Region.sub_prefix pLe)
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · change y.mem.readW (off (State.addr y.sp) 0) 32 = _
        rw [slotY .r0 0 (by decide), hx.r0]; rfl
      · change y.mem.readW (off (State.addr y.sp) 8) 32 = _
        rw [slotY .r2 8 (by decide), hx.r2]; rfl
      · change y.mem.readW (off (State.addr y.sp) 16) 32 = _
        rw [slotY .r4 16 (by decide), hx.r4]; rfl
      · change y.mem.readW (off (State.addr y.sp) 24) 32 = _
        rw [slotY .r6 24 (by decide), hx.r6]; rfl
      · change y.mem.readW (off (State.addr y.sp) 32) 32 = _
        rw [slotY .r8 32 (by decide), hx.r8]; rfl
      · change y.mem.readW (off (State.addr y.sp) 40) 32 = _
        rw [slotY .r10 40 (by decide), hx.r10]; rfl
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · change y.mem.readW (off (State.addr y.sp) 4) 32 = _
        rw [slotY .r1 4 (by decide), hx.r1]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 12) 32 = _
        rw [slotY .r3 12 (by decide), hx.r3]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 20) 32 = _
        rw [slotY .r5 20 (by decide), hx.r5]
        change _ = BitVec.ofNat 32 (stackArg s 3).toNat; simp
      · change y.mem.readW (off (State.addr y.sp) 28) 32 = _
        rw [slotY .r7 28 (by decide), hx.r7]; simp [ppGeometry, CrtGeometry.sourceLength]
      · change y.mem.readW (off (State.addr y.sp) 36) 32 = _
        rw [slotY .r9 36 (by decide), hx.r9]
        change _ = BitVec.ofNat 32 (stackArg s 3).toNat; simp
      · change y.mem.readW (off (State.addr y.sp) 44) 32 = _
        rw [slotY .r11 44 (by decide), hx.r11]; simp [ppGeometry, CrtGeometry.sourceLength]
    · intro i
      rw [belowY]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact nD.sub_left (Region.sub_prefix (by decide))
      · exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix nLe)
      · exact pD.sub_left (Region.sub_prefix (by decide))
      · exact qD.sub_left (Region.sub_prefix (by decide))
      · exact pD.sub_left (Region.sub_prefix (by decide))
      · exact qD.sub_left (Region.sub_prefix (by decide))
      · exact (preD.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix pLe)
  have hCall : PpCall (ppGeometry s) y := by
    refine ⟨by rw [hPw]; exact preFit, by rw [hPw]; exact ⟨_, preMem, Region.contains_self _ _⟩,
      by rw [hPw]; exact preWs'.symm, by rw [hPw, belowY]; exact preD.sub_left (Region.sub_prefix (by decide)),
      by rw [hPw, addrY]; exact preD.sub_left (stackSub 56 (by decide)), ?_, rfl, rfl, ?_⟩
    · intro i h1 h6
      rw [hPw]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact preN.symm
      · exact absurd rfl h1
      · exact preP'.symm
      · exact preQ'.symm
      · exact preP'.symm
      · exact preQ'.symm
      · exact absurd rfl h6
    · rw [hPw, memY, Proof.Rsa.wordsAt_frame frameY0 (by omega)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact (preD.sub_left (stackSub 56 (by decide))).symm)]
      exact VG.Proof.Bignum.wordsAt_zero_read hx.zero
  refine ⟨hIn, hCall, spY', wrY, ?_⟩
  rw [memY]
  exact (hx.frame.mono (by simp)).trans (frameY0.mono (by simp))

/-- The callable precomputation: the caller's registers kept, and the CRT's result. -/
theorem ppFn_ok (s : State) (h : PpFnInput s) :
    WP isa code s fun t => abiPreserved s t ∧
      t.gpr .r0 = (if ppGood (ppGeometry s) (ppBytes s) then 1 else 0) ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) (ppPreWords (ppGeometry s)) =
        (if ppGood (ppGeometry s) (ppBytes s) then ppValues (ppGeometry s) (ppBytes s)
         else List.replicate (ppPreWords (ppGeometry s)) 0) := by
  have L := pp_layout s h
  generalize hP : ppPreWords (ppGeometry s) = P at L ⊢
  generalize hB : State.addr s.sp - BitVec.ofNat 64 168 = B at L
  have stackFit := h.stackFit
  have argFit := h.argFit
  have Bnat := L.Bnat
  have preD := L.preD
  have wsD := L.wsD
  have stackSub := L.stackSub
  unfold code
  refine WP.frame (by decide) (by show 56 ≤ _; omega) (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_zeroArgs_ok s L) fun v hv => ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_zero_ok s h L v hv) fun w hw => ?_
  rw [WP.seq_iff]
  refine WP.mono (pp_load_ok s h L w hw) fun x hx => ?_
  have spX : x.sp = s.sp - BitVec.ofNat 32 56 := by rw [hx.rest.sp]; rfl
  rw [WP.seq_iff]
  unfold argsFrame
  refine WP.frame (by decide) (by show 56 ≤ _; rw [spX, FrameStack.sub_toNat' (by omega)]; omega) (by decide) ?_
  change WP isa _ (pcPushed x) _
  rw [WP.seq_iff]
  refine WP.mono (pp_call_ok s h L x hx) fun y hy => ?_
  have belowY : FrameStack.belowA y.sp 56 = ⟨B, 56⟩ := by
    unfold FrameStack.belowA; rw [hy.sp, L.a3]
  refine WP.mono (pp_crtFrame_ok y hy.input hy.call) ?_
  rintro z ⟨r0z, wordsz, spz, wrz, _, frameZ⟩
  rw [L.hPw] at wordsz frameZ
  -- The CRT's arguments popped, and the caller's registers restored.
  have zsp : (popped .r12 56 z).sp = s.sp - BitVec.ofNat 32 56 := by
    rw [popped_sp, spz, hy.sp]; exact BitVec.sub_add_cancel _ _
  have saved : Spill.Saved (popped .r12 56 z).mem (State.addr (popped .r12 56 z).sp) s.gpr pcCalleeSaved := by
    rw [popped_mem, zsp]
    have base := pc_push_callee_saved s (by omega)
    have outer : (⟨State.addr (s.sp - 56) + BitVec.ofNat 64 0, 56 - 0⟩ : Region) = ⟨B + BitVec.ofNat 64 112, 56⟩ := by
      rw [BitVec.add_zero]; exact congrArg (Region.mk · 56) L.a1
    have f1 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
        ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] (pcPushed s).mem z.mem := by
      have g1 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
          ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] (pcPushed s).mem y.mem := hy.frame.mono (by simp)
      have g3 : Frame [⟨State.addr (s.gpr .r0), 8 * P⟩, ⟨B + BitVec.ofNat 64 56, 56⟩, ⟨B, 56⟩,
          ⟨State.addr (stackArg s 4), (stackArg s 5).toNat * 8⟩] y.mem z.mem := by
        rw [belowY] at frameZ
        refine frameZ.mono ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl
        · simp
        · simp [ppGeometry]
        · simp [ppGeometry]
      exact g1.trans g3
    refine base.frame (lo := 0) (hi := 56) (by decide) f1 ?_
    rw [outer]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact preD.sub_left (stackSub 112 (by decide))
    · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact wsD.sub_left (stackSub 112 (by decide))
  have fitR : (popped .r12 56 z).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [zsp, FrameStack.sub_toNat' (by omega)]; omega
  have readR : InRegions ((popped .r12 56 z).rd ++ (popped .r12 56 z).wr) (State.addr (popped .r12 56 z).sp) 56 := by
    refine ⟨⟨State.addr (popped .r12 56 z).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [popped_wr, wrz, hy.wr, zsp]; exact List.mem_cons_self
  refine WP.mono (pc_restore_ok (popped .r12 56 z) s.gpr fitR readR saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = z.gpr .r0 := by rw [restT.gpr .r0 (by decide), popped_gpr (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, zsp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret, r0z]
  · rw [popped_mem, memT, popped_mem]; exact wordsz

/-! ## Against the specification -/

theorem os2ip_replicate_zero : ∀ k, Spec.Rsa.os2ip (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ', Spec.Rsa.os2ip, List.foldl_append, ← Spec.Rsa.os2ip, os2ip_replicate_zero k]
    rfl

theorem pp_result (s : State) (h : PpFnInput s) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat) =
    if ppGood (ppGeometry s) (ppBytes s) then some (ppValues (ppGeometry s) (ppBytes s)) else none := by
  have b0 : ppBytes s 0 = Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat :=
    ppBytes_other s 0 (by decide) (by decide)
  have b1 : ppBytes s 1 = List.replicate (s.gpr .r3).toNat 0 := ppBytes_zero s 1 (Or.inl rfl)
  have b2 : ppBytes s 2 = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    ppBytes_other s 2 (by decide) (by decide)
  have b3 : ppBytes s 3 = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
    ppBytes_other s 3 (by decide) (by decide)
  have b6 : ppBytes s 6 = List.replicate (stackArg s 1).toNat 0 := ppBytes_zero s 6 (Or.inr rfl)
  have ln := bytesAt_length s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have lp := bytesAt_length s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  have lq := bytesAt_length s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat
  generalize Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = nb at b0 ln
  generalize Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat = pb at b2 lp
  generalize Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat = qb at b3 lq
  simp only [ppGood, crtAccepted, ppValues, b0, b1, b2, b3, b6, os2ip_replicate_zero]
  unfold Spec.Rsa.privatePrecompute
  by_cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) (s.gpr .r3).toNat = true
  · obtain ⟨_, gt, _⟩ := valid_facts hv h.valid.1
    by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
    · have pPos : 0 < Spec.Rsa.os2ip pb := by
        rcases Nat.eq_zero_or_pos (Spec.Rsa.os2ip pb) with h0 | h0
        · rw [h0, Nat.zero_mul] at hpq; omega
        · exact h0
      rw [VG.Proof.Bignum.publicPrecompute_some ln hv]
      have ne : Spec.Rsa.os2ip nb ≠ 0 := by omega
      simp [hpq, hv, ne, pPos, Spec.Rsa.primeR2, lp, lq, ppWords, Spec.Rsa.primeWords, ppGeometry,
        CrtGeometry.words, Spec.Rsa.modulusWords]
    · simp [hpq]
  · have none : Spec.Rsa.publicPrecompute nb = none := by simp [Spec.Rsa.publicPrecompute, ln, hv]
    simp only [none, Option.map_none, ite_self]
    split
    · next hg => exact absurd hg.1 hv
    · rfl

theorem pp_contract_correct (s : State) (h : (Spec.Rsa.privatePrecomputeContract abi 168).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.privatePrecomputeContract abi 168).post s t := by
  have hi := pp_contract_pre s h
  obtain ⟨tr, t, run, preserved, r0, words⟩ := ppFn_ok s hi
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, reduceClassify, Loc.val]
  have e := pp_result s hi
  simp only [State.addr] at e words
  rw [e, pp_preWords hi, BitVec.setWidth_append_eq_right]
  by_cases good : ppGood (ppGeometry s) (ppBytes s)
  · simp only [good, ite_true] at r0 words ⊢
    exact ⟨r0, words⟩
  · simp only [good, ite_false] at r0 words ⊢
    exact ⟨r0, words⟩

end VG.Proof.Bignum.Arm
