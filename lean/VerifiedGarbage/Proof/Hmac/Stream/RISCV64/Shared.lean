module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# HMAC over any streaming hash function on RISC-V: the shared contracts

The generic proofs (`Init.correct`, `Finalize.correct`) are written against
`initG` and `finG`, with the bytes of stack the code and its callees use
(the frame and the callees' `F` bytes below it); with each hash function's
constant time (checked for its code) they are moved to the shared contracts
of `Spec/Hmac/Generic.lean` (`generic_implies`), for any instance `I` of the
hash function, with that stack.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Shared

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- The initial taint of `init` and `finalize`: only the arguments are
public. -/
theorem agree {s₁ s₂ : State}
    (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [p0, p1, p2, p3]

theorem initImp {I : Spec.Hmac.Instance} {n : Nat}
    (hs : ∃ s, (I.initAnyKeyContract RISCV64.abi (n + 1)).pre s) :
    (initG I.S (n + 1)).Implies (I.initAnyKeyContract RISCV64.abi (n + 1)) := by
  generic_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, initG, RISCV64.abi, RISCV64.argRegs] using hs

theorem finImp {I : Spec.Hmac.Instance} {n : Nat}
    (hs : ∃ s, (I.finalizeContract RISCV64.abi (n + 1)).pre s) :
    (finG I.S (n + 1)).Implies (I.finalizeContract RISCV64.abi (n + 1)) := by
  generic_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.finalizePost, finG, RISCV64.abi, RISCV64.argRegs] using hs

variable {H : Hash} (hH : HashOK H) {I : Spec.Hmac.Instance} (hSH : hH.SH = I.S)
include hSH

/-- `init` against the shared contract, given its constant time. -/
theorem init
    (ct : ConstantTime isa (initG hH.SH (H.ibytes + H.F)).pre (initG hH.SH (H.ibytes + H.F)).pub H.init)
    (hs : ∃ s, (I.initAnyKeyContract RISCV64.abi (H.ibytes + H.F)).pre s) :
    Verified RISCV64.target H.init (I.initAnyKeyContract RISCV64.abi (H.ibytes + H.F)) := by
  obtain ⟨n, hn⟩ : ∃ n, H.ibytes + H.F = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by have := hH.lay.ibytes; simp only [Hash.ibytes] at this ⊢; omega)).symm⟩
  rw [hn] at ct hs ⊢
  have imp := initImp hs
  rw [← hSH] at imp
  exact Verified.of_implies (⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := Init.correct hH (by rw [hn]; exact hs); rw [hn] at h₂; exact ⟨t, s', he, h₁, h₂⟩, ct,
    imp.sat_left⟩ : Verified RISCV64.target H.init (initG hH.SH (n + 1))) imp

/-- `finalize` against the shared contract, given its constant time. -/
theorem finalize
    (ct : ConstantTime isa (finG hH.SH (H.fbytes + H.F)).pre (finG hH.SH (H.fbytes + H.F)).pub H.finalize)
    (hs : ∃ s, (I.finalizeContract RISCV64.abi (H.fbytes + H.F)).pre s) :
    Verified RISCV64.target H.finalize (I.finalizeContract RISCV64.abi (H.fbytes + H.F)) := by
  obtain ⟨n, hn⟩ : ∃ n, H.fbytes + H.F = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by have := hH.lay.fbytes; simp only [Hash.fbytes] at this ⊢; omega)).symm⟩
  rw [hn] at ct hs ⊢
  have imp := finImp hs
  rw [← hSH] at imp
  exact Verified.of_implies (⟨fun s hs => by obtain ⟨t, s', he, h₁, h₂⟩ := Finalize.correct hH (by rw [hn]; exact hs); rw [hn] at h₂; exact ⟨t, s', he, h₁, h₂⟩,
    ct, imp.sat_left⟩ : Verified RISCV64.target H.finalize (finG hH.SH (n + 1))) imp

/-- A state satisfying `init`'s precondition, with states of `S` bytes and a
one-byte key. -/
def initSat (S : Nat) : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a1 => 0x20000 | .a2 => 0x30000 | .a3 => 1
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes
and a digest of `D` bytes. -/
def finSat (S D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x10000 | .a1 => 0x20000 | .a3 => 0x30000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩]

end VG.Proof.Hmac.Stream.RISCV64.Shared
