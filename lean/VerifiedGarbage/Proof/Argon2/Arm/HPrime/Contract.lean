import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Argon2.Arm.HPrime

/-!
# Argon2 H′ on ARMv7: the contract of the proof

`hPrimeArm`: `vg_argon2_hprime(input = r0, input_len = r1, out = r2,
out_len = r3, scratch = [sp])` with its stack argument only read;
`Spec.Argon2.hPrimeContract`, which lets the code write it, is reached by
narrowing. H′ uses the 32 bytes of stack below the stack pointer: a call of
`vg_blake2b_update` pushes four words, and `update` itself uses 16 bytes.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm
open VG.Proof.Argon2.Arm (stkR)
open VG.Spec.Blake2 (bytesAt)

def hPrimeArm : Contract Arm.isa where
  pre s :=
    let input : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 16384⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    let stack : Region := stkR s.sp 32
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧
    input.Disjoint scratch ∧ out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 16384 ≤ 2 ^ 32 ∧ 32 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    1 ≤ (s.gpr .r3).toNat
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
    Spec.Argon2.hPrime (s.gpr .r3).toNat (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

section
variable (s₀ : State)

abbrev inp : BitVec 32 := s₀.gpr .r0
abbrev inl : Nat := (s₀.gpr .r1).toNat
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev ol : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev sp₀ : BitVec 32 := s₀.sp
/-- `scratch`, as an address. -/
abbrev P : Addr := State.addr (scr s₀)
abbrev inR : Region := ⟨State.addr (inp s₀), inl s₀⟩
abbrev outR : Region := ⟨State.addr (op s₀), ol s₀⟩
abbrev scrR : Region := ⟨P s₀, 16384⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stk : Region := stkR (sp₀ s₀) 32

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  in_scr : (inR s₀).Disjoint (scrR s₀)
  out_scr : (outR s₀).Disjoint (scrR s₀)
  arg_out : (argR s₀).Disjoint (outR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  stk_in : (stk s₀).Disjoint (inR s₀)
  stk_out : (stk s₀).Disjoint (outR s₀)
  stk_scr : (stk s₀).Disjoint (scrR s₀)
  in_fits : (inp s₀).toNat + inl s₀ ≤ 2 ^ 32
  out_fits : (op s₀).toNat + ol s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 16384 ≤ 2 ^ 32
  sp_lo : 32 ≤ (sp₀ s₀).toNat
  sp_hi : (sp₀ s₀).toNat + 4 ≤ 2 ^ 32
  ol_pos : 1 ≤ ol s₀

theorem pre_of (s₀ : State) (h : hPrimeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- `[scratch + d]`, as the code addresses it. -/
theorem scr_addr {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 16384) :
    State.addr (scr s₀ + BitVec.ofNat 32 d) = P s₀ + BitVec.ofNat 64 d := addr_add (by have := hp.scr_fits; omega)

end VG.Proof.Argon2.Arm.HPrime
