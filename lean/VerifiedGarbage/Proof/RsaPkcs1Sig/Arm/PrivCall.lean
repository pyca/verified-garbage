module
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl

import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.PublicStack

/-!
# The ARMv7 PKCS #1 v1.5 functions: their callee `vg_rsa_private_checked`

`vg_rsa_private_checked` calling an implementation `v` of
`vg_rsa_private_crt` (`privCode v`) uses at most 3440 bytes of stack
(`privCode_stack`). Its contract, at a call with given arguments
(`priv_pre`, `priv_pub`, `priv_post`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm

theorem privCode_stack (v : Proof.Rsa.Arm.CrtImpl) :
    FrameStack.armStack (Proof.Rsa.Arm.privCode v) ≤ Proof.Rsa.Arm.stackBytes := by
  have := v.stack
  have := v.pcStack
  have := v.pdStack
  simp only [Proof.Rsa.Arm.privCode, Impl.Rsa.Arm.PrivChecked.code, Impl.Rsa.Arm.PrivChecked.body,
    Impl.Rsa.Arm.PrivChecked.check, Impl.Rsa.Arm.PrivChecked.tail, Impl.Rsa.Arm.PrivChecked.releaseTail,
    Impl.Rsa.Arm.PrivChecked.release, Impl.Bignum.Arm.compareBytes, FrameStack.armStack, List.length_cons,
    List.length_nil, Impl.Rsa.Arm.PrivChecked.frameBytes, Proof.Rsa.Arm.stackBytes]
  omega_arith

section

variable {s : State} {out n e inp p q dp dq qinv scr : BitVec 32} {K el pl ql sl : Nat}

/-- The call's arguments. -/
structure PrivArgs (s : State) (out n e inp p q dp dq qinv scr : BitVec 32) (K el pl ql sl : Nat) : Prop where
  r0 : s.gpr .r0 = out
  r1 : s.gpr .r1 = BitVec.ofNat 32 K
  r2 : s.gpr .r2 = n
  r3 : s.gpr .r3 = BitVec.ofNat 32 K
  a0 : stackArg s 0 = e
  a1 : stackArg s 1 = BitVec.ofNat 32 el
  a2 : stackArg s 2 = inp
  a3 : stackArg s 3 = BitVec.ofNat 32 K
  a4 : stackArg s 4 = p
  a5 : stackArg s 5 = BitVec.ofNat 32 pl
  a6 : stackArg s 6 = q
  a7 : stackArg s 7 = BitVec.ofNat 32 ql
  a8 : stackArg s 8 = dp
  a9 : stackArg s 9 = BitVec.ofNat 32 pl
  a10 : stackArg s 10 = dq
  a11 : stackArg s 11 = BitVec.ofNat 32 ql
  a12 : stackArg s 12 = qinv
  a13 : stackArg s 13 = BitVec.ofNat 32 pl
  a14 : stackArg s 14 = scr
  a15 : stackArg s 15 = BitVec.ofNat 32 sl
  kv : Spec.Rsa.lenValid K
  el1 : 1 ≤ el
  elK : el ≤ K
  pl1 : 1 ≤ pl
  plK : pl < K
  ql1 : 1 ≤ ql
  qlK : ql < K
  slK : Spec.Rsa.scratchWords K ≤ sl
  sl32 : sl < 2 ^ 32

/-- The callee's buffers. -/
abbrev privRd (sp n e inp p q dp dq qinv : BitVec 32) (K el pl ql : Nat) : List Region :=
  [⟨State.addr n, K⟩, ⟨State.addr e, el⟩, ⟨State.addr inp, K⟩, ⟨State.addr p, pl⟩, ⟨State.addr q, ql⟩,
    ⟨State.addr dp, pl⟩, ⟨State.addr dq, ql⟩, ⟨State.addr qinv, pl⟩, ⟨State.addr sp, 64⟩]
abbrev privWr (out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨State.addr out, K⟩, ⟨State.addr scr, sl * 8⟩]

/-- The callee's buffers but its stack arguments. -/
abbrev privBufs (out n e inp p q dp dq qinv scr : BitVec 32) (K el pl ql sl : Nat) : List Region :=
  [⟨State.addr out, K⟩, ⟨State.addr n, K⟩, ⟨State.addr e, el⟩, ⟨State.addr inp, K⟩, ⟨State.addr p, pl⟩,
    ⟨State.addr q, ql⟩, ⟨State.addr dp, pl⟩, ⟨State.addr dq, ql⟩, ⟨State.addr qinv, pl⟩,
    ⟨State.addr scr, sl * 8⟩]

theorem PrivArgs.k32 (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl) : K < 2 ^ 32 := by
  have := h.kv.2; omega_arith

theorem priv_pre {sp : BitVec 32} (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl) (hspE : s.sp = sp)
    (hsp : 3440 ≤ sp.toNat) (hsa : sp.toNat + 64 ≤ 2 ^ 32)
    (dW : ∀ w ∈ privWr out scr K sl, ∀ r ∈ privRd sp n e inp p q dp dq qinv K el pl ql, w.Disjoint r)
    (dWW : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr scr, sl * 8⟩)
    (dLow : ∀ r ∈ privWr out scr K sl ++ privRd sp n e inp p q dp dq qinv K el pl ql,
      Region.Disjoint ⟨State.addr sp - BitVec.ofNat 64 3440, 3440⟩ r)
    (fit : ∀ r ∈ privBufs out n e inp p q dp dq qinv scr K el pl ql sl, r.base.toNat + r.len ≤ 2 ^ 32) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pre
      (s.callEntry.withRegions (privRd sp n e inp p q dp dq qinv K el pl ql) (privWr out scr K sl)) := by
  subst hspE
  have k32 := h.k32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega_arith
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega_arith
  have ql32 : ql < 2 ^ 32 := by have := h.qlK; omega_arith
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, h.a3, h.a4, h.a5,
    h.a6, h.a7, h.a8, h.a9, h.a10, h.a11, h.a12, h.a13, h.a14, h.a15, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32, Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt ql32,
    Nat.mod_eq_of_lt h.sl32]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  have wo := fun {r : Region} (hr : r ∈ privRd s.sp n e inp p q dp dq qinv K el pl ql) =>
    dW _ (List.mem_cons_self ..) r hr
  have ws := fun {r : Region} (hr : r ∈ privRd s.sp n e inp p q dp dq qinv K el pl ql) =>
    (dW _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) r hr).symm
  have lo := fun {r : Region} (hr : r ∈ privWr out scr K sl ++ privRd s.sp n e inp p q dp dq qinv K el pl ql) =>
    dLow r hr
  have fi := fun {r : Region} (hr : r ∈ privBufs out n e inp p q dp dq qinv scr K el pl ql sl) => fit r hr
  simp only [privBufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Proof.X25519.Arm.addr_toNat] at fit
  obtain ⟨fO, fN, fE, fI, fP, fQ, fDP, fDQ, fQI, fS⟩ := fit
  exact ⟨hsp, hsa, rfl, rfl, wo (by simp [State.addr]), wo (by simp [State.addr]), wo (by simp [State.addr]), wo (by simp [State.addr]), wo (by simp [State.addr]), wo (by simp [State.addr]),
    wo (by simp [State.addr]), wo (by simp [State.addr]), dWW, wo (by simp [State.addr]), ws (by simp [State.addr]), ws (by simp [State.addr]), ws (by simp [State.addr]), ws (by simp [State.addr]),
    ws (by simp [State.addr]), ws (by simp [State.addr]), ws (by simp [State.addr]), ws (by simp [State.addr]), (ws (by simp [State.addr])).symm, lo (by simp [State.addr]), lo (by simp [State.addr]),
    lo (by simp [State.addr]), lo (by simp [State.addr]), lo (by simp [State.addr]), lo (by simp [State.addr]), lo (by simp [State.addr]), lo (by simp [State.addr]), lo (by simp [State.addr]),
    lo (by simp [State.addr]), lo (by simp [State.addr]), fO, fN, fE, fI, fP, fQ, fDP, fDQ, fQI, fS, h.kv, trivial, trivial, h.el1, h.elK,
    h.pl1, h.plK, h.ql1, h.qlK, trivial, trivial, trivial, h.slK⟩
theorem priv_pub {s₁ s₂ : State} (h₁ : PrivArgs s₁ out n e inp p q dp dq qinv scr K el pl ql sl)
    (h₂ : PrivArgs s₂ out n e inp p q dp dq qinv scr K el pl ql sl) (hsp : s₁.sp = s₂.sp)
    (hn : Spec.Rsa.bytesAt s₁.mem (State.addr n) K = Spec.Rsa.bytesAt s₂.mem (State.addr n) K)
    (he : Spec.Rsa.bytesAt s₁.mem (State.addr e) el = Spec.Rsa.bytesAt s₂.mem (State.addr e) el)
    (rd wr : List Region) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  have k32 := h₁.k32
  have el32 : el < 2 ^ 32 := by have := h₁.elK; omega_arith
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₁.a6, h₁.a7,
    h₁.a8, h₁.a9, h₁.a10, h₁.a11, h₁.a12, h₁.a13, h₁.a14, h₁.a15,
    h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, h₂.a6, h₂.a7,
    h₂.a8, h₂.a9, h₂.a10, h₂.a11, h₂.a12, h₂.a13, h₂.a14, h₂.a15,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32]
  have hn' : Spec.Rsa.bytesAt s₁.mem (n.setWidth 64) K = Spec.Rsa.bytesAt s₂.mem (n.setWidth 64) K := hn
  have he' : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el := he
  rw [hn', he']
  exact ⟨hsp, rfl, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The call's result: what it writes to `out` and returns. -/
theorem priv_post {s t : State} (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl)
    {rd wr : List Region}
    (hp : (Spec.Rsa.privateCheckedContract abi Proof.Rsa.Arm.stackBytes).post (s.callEntry.withRegions rd wr)
      (t.withRegions rd wr)) :
    Spec.Rsa.writtenOutcome t.mem (State.addr out) K (t.gpr .r0)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (State.addr n) K)
        (Spec.Rsa.bytesAt s.mem (State.addr e) el) (Spec.Rsa.bytesAt s.mem (State.addr inp) K)
        (Spec.Rsa.bytesAt s.mem (State.addr p) pl) (Spec.Rsa.bytesAt s.mem (State.addr q) ql)
        (Spec.Rsa.bytesAt s.mem (State.addr dp) pl) (Spec.Rsa.bytesAt s.mem (State.addr dq) ql)
        (Spec.Rsa.bytesAt s.mem (State.addr qinv) pl)) := by
  have k32 := h.k32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega_arith
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega_arith
  have ql32 : ql < 2 ^ 32 := by have := h.qlK; omega_arith
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r2, h.r3, h.a0, h.a1, h.a2, h.a4, h.a5, h.a6, h.a7, h.a8,
    h.a10, h.a12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt el32,
    Nat.mod_eq_of_lt pl32, Nat.mod_eq_of_lt ql32] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Sig.Arm
