module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ffdh_exchange` on AArch64: the contract the proofs use

`exContract` states `Spec.Ffdh.exchangeContract` on the registers and the
stack: `vg_ffdh_exchange(out = x0, out_len = x1, domain = x2,
domain_len = x3, p_len = x4, x = x5, x_len = x6, peer = x7,
peer_len = [sp], scratch = [sp + 8], scratch_len = [sp + 16])`; the shared
contract implies it (`ex_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip written)

def exPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let dom : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let xr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let peer : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  s.sp.toNat + 24 ≤ 2 ^ 64 ∧ s.rd = [dom, xr, peer, args] ∧ s.wr = [out, scr] ∧
    out.Disjoint dom ∧ out.Disjoint xr ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    dom.Disjoint scr ∧ xr.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
    (s.gpr .x1).toNat = (s.gpr .x4).toNat ∧ (stackArg s 0).toNat = (s.gpr .x4).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧
    (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev exDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

/-- The peer's value on entry. -/
abbrev exY (s : State) : List Byte := bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

/-- The scalar on entry. -/
abbrev exX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

def exPost (s s' : State) : Prop :=
  domainValid (s.gpr .x4).toNat (exDom s) → publicValid ⟨domainOf (s.gpr .x4).toNat (exDom s), os2ip (exY s)⟩ →
    written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
      (exchangeOp (domainOf (s.gpr .x4).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s)))

/-- What timing may depend on, beyond the arguments. -/
def exLeak (s : State) : List Nat :=
  (exDom s).map (·.toNat) ++ (exY s).map (·.toNat) ++
    [if (exchangeOp (domainOf (s.gpr .x4).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s))).isSome then 1 else 0]

def exPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 3).map (stackArg s₁) = (List.range 3).map (stackArg s₂) ∧ exLeak s₁ = exLeak s₂

def exContract : Contract isa where
  pre := exPre
  post := exPost
  pub := exPub

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def exSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 128 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x3100 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 64 else if a = 0x6009 then 0x80 else if a = 0x6010 then 0x20
    else if a = 0x6011 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x6000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem ex_implies : exContract.Implies (exchangeContract abi) where
  pre := by
    intro s h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [exchangeContract, exchangeSig, abi, argRegs, exContract, exPost, stackArgs_three,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [exchangeContract, exchangeSig, abi, argRegs, exContract, exPub, stackArgs_three, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_three, stackArgs_three, a0, a1, a2], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold exLeak; exact hl
  sat := by
    sig_implies_sat [exchangeContract, exchangeSig, abi, argRegs, exContract, exPre, stackArgs_three,
      List.append_eq, pLenValid, domainLenValid] [exSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using exSat

end VG.Proof.Ffdh.AArch64.Exchange
