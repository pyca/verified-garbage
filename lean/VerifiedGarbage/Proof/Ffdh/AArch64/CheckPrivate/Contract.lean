module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelList

/-!
# `vg_ffdh_check_private` on AArch64: the contract the proofs use

`kpContract` states `Spec.Ffdh.checkPrivateContract` on the registers and
the stack: `vg_ffdh_check_private(domain = x0, domain_len = x1, p_len = x2,
y = x3, y_len = x4, x = x5, x_len = x6, scratch = x7,
scratch_len = [sp])`; the shared contract implies it (`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def kpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let y : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let x : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, args] ∧ s.wr = [scr] ∧
    dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x2).toNat ∧ domainLenValid (s.gpr .x2).toNat (s.gpr .x1).toNat ∧
    (s.gpr .x4).toNat = (s.gpr .x2).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧ (s.gpr .x6).toNat ≤ (s.gpr .x2).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x2).toNat ≤ (stackArg s 0).toNat

/-- The domain on entry. -/
abbrev kpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat

/-- y on entry. -/
abbrev kpY (s : State) : List Byte := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat

/-- x on entry. -/
abbrev kpX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

def kpPost (s s' : State) : Prop :=
  domainValid (s.gpr .x2).toNat (kpDom s) →
    ((s'.gpr .x0).setWidth 32).toNat = privateStatus (domainOf (s.gpr .x2).toNat (kpDom s)) (os2ip (kpY s))
      (os2ip (kpX s))

/-- What timing may depend on, beyond the arguments. -/
def kpLeak (s : State) : List Nat :=
  (kpDom s).map (·.toNat) ++ (kpY s).map (·.toNat) ++
    [privateStatus (domainOf (s.gpr .x2).toNat (kpDom s)) (os2ip (kpY s)) (os2ip (kpX s))]

def kpPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 1).map (stackArg s₁) = (List.range 1).map (stackArg s₂) ∧ kpLeak s₁ = kpLeak s₂

def kpContract : Contract isa where
  pre := kpPre
  post := kpPost
  pub := kpPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def kpSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 64 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x8000, 1056 * 8⟩]

theorem kp_implies : kpContract.Implies (checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPost, stackArgs_one,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPub, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_one, stackArgs_one, a0], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold kpLeak; exact hl
  sat := by
    sig_implies_sat [checkPrivateContract, checkPrivateSig, abi, argRegs, kpContract, kpPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

end VG.Proof.Ffdh.AArch64.CheckPrivate
