module

public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ffdh_derive_public` on AArch64: the contract the proofs use

`dvContract` states `Spec.Ffdh.derivePublicContract` on the registers and
the stack: `vg_ffdh_derive_public(y = x0, y_len = x1, domain = x2,
domain_len = x3, p_len = x4, x = x5, x_len = x6, scratch = x7,
scratch_len = [sp])`; the shared contract implies it (`dv_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip i2osp powMod)

def dvPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let dom : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let xr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 64 ∧ s.rd = [dom, xr, args] ∧ s.wr = [out, scr] ∧
    out.Disjoint dom ∧ out.Disjoint xr ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    dom.Disjoint scr ∧ xr.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x4).toNat ∧ domainLenValid (s.gpr .x4).toNat (s.gpr .x3).toNat ∧
    (s.gpr .x1).toNat = (s.gpr .x4).toNat ∧ 1 ≤ (s.gpr .x6).toNat ∧ (s.gpr .x6).toNat ≤ (s.gpr .x4).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 0).toNat

/-- The domain on entry. -/
abbrev dvDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat

/-- x on entry. -/
abbrev dvX (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

/-- The parameters. -/
abbrev dvA (s : State) : Parameters := domainOf (s.gpr .x4).toNat (dvDom s)

def dvPost (s s' : State) : Prop :=
  domainValid (s.gpr .x4).toNat (dvDom s) →
    ((s'.gpr .x0).setWidth 32).toNat = keyStatus (dvA s) (os2ip (dvX s)) ∧
      if keyStatus (dvA s) (os2ip (dvX s)) = 1 then
        bytesAt s'.mem (s.gpr .x0) (s.gpr .x4).toNat =
          i2osp (powMod (dvA s).g (os2ip (dvX s)) (dvA s).p) (s.gpr .x4).toNat
      else bytesAt s'.mem (s.gpr .x0) (s.gpr .x4).toNat = List.replicate (s.gpr .x4).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def dvLeak (s : State) : List Nat := (dvDom s).map (·.toNat) ++ [keyStatus (dvA s) (os2ip (dvX s))]

def dvPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 1).map (stackArg s₁) = (List.range 1).map (stackArg s₂) ∧ dvLeak s₁ = dvLeak s₂

def dvContract : Contract isa where
  pre := dvPre
  post := dvPost
  pub := dvPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def dvSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 128 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem dv_implies : dvContract.Implies (derivePublicContract abi) where
  pre := by
    intro s h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPost, stackArgs_one,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPub, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_one, stackArgs_one, a0], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold dvLeak; exact hl
  sat := by
    sig_implies_sat [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] [dvSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using dvSat

end VG.Proof.Ffdh.AArch64.Derive
