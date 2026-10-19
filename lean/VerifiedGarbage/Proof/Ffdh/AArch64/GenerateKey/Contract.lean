module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_ffdh_generate_key` on AArch64: the contract the proofs use

`gkContract` states `Spec.Ffdh.generateKeyContract` on the registers and
the stack: `vg_ffdh_generate_key(x = x0, x_len = x1, y = x2, y_len = x3,
domain = x4, domain_len = x5, p_len = x6, rand = x7, rand_len = [sp],
scratch = [sp + 8], scratch_len = [sp + 16])`; the shared contract implies
it (`gk_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip i2osp powMod)

def gkPre (s : State) : Prop :=
  let xr : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let yr : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let dom : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let rnd : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  s.sp.toNat + 24 ≤ 2 ^ 64 ∧ s.rd = [dom, rnd, args] ∧ s.wr = [xr, yr, scr] ∧
    xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint args ∧
    yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint args ∧
    dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x6).toNat ∧ domainLenValid (s.gpr .x6).toNat (s.gpr .x5).toNat ∧
    (s.gpr .x1).toNat = (s.gpr .x6).toNat ∧ (s.gpr .x3).toNat = (s.gpr .x6).toNat ∧
    (stackArg s 0).toNat = (s.gpr .x6).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x6).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev gkDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat

/-- The random octets on entry. -/
abbrev gkRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

/-- The parameters. -/
abbrev gkA (s : State) : Parameters := domainOf (s.gpr .x6).toNat (gkDom s)

/-- The attempt's scalar. -/
abbrev gkS (s : State) : Nat := scalarOfOctets (gkA s) (gkRand s)

def gkPost (s s' : State) : Prop :=
  domainValid (s.gpr .x6).toNat (gkDom s) →
    ((s'.gpr .x0).setWidth 32).toNat = keyStatus (gkA s) (gkS s) ∧
      if keyStatus (gkA s) (gkS s) = 1 then
        bytesAt s'.mem (s.gpr .x0) (s.gpr .x6).toNat = i2osp (gkS s) (s.gpr .x6).toNat ∧
          bytesAt s'.mem (s.gpr .x2) (s.gpr .x6).toNat = i2osp (powMod (gkA s).g (gkS s) (gkA s).p) (s.gpr .x6).toNat
      else bytesAt s'.mem (s.gpr .x0) (s.gpr .x6).toNat = List.replicate (s.gpr .x6).toNat 0 ∧
        bytesAt s'.mem (s.gpr .x2) (s.gpr .x6).toNat = List.replicate (s.gpr .x6).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def gkLeak (s : State) : List Nat := (gkDom s).map (·.toNat) ++ [keyStatus (gkA s) (gkS s)]

def gkPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
    (List.range 3).map (stackArg s₁) = (List.range 3).map (stackArg s₂) ∧ gkLeak s₁ = gkLeak s₂

def gkContract : Contract isa where
  pre := gkPre
  post := gkPost
  pub := gkPub

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting the precondition: a 64-byte p, no q. -/
def gkSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1100 | .x3 => 64 | .x4 => 0x2000 | .x5 => 128 | .x6 => 64
    | .x7 => 0x3000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 64 else if a = 0x6009 then 0x80 else if a = 0x6010 then 0x20
    else if a = 0x6011 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 64⟩, ⟨0x6000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem gk_implies : gkContract.Implies (generateKeyContract abi) where
  pre := by
    intro s h
    sig_pre [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_three,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPost, stackArgs_three,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPub, stackArgs_three,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_three, stackArgs_three, a0, a1, a2], ?_⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · unfold gkLeak; exact hl
  sat := by
    sig_implies_sat [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_three,
      List.append_eq, pLenValid, domainLenValid] [gkSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSat

end VG.Proof.Ffdh.AArch64.GenerateKey
