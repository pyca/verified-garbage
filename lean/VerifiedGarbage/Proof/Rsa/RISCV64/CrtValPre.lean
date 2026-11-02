module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_crt_values` on RISC-V: the contract on the registers and the stack

`PreC s`: the shared contract's precondition (`crtValuesContract`), by name
(`preC_of`); `fnPost`: its postcondition on the registers and the stack,
which implies the shared contract's (`cv_implies`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.CrtValues

open VG VG.RISCV64

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-! ## The buffers -/

abbrev dpR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev dqR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev qiR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- What the code needs of `crtValuesContract.pre`, by name. -/
structure PreC (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  hrd : s.rd = [nR s, pR s, qR s, dR s, aR s]
  hwr : s.wr = [dpR s, dqR s, qiR s, sR s]
  dpdq : (dpR s).Disjoint (dqR s)
  dpqi : (dpR s).Disjoint (qiR s)
  dpn : (dpR s).Disjoint (nR s)
  dpp : (dpR s).Disjoint (pR s)
  dpq : (dpR s).Disjoint (qR s)
  dpd : (dpR s).Disjoint (dR s)
  dps : (dpR s).Disjoint (sR s)
  dpa : (dpR s).Disjoint (aR s)
  dqqi : (dqR s).Disjoint (qiR s)
  dqn : (dqR s).Disjoint (nR s)
  dqp : (dqR s).Disjoint (pR s)
  dqq : (dqR s).Disjoint (qR s)
  dqd : (dqR s).Disjoint (dR s)
  dqs : (dqR s).Disjoint (sR s)
  dqa : (dqR s).Disjoint (aR s)
  qin : (qiR s).Disjoint (nR s)
  qip : (qiR s).Disjoint (pR s)
  qiq : (qiR s).Disjoint (qR s)
  qid : (qiR s).Disjoint (dR s)
  qis : (qiR s).Disjoint (sR s)
  qia : (qiR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR s)
  wdp : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wdq : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wqi : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wn : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wd : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  ws : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a7).toNat
  k2 : (s.gpr .a7).toNat ≤ 1024
  p1 : 1 ≤ (stackArg s 1).toNat
  p2 : (stackArg s 1).toNat < (s.gpr .a7).toNat
  q1 : 1 ≤ (stackArg s 3).toNat
  q2 : (stackArg s 3).toNat < (s.gpr .a7).toNat
  h1 : (s.gpr .a1).toNat = (stackArg s 1).toNat
  h5 : (s.gpr .a5).toNat = (stackArg s 1).toNat
  h3 : (s.gpr .a3).toNat = (stackArg s 3).toNat
  d1 : 1 ≤ (stackArg s 5).toNat
  d2 : (stackArg s 5).toNat ≤ (s.gpr .a7).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a7).toNat ≤ (stackArg s 7).toNat
  al : (stackArg s 6).toNat % 8 = 0

theorem preC_of {s : State} (h : (Spec.Rsa.crtValuesContract RISCV64.abi).pre s) : PreC s := by
  sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp2, hrd, hwr, dpdq, dpqi, dpn, dpp, dpq, dpd, dps, dpa, dqqi, dqn, dqp, dqq, dqd, dqs, dqa,
    qin, qip, qiq, qid, qis, qia, ns, ps, qs, ds, sa, wdp, wdq, wqi, wn, wp, wq, wd, ws, ⟨k1, k2⟩, p1, p2,
    q1, q2, h1, h5, h3, d1, d2, hs, al⟩ := h
  exact ⟨sp16, sp2, hrd, hwr, dpdq, dpqi, dpn, dpp, dpq, dpd, dps, dpa, dqqi, dqn, dqp, dqq, dqd, dqs, dqa,
    qin, qip, qiq, qid, qis, qia, ns, ps, qs, ds, sa, wdp, wdq, wqi, wn, wp, wq, wd, ws, k1, k2, p1, p2,
    q1, q2, h1, h5, h3, d1, d2, hs, al⟩

/-! ## The postcondition -/

/-- The shared contract's postcondition, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenAll s'.mem [(s.gpr .a0, (stackArg s 1).toNat), (s.gpr .a2, (stackArg s 3).toNat),
      (s.gpr .a4, (stackArg s 1).toNat)] ((s'.gpr .a0).setWidth 32)
    ((Spec.Rsa.crtKey (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)).map fun v => [v.1, v.2.1, v.2.2])

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.Rsa.crtValuesContract RISCV64.abi).pre
  post := fnPost
  pub := (Spec.Rsa.crtValuesContract RISCV64.abi).pub

/-- A state meeting the precondition: a 64-byte modulus, one-byte factors and
exponent, and the stack arguments at `0x10000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x1100 | .a3 => 1 | .a4 => 0x1200 | .a5 => 1
    | .a6 => 0x2000 | .a7 => 64 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10001 then 0x30 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x31 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x32 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10032 then 0x02 else bif Nat.beq a.toNat 0x10038 then 0x20
    else bif Nat.beq a.toNat 0x10039 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x10000, 64⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x20000, 8448⟩]

theorem cv_implies : fnContract.Implies (Spec.Rsa.crtValuesContract RISCV64.abi) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost, stackArgs_eight, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, stackArgs_eight, List.append_eq] [satState, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using satState

end VG.Proof.Rsa.RISCV64.CrtValues
