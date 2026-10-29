module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# Blowfish on x86 (32-bit): the contracts the proofs use

`Proof.Blowfish.ecbScratchContract` and
`Proof.Blowfish.expandKeyScratch8Contract` spelled out for x86: `ecbC`,
with the arguments only read (the taint analysis follows them in memory only
while nothing that may alias them is written), and `keyC`. `wideEcb` lets
the code write the arguments, as the shared contract does, and implies it;
`Verified.lean` narrows it back.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86
open VG VG.X86 VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

def ecbC (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨(arg s 0).setWidth 64, 4168⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sch, args] ∧ s.wr = [data, scratch] ∧ sch.Disjoint data ∧ sch.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + (arg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 256 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      ecb (scheduleAt s.mem ((arg s 0).setWidth 64)) (dir up)
        (blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecbC`, with the arguments writable. -/
def wideEcb (up : Bool) : Contract isa :=
  { ecbC up with
    pre := fun s =>
      let sch : Region := ⟨(arg s 0).setWidth 64, 4168⟩
      let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 256⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sch] ∧ s.wr = [data, scratch, args] ∧ sch.Disjoint data ∧ sch.Disjoint scratch ∧
        data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧
        ret.Disjoint scratch ∧ (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
        (arg s 1).toNat + (arg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 256 ≤ 2 ^ 32 ∧
        (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ args.Disjoint sch }

def keyC : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sch : Region := ⟨(arg s 2).setWidth 64, 4168⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sch, scratch] ∧ key.Disjoint sch ∧ key.Disjoint scratch ∧
      sch.Disjoint scratch ∧ args.Disjoint sch ∧ args.Disjoint scratch ∧ ret.Disjoint sch ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 4168 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ validKey (arg s 1).toNat
  post s s' :=
    scheduleAt s'.mem ((arg s 2).setWidth 64) =
      expandKey (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecb(0x1000, 0x2000, 0, 0x3000)`. -/
def ecbSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6009 then 0x20 else if a = 0x6011 then 0x30 else 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩, ⟨0x6004, 16⟩]

/-- `expand_key(0x1000, 4, 0x2000, 0x4000)`. -/
def keySat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 4 else if a = 0x600d then 0x20 else
    if a = 0x6011 then 0x40 else 0
  rd := [⟨0x1000, 4⟩, ⟨0x6004, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 64⟩]

tactic_template "bf_pre" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega))

theorem ecb_implies (up : Bool) : (wideEcb up).Implies (ecbScratchContract abi (dir up)) where
  pre := by
    bf_pre [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes, wideEcb, ecbC]
  post := by
    sig_implies_post [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes,
      wideEcb, ecbC]
  pub := by
    sig_implies_pub [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes,
      wideEcb, ecbC]
  sat := by
    refine ⟨ecbSat, ?_⟩
    have h0 : (arg ecbSat 2).toNat = 0 := by decide
    sig_pre [ecbScratchContract, ecbScratchSig, ecbPost, abi, argSlots, argVal, argBytes, wideEcb, ecbC]
    sig_and_intros
    -- The data is empty.
    all_goals first
      | rfl
      | decide
      | (intro a _ h₂; simp only [Region.Contains, h0] at h₂; omega)
      | exact Region.disjoint_of_sep (by decide)

theorem key_implies : keyC.Implies (expandKeyScratch8Contract abi) where
  pre := by
    bf_pre [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  post := by
    sig_implies_post [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  pub := by
    sig_implies_pub [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
  sat := by
    sig_implies_sat [expandKeyScratch8Contract, expandKeyScratch8Sig, expandKeyPre, expandKeyPost, abi, argSlots,
      argVal, argBytes, keyC, validKey]
      [keySat, arg, argAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.Blowfish.X86
