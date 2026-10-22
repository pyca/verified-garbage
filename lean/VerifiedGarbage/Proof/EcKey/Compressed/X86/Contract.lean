module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Point conversion's cdecl contract and readable argument view -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86

def codecPre (inputLen outputLen : Nat) (wide : Bool) (s : State) : Prop :=
  let out : Region := ⟨(arg s 0).setWidth 64, outputLen⟩
  let pk : Region := ⟨(arg s 1).setWidth 64, inputLen⟩
  let ws : Region := ⟨(arg s 2).setWidth 64, 8192⟩
  let args : Region := ⟨argAddr s 0, 12⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
  s.rd = (if wide then [pk] else [pk, args]) ∧ s.wr = (if wide then [out, ws, args] else [out, ws]) ∧
    out.Disjoint ws ∧ out.Disjoint pk ∧ pk.Disjoint ws ∧
    args.Disjoint out ∧ args.Disjoint ws ∧ ret.Disjoint out ∧ ret.Disjoint ws ∧
    (arg s 0).toNat + outputLen ≤ 2 ^ 32 ∧ (arg s 1).toNat + inputLen ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧
    28 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint ws

def compressContract (C : Spec.Weierstrass.Curve) (wide : Bool := false) : Contract isa where
  pre := codecPre (2 * C.len + 1) (C.len + 1) wide
  post s t := match Spec.EcKey.compressPublicKey C
      (Spec.EcKey.bytesAt s.mem ((arg s 1).setWidth 64) (2 * C.len + 1)) with
    | some bs => (t.gpr .edx ++ t.gpr .eax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt t.mem ((arg s 0).setWidth 64) (C.len + 1) = bs
    | none => (t.gpr .edx ++ t.gpr .eax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt t.mem ((arg s 0).setWidth 64) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

def codecRd (inputLen : Nat) (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, inputLen⟩, ⟨argAddr s 0, 12⟩]

def codecWr (outputLen : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, outputLen⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem codecWide_pre {inputLen outputLen : Nat} {s : State} (h : codecPre inputLen outputLen true s) :
    codecPre inputLen outputLen false (s.withRegions (codecRd inputLen s) (codecWr outputLen s)) := by
  simp only [codecPre, codecRd, codecWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨rfl, rfl, h.2.2⟩

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 28).pre s) :
    (compressContract I.curve true).Implies (I.compressPublicKeyContract abi 28) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract, Spec.EcKey.Instance.compressPublicKeySig,
      Spec.EcKey.scratchWords, abi, argSlots, argVal, argBytes, stackBelow, compressContract, codecPre]
  post := by
    intro s t _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract, Spec.EcKey.Instance.compressPublicKeySig,
      Spec.EcKey.scratchWords, abi, argSlots, argVal, argBytes, stackBelow, compressContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract, Spec.EcKey.Instance.compressPublicKeySig,
      Spec.EcKey.scratchWords, abi, argSlots, argVal, argBytes, stackBelow, compressContract]
  sat := hsat

def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x80 else 0

def satState (inputLen outputLen : Nat) : State where
  gpr r := match r with | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, inputLen⟩]
  wr := [⟨0x1000, outputLen⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 12⟩]

end VG.Proof.EcKey.Compressed.X86
