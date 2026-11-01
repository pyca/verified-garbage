module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Resources supplied by the shared CRT-values cdecl contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

def caller (s : State) : CallGeometry :=
  ⟨argumentPointer s 14, (arg s 15).toNat * 8, Spec.Rsa.modulusWords (arg s 7).toNat, arg s⟩

structure ABI (s : State) : Prop where
  stackLow : 52 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 68 ≤ 2 ^ 32
  rd : s.rd = [(caller s).buffer 6, (caller s).buffer 8, (caller s).buffer 10, (caller s).buffer 12]
  wr : s.wr = [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4,
    ⟨(caller s).base, (caller s).size⟩, ⟨argAddr s 0, 64⟩]
  scratchBound : (arg s 14).toNat + (caller s).size ≤ 2 ^ 32
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 52#64, 52⟩ : Region).Disjoint
    ⟨(caller s).base, (caller s).size⟩
  argsApart : ∀ r ∈ (caller s).writes, (⟨argAddr s 0, 64⟩ : Region).Disjoint r
  retApart : ∀ r ∈ (caller s).writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  inApart : ∀ r ∈ s.rd, ∀ w ∈ (caller s).writes, r.Disjoint w
  outScratch : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4],
    r.Disjoint ⟨(caller s).base, (caller s).size⟩
  outSeparate : ((caller s).buffer 0).Disjoint ((caller s).buffer 2) ∧
    ((caller s).buffer 0).Disjoint ((caller s).buffer 4) ∧
    ((caller s).buffer 2).Disjoint ((caller s).buffer 4)
  bounds : ∀ i ∈ [0, 2, 4, 6, 8, 10, 12], (arg s i).toNat + (arg s (i + 1)).toNat ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 7).toNat
  pPositive : 1 ≤ (arg s 9).toNat
  pSmall : (arg s 9).toNat < (arg s 7).toNat
  qPositive : 1 ≤ (arg s 11).toNat
  qSmall : (arg s 11).toNat < (arg s 7).toNat
  dpLen : (arg s 1).toNat = (arg s 9).toNat
  qiLen : (arg s 5).toNat = (arg s 9).toNat
  dqLen : (arg s 3).toNat = (arg s 11).toNat
  dPositive : 1 ≤ (arg s 13).toNat
  dBound : (arg s 13).toNat ≤ (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 7).toNat ≤ (arg s 15).toNat

theorem abi_of {s : State} (h : (Spec.Rsa.crtValuesContract abi 52).pre s) : ABI s := by
  sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 6, (caller s).buffer 8, (caller s).buffer 10, (caller s).buffer 12] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 7).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  constructor
  all_goals try simp only [rd, CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.Rsa.X86.CrtValues
