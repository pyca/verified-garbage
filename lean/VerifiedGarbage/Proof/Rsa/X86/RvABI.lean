module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset

/-! # Resources supplied by the shared prime-recovery cdecl contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

def caller (s : State) : CallGeometry :=
  ⟨⟨argumentPointer s 10, (arg s 11).toNat * 8, Spec.Rsa.modulusWords (arg s 5).toNat, s.gpr .esp, arg s, s.wr⟩⟩

/-- What the call writes but the stack below `esp`: the working space and the outputs. -/
abbrev bodyRegions (s : State) : List Region :=
  [⟨(caller s).B, (caller s).Z⟩, (caller s).buffer 0, (caller s).buffer 2]

/-- The 40 bytes below `esp` the calls' frames use, as the contract states them. -/
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩

structure ABI (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 52 ≤ 2 ^ 32
  rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8]
  wr : s.wr = [(caller s).buffer 0, (caller s).buffer 2,
    ⟨(caller s).B, (caller s).Z⟩, ⟨argAddr s 0, 48⟩]
  scratchBound : (arg s 10).toNat + (caller s).Z ≤ 2 ^ 32
  belowScratch : (lowR s).Disjoint ⟨(caller s).B, (caller s).Z⟩
  belowIn : ∀ r ∈ s.rd, r.Disjoint (lowR s)
  belowOut : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2], r.Disjoint (lowR s)
  argsApart : ∀ r ∈ bodyRegions s, (⟨argAddr s 0, 48⟩ : Region).Disjoint r
  retApart : ∀ r ∈ bodyRegions s, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  inApart : ∀ r ∈ s.rd, ∀ w ∈ bodyRegions s, r.Disjoint w
  outScratch : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2],
    r.Disjoint ⟨(caller s).B, (caller s).Z⟩
  outSeparate : ((caller s).buffer 0).Disjoint ((caller s).buffer 2)
  bounds : ∀ i ∈ [0, 2, 4, 6, 8], (arg s i).toNat + (arg s (i + 1)).toNat ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 5).toNat
  pLen : (arg s 1).toNat = (arg s 5).toNat
  qLen : (arg s 3).toNat = (arg s 5).toNat
  ePositive : 1 ≤ (arg s 7).toNat
  eBound : (arg s 7).toNat ≤ (arg s 5).toNat
  dPositive : 1 ≤ (arg s 9).toNat
  dBound : (arg s 9).toNat ≤ (arg s 5).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 5).toNat ≤ (arg s 11).toNat

theorem abi_of {s : State} (h : (Spec.Rsa.recoverPrimesContract abi 96).pre s) : ABI s := by
  sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 5).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  constructor
  all_goals try simp only [rd, bodyRegions, lowR, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

/-- The stack below `esp`, in the contract's form. -/
theorem below_eq {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    below sp 96 = ⟨sp.setWidth 64 - 96#64, 96⟩ := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]

theorem ABI.room {s : State} (a : ABI s) : CallRoom (s.gpr .esp) (caller s).B (caller s).Z :=
  ⟨a.stackLow, by rw [below_eq a.stackLow]; exact a.belowScratch⟩

theorem ABI.argsApartW {s : State} (a : ABI s) :
    ∀ r ∈ (caller s).writes, (⟨argAddr s 0, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.argsApart _ (by simp)
  · exact a.argsApart _ (by simp)
  · exact a.argsApart _ (by simp)
  · have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      addr_eq (by have := a.stackBound; omega)
    rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow, z]
    exact Offset.disjoint_below _ (by decide)

theorem ABI.retApartW {s : State} (a : ABI s) :
    ∀ r ∈ (caller s).writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.retApart _ (by simp)
  · exact a.retApart _ (by simp)
  · exact a.retApart _ (by simp)
  · rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow]
    exact Offset.base_disjoint_below _ (by decide)

theorem ABI.inApartW {s : State} (a : ABI s) : ∀ r ∈ s.rd, ∀ w ∈ (caller s).writes, r.Disjoint w := by
  intro r hr w hw
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact a.inApart _ hr _ (by simp)
  · exact a.inApart _ hr _ (by simp)
  · exact a.inApart _ hr _ (by simp)
  · rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow]
    exact a.belowIn _ hr

end VG.Proof.Rsa.X86.Recover
