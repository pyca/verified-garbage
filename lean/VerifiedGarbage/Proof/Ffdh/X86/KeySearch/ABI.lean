module

public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig

/-! # The key search on i686: what its cdecl contract supplies

`vg_ffdh_generate_key_search(x, x_len, y, y_len, used, domain, domain_len, p_len, rand, rand_len,
scratch, scratch_len, state)`: thirteen arguments on the stack. The controller uses 220 bytes of
stack: its attempt's frame of 44, the call's return address and the callee's own 172.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86.KeySearch
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the controller uses. -/
abbrev stack : Nat := 220

/-- The arguments' regions: `x`, `y`, `used`, `domain`, `rand`, `scratch` and `state`. -/
abbrev xR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev yR (s : State) : Region := ⟨argumentPointer s 2, (arg s 3).toNat⟩
abbrev uR (s : State) : Region := ⟨argumentPointer s 4, 8⟩
abbrev dR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev rR (s : State) : Region := ⟨argumentPointer s 8, (arg s 9).toNat⟩
abbrev bR (s : State) : Region := ⟨argumentPointer s 10, (arg s 11).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨argumentPointer s 12, 128⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 52⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 220#64, 220⟩

structure KeySearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 52 ≤ 2 ^ 32
  rd : s.rd = [dR s, rR s]
  wr : s.wr = [xR s, yR s, uR s, bR s, sR s, aR s]
  xy : (xR s).Disjoint (yR s)
  xu : (xR s).Disjoint (uR s)
  xd : (xR s).Disjoint (dR s)
  xr : (xR s).Disjoint (rR s)
  xb : (xR s).Disjoint (bR s)
  xs : (xR s).Disjoint (sR s)
  xa : (xR s).Disjoint (aR s)
  yu : (yR s).Disjoint (uR s)
  yd : (yR s).Disjoint (dR s)
  yr : (yR s).Disjoint (rR s)
  yb : (yR s).Disjoint (bR s)
  ys : (yR s).Disjoint (sR s)
  ya : (yR s).Disjoint (aR s)
  ud : (uR s).Disjoint (dR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  ua : (uR s).Disjoint (aR s)
  db : (dR s).Disjoint (bR s)
  ds : (dR s).Disjoint (sR s)
  da : (dR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  ba : (bR s).Disjoint (aR s)
  sa : (sR s).Disjoint (aR s)
  retX : (retR s).Disjoint (xR s)
  retY : (retR s).Disjoint (yR s)
  retU : (retR s).Disjoint (uR s)
  retD : (retR s).Disjoint (dR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retA : (retR s).Disjoint (aR s)
  lowX : (lowR s).Disjoint (xR s)
  lowY : (lowR s).Disjoint (yR s)
  lowU : (lowR s).Disjoint (uR s)
  lowD : (lowR s).Disjoint (dR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowA : (lowR s).Disjoint (aR s)
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  uBound : (arg s 4).toNat + 8 ≤ 2 ^ 32
  dBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  rBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  bBound : (arg s 10).toNat + (arg s 11).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 12).toNat + 128 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 7).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 7).toNat (arg s 6).toNat
  xLen : (arg s 1).toNat = (arg s 7).toNat
  yLen : (arg s 3).toNat = (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 7).toNat ≤ (arg s 11).toNat
  domValid : Spec.Ffdh.domainValid (arg s 7).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
  keys : (s.mem.readW (argumentPointer s 12) 64).toNat ≤ 128
  scalars : (s.mem.readW (argumentPointer s 12 + 8) 64).toNat ≤ 128
  width : s.mem.readW (argumentPointer s 12 + 16) 64 = BitVec.ofNat 64 (arg s 7).toNat

theorem keySearchABI_of {s : State} (h : (Spec.Ffdh.keySearchContract abi stack).pre s) : KeySearchABI s := by
  sig_pre [Spec.Ffdh.keySearchContract, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86.KeySearch
