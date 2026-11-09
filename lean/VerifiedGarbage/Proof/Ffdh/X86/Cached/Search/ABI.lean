module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig

/-! # The key search from the context on i686: what its cdecl contract supplies

`vg_ffdh_generate_key_search_cached(x, x_len, y, y_len, used, domain, domain_len, p_len, rand,
rand_len, scratch, scratch_len, state, ctx, ctx_len)`: fifteen arguments on the stack. The
controller uses 228 bytes of stack: its attempt's frame of 52, the call's return address and the
callee's own 172.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86.Cached.Search
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the controller uses. -/
abbrev stack : Nat := 228

/-- The arguments' regions: `x`, `y`, `used`, `domain`, `rand`, `scratch` and `state`. -/
abbrev xR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev yR (s : State) : Region := ⟨argumentPointer s 2, (arg s 3).toNat⟩
abbrev uR (s : State) : Region := ⟨argumentPointer s 4, 8⟩
abbrev dR (s : State) : Region := ⟨argumentPointer s 5, (arg s 6).toNat⟩
abbrev rR (s : State) : Region := ⟨argumentPointer s 8, (arg s 9).toNat⟩
abbrev bR (s : State) : Region := ⟨argumentPointer s 10, (arg s 11).toNat * 8⟩
abbrev sR (s : State) : Region := ⟨argumentPointer s 12, 128⟩
abbrev cR (s : State) : Region := ⟨argumentPointer s 13, (arg s 14).toNat * 8⟩
/-- The arguments themselves. -/
abbrev aR (s : State) : Region := ⟨argAddr s 0, 60⟩
/-- The return address and the stack below it. -/
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 228#64, 228⟩

structure KeySearchABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 60 ≤ 2 ^ 32
  rd : s.rd = [dR s, rR s, cR s]
  wr : s.wr = [xR s, yR s, uR s, bR s, sR s, aR s]
  xy : (xR s).Disjoint (yR s)
  xu : (xR s).Disjoint (uR s)
  xd : (xR s).Disjoint (dR s)
  xr : (xR s).Disjoint (rR s)
  xb : (xR s).Disjoint (bR s)
  xs : (xR s).Disjoint (sR s)
  xc : (xR s).Disjoint (cR s)
  xa : (xR s).Disjoint (aR s)
  yu : (yR s).Disjoint (uR s)
  yd : (yR s).Disjoint (dR s)
  yr : (yR s).Disjoint (rR s)
  yb : (yR s).Disjoint (bR s)
  ys : (yR s).Disjoint (sR s)
  yc : (yR s).Disjoint (cR s)
  ya : (yR s).Disjoint (aR s)
  ud : (uR s).Disjoint (dR s)
  ur : (uR s).Disjoint (rR s)
  ub : (uR s).Disjoint (bR s)
  us : (uR s).Disjoint (sR s)
  uc : (uR s).Disjoint (cR s)
  ua : (uR s).Disjoint (aR s)
  db : (dR s).Disjoint (bR s)
  ds : (dR s).Disjoint (sR s)
  da : (dR s).Disjoint (aR s)
  rb : (rR s).Disjoint (bR s)
  rs : (rR s).Disjoint (sR s)
  ra : (rR s).Disjoint (aR s)
  bs : (bR s).Disjoint (sR s)
  bc : (bR s).Disjoint (cR s)
  ba : (bR s).Disjoint (aR s)
  sc : (sR s).Disjoint (cR s)
  sa : (sR s).Disjoint (aR s)
  ca : (cR s).Disjoint (aR s)
  retX : (retR s).Disjoint (xR s)
  retY : (retR s).Disjoint (yR s)
  retU : (retR s).Disjoint (uR s)
  retD : (retR s).Disjoint (dR s)
  retRand : (retR s).Disjoint (rR s)
  retB : (retR s).Disjoint (bR s)
  retS : (retR s).Disjoint (sR s)
  retC : (retR s).Disjoint (cR s)
  retA : (retR s).Disjoint (aR s)
  lowX : (lowR s).Disjoint (xR s)
  lowY : (lowR s).Disjoint (yR s)
  lowU : (lowR s).Disjoint (uR s)
  lowD : (lowR s).Disjoint (dR s)
  lowRand : (lowR s).Disjoint (rR s)
  lowB : (lowR s).Disjoint (bR s)
  lowS : (lowR s).Disjoint (sR s)
  lowC : (lowR s).Disjoint (cR s)
  lowA : (lowR s).Disjoint (aR s)
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  uBound : (arg s 4).toNat + 8 ≤ 2 ^ 32
  dBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  rBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  bBound : (arg s 10).toNat + (arg s 11).toNat * 8 ≤ 2 ^ 32
  sBound : (arg s 12).toNat + 128 ≤ 2 ^ 32
  cBound : (arg s 13).toNat + (arg s 14).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 7).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 7).toNat (arg s 6).toNat
  xLen : (arg s 1).toNat = (arg s 7).toNat
  yLen : (arg s 3).toNat = (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 7).toNat ≤ (arg s 11).toNat
  domValid : Spec.Ffdh.domainValid (arg s 7).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
  keys : (s.mem.readW (argumentPointer s 12) 64).toNat ≤ 128
  scalars : (s.mem.readW (argumentPointer s 12 + 8) 64).toNat ≤ 128
  width : s.mem.readW (argumentPointer s 12 + 16) 64 = BitVec.ofNat 64 (arg s 7).toNat
  ctxLen : (arg s 14).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 7).toNat
  ctx : Spec.Ffdh.generationPrecompute (arg s 7).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (argumentPointer s 13) (arg s 14).toNat)

theorem keySearchABI_of {s : State} (h : (Spec.Ffdh.cachedKeySearchContract abi stack).pre s) : KeySearchABI s := by
  sig_pre [Spec.Ffdh.cachedKeySearchContract, Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, abi, argSlots,
    argVal, argBytes, stackBelow, Spec.Ffdh.generationContextAt] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86.Cached.Search
