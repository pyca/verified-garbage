module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Frame
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.TCB.Mem

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the precondition

Untrusted: everything here is checked by Lean. `PreR s`: the shared
contract's precondition (`recoverPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preR_of`). As `vg_rsa_pkcs1_verify_precomputed`'s
(`VerifyPre.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `out`, `n`, `e`, the signature and the precomputed values
(the working space, the arguments on the stack and the stack the function
uses are `sR`, `aR` and `kR`). -/
abbrev oR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `recoverPrecomputedContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, gR s, pR s, aR s]
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  og : (oR s).Disjoint (gR s)
  os : (oR s).Disjoint (sR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (aR s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sp : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kg : (kR s).Disjoint (gR s)
  ks : (kR s).Disjoint (sR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wo : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  wn : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  we : (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wg : (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r6).toNat
  k2 : (s.gpr .r6).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .r8).toNat
  e2 : (s.gpr .r8).toNat ≤ (s.gpr .r6).toNat
  hh : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .r9).setWidth 32).toNat = some h ∧ (s.gpr .r4).toNat = h.len
  hs : Spec.Rsa.publicScratchWords (s.gpr .r6).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat

theorem preR_of {s : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi frameBytes).pre s) : PreR s := by
  have e : frameBytes = 2223 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn, we,
    wg, ws, wp, ⟨k1, k2⟩, e1, e2, hh, hs, hp⟩ := h
  exact ⟨sp1, by omega, hrd, hwr, on, oe, og, os, op, oa, ns, es, gs, sp, sa, ko, kn, ke, kg, ks, kp, ka, wo, wn,
    we, wg, ws, wp, k1, k2, e1, e2, hh, hs, hp⟩

/-- The hash's length, at least one octet. -/
theorem PreR.len_pos {s : State} (hp : PreR s) : 1 ≤ (s.gpr .r4).toNat := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

/-- The hash's length, at most 64 octets. -/
theorem PreR.len_le {s : State} (hp : PreR s) : (s.gpr .r4).toNat ≤ 64 := by
  obtain ⟨h, -, e⟩ := hp.hh
  rw [e]; cases h <;> decide

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
