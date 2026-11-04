module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on PPC64LE: the functions it calls

What the proof needs of a hash function (`Kit`): its streaming functions
with what the proofs know of them (`HashOK`, `HashCT`), and the functions an
indirect call of a table's functions may reach. The call of the signature
with a given `k` (`coreCall`), against the curve's contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Impl.RsaOaep.PPC64LE (Fns)

/-- What the proof needs of a hash function: its streaming functions, with
what the proofs know of them (`HashOK`) and their constant time (`HashCT`),
and the functions an indirect call of a table's functions may reach. -/
structure Kit where
  H : Hash
  hH : HashOK H
  ct : Proof.RsaOaep.PPC64LE.HashCT hH
  f : Fns
  /-- The working space of the streaming functions, between the states and
  the padded key, and the states, in 192 bytes. -/
  hW : Impl.Ecdsa.Rfc6979.PPC64LE.sWork + H.W ≤ Impl.Ecdsa.Rfc6979.PPC64LE.sPad
  hS : H.S ≤ 192

/-- The signature with a given `k`, as the code calls it: the curve's
contract, its code and its name. -/
structure Core where
  E : Spec.Ecdsa.Instance
  C : Prog isa
  N : String
  V : ∀ s, (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pre s → ∃ t s', Exec isa C s t s' ∧ abiPreserved s s' ∧
    (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).post s s'
  ct : ConstantTime isa (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pre (Proof.Ecdsa.Instance.signContract E PPC64LE.abi).pub C
  d : sdepth C ≤ 96

theorem corePre (R : Core) {s : State} {out d dg k scr : Addr}
    (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = d) (h5 : s.gpr .r5 = dg) (h6 : s.gpr .r6 = k)
    (h7 : s.gpr .r7 = scr)
    (o₁ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨d, R.E.curve.len⟩)
    (o₂ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨dg, R.E.curve.len⟩)
    (o₃ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨k, R.E.curve.len⟩)
    (o₄ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₁ : Region.Disjoint ⟨d, R.E.curve.len⟩ ⟨scr, 8192⟩) (c₂ : Region.Disjoint ⟨dg, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₃ : Region.Disjoint ⟨k, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (n₁ : out.toNat + 2 * R.E.curve.len ≤ 2 ^ 64) (n₂ : d.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₃ : dg.toNat + R.E.curve.len ≤ 2 ^ 64) (n₄ : k.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₅ : scr.toNat + 8192 ≤ 2 ^ 64)
    : (Proof.Ecdsa.Instance.signContract R.E PPC64LE.abi).pre (s.callEntry.withRegions
      [⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩] [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩]) := by
  sig_pre [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  simp only [h3, h4, h5, h6, h7]
  exact ⟨trivial, trivial, o₁, o₂, o₃, o₄, c₁, c₂, c₃, n₁, n₂, n₃, n₄, n₅⟩

/-- The call of the signature with `k`: `out` of `2 Q` bytes, `d`, the
digest and `k` of `Q` each, the working space at `scr`. -/
theorem coreCall (R : Core) {s : State} {out d dg k scr : Addr}
    (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = d) (h5 : s.gpr .r5 = dg) (h6 : s.gpr .r6 = k)
    (h7 : s.gpr .r7 = scr)
    (o₁ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨d, R.E.curve.len⟩)
    (o₂ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨dg, R.E.curve.len⟩)
    (o₃ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨k, R.E.curve.len⟩)
    (o₄ : Region.Disjoint ⟨out, 2 * R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₁ : Region.Disjoint ⟨d, R.E.curve.len⟩ ⟨scr, 8192⟩) (c₂ : Region.Disjoint ⟨dg, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (c₃ : Region.Disjoint ⟨k, R.E.curve.len⟩ ⟨scr, 8192⟩)
    (n₁ : out.toNat + 2 * R.E.curve.len ≤ 2 ^ 64) (n₂ : d.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₃ : dg.toNat + R.E.curve.len ≤ 2 ^ 64) (n₄ : k.toNat + R.E.curve.len ≤ 2 ^ 64)
    (n₅ : scr.toNat + 8192 ≤ 2 ^ 64)
    (hc : Covers ([⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩] ++
      [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩] ++ [below s.sp 96]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (match Spec.Ecdsa.signWith R.E.curve (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem d R.E.curve.len))
          (Spec.Ecdsa.hashToInt R.E.curve (Spec.Ecdsa.bytesAt s.mem dg R.E.curve.len))
          (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem k R.E.curve.len)) with
        | some rs => (s'.gpr .r3).setWidth 32 = (1 : BitVec 32) ∧
            Spec.Ecdsa.bytesAt s'.mem out (2 * R.E.curve.len) = Spec.Ecdsa.encode R.E.curve rs
        | none => (s'.gpr .r3).setWidth 32 = (0 : BitVec 32) ∧
            Spec.Ecdsa.bytesAt s'.mem out (2 * R.E.curve.len) = List.replicate (2 * R.E.curve.len) 0) →
      Q s') :
    WP isa (.call R.N R.C) s Q := by
  refine WP.callAny (k := Proof.Ecdsa.Instance.signContract R.E PPC64LE.abi) R.V
    (rd := [⟨d, R.E.curve.len⟩, ⟨dg, R.E.curve.len⟩, ⟨k, R.E.curve.len⟩])
    (wr := [⟨out, 2 * R.E.curve.len⟩, ⟨scr, 8192⟩])
    (corePre R h3 h4 h5 h6 h7 o₁ o₂ o₃ o₄ c₁ c₂ c₃ n₁ n₂ n₃ n₄ n₅) hc hw ?_ (by have := R.d; omega_arith)
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    sig_post [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
      PPC64LE.abi, PPC64LE.argRegs, stackBelow] at hpost
    simp only [h3, h4, h5, h6] at hpost
    exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by have := R.d; omega_arith) (by omega_arith)) hcs hpost

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
