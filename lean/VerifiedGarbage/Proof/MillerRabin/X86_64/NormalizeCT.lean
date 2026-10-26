module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Normalization observes only the public workspace and limb count -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.MillerRabin.X86_64 VG.Impl.Bignum

structure NormalizePub where
  B : Addr
  wr : List Region
  w : Nat

def NormalizePre (p : NormalizePub) (s : State) : Prop :=
  KW p.B p.wr ∧ HP p.B p.wr [(sW, BitVec.ofNat 64 p.w)] s

theorem normalize_ct : RelCT isa (Two NormalizePre) (.block normalize) fun _ _ => True := by
  apply kt_ct NormalizePub.B NormalizePub.wr [sW]
    (fun p => [(sW, BitVec.ofNat 64 p.w)]) []
  · simp only [List.mem_singleton]
    rintro j rfl
    decide
  · intro p
    rfl
  · intro p s h
    exact h
  · intro p s t hs ht r hr
    cases hr
  · taint_decide

end VG.Proof.MillerRabin.X86_64
