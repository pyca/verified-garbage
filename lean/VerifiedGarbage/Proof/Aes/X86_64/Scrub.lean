module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Frame
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# The AES key expansion on x86-64, without secret residue

`vg_aes_expand_key` and `vg_aes_expand_key_aesni`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postcondition reads the
memory on return only within the schedule (`Proof.Aes.expandKeyPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract X86_64.abi stack) (Spec.Aes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

/-- `vg_aes_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey

def expandKeyKs : List Nat := keep_for% Spec.Aes.expandKeyApi.sig 520 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Aes.expandKeyApi.sig 520 []) expandKeyCode
      h).any (RScrub.resOkB · 520 expandKeyKs (Impl.Scrub.X86_64.chunks 520)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

def expandKeyAesniKs : List Nat :=
  keep_for% Spec.Aes.expandKeyApi.sig 0 Impl.Aes.X86_64.AesNi.expandKey []

theorem expandKeyAesniOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Aes.expandKeyApi.sig 0 [])
      Impl.Aes.X86_64.AesNi.expandKey h).any
      (RScrub.resOkB · 0 expandKeyAesniKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of expandKeyAesniKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_aes_expand_key`. -/
def expandKeyReg : Registration Spec.Aes.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 520
    verified := Proof.Aes.X86_64.scalar_expandKey_framed }
    (expandKeyOut _) [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

open VG.X86_64.RScrub in
/-- `vg_aes_expand_key_aesni`. -/
def expandKeyAesniReg : Registration Spec.Aes.expandKeyApi X86_64.target :=
  withScrub {
    suffix := "_aesni"
    code := Impl.Aes.X86_64.AesNi.expandKey
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey3_verified }
    (expandKeyOut _) [] (pubOk_nil _) (some ⟨expandKeyAesniKs, expandKeyAesniOk⟩)

end VG.Proof.Aes.X86_64.Scrub
