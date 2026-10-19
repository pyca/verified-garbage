module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224
meta import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha224
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Sha1.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha512.Arm.Shared
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Md5.Arm.Shared
meta import VerifiedGarbage.Proof.Pbkdf2.Memory
meta import VerifiedGarbage.Proof.Sha1.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-!
# PBKDF2-HMAC-SHA-224 on 32-bit ARM, the whole derivation

The generic proof (`CT.lean`) at SHA-224
(`Proof/Pbkdf2/Stream/Arm/Sha224.lean`), as for the other hash functions
(`Instances.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Pbkdf2.Stream.Arm (sha224H sha224OK)

def sha224F : Fns := fnsOf Spec.Hmac.sha224I Md.Arm.sha224Md

theorem sha224_checks : Checks sha224F := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

def sha224OKF : FnsOK sha224F where
  hH := sha224OK
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha224_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha224_sat : ∃ s, (Spec.Hmac.sha224I.pbkdf2ScratchContract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 200

theorem sha224 : Verified Arm.target sha224F.pbkdf2 (Spec.Hmac.sha224I.pbkdf2ScratchContract Arm.abi 24) :=
  verified sha224OKF sha224_checks rfl rfl sha224_sat

end VG.Proof.Pbkdf2.Whole.Arm
