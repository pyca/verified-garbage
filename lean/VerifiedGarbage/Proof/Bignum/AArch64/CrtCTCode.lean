module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_private_crt` on AArch64: constant time

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`), given that `n`'s setup is
constant time.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA stackArgs_ten)

/-- The public data of `vg_rsa_private_crt`: `main`'s and the stack pointer. -/
structure CCPub where
  m : CrtPub
  sp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CCRel (p : CCPub) (s : State) : Prop :=
  crtA.pre s ∧ s.sp = p.sp ∧ stackArg s 8 = p.m.B ∧ (stackArg s 9).toNat * 8 = p.m.Z ∧
    (s.gpr .x3).toNat = p.m.k ∧ s.gpr .x0 = p.m.op ∧ s.gpr .x2 = p.m.np ∧ s.gpr .x4 = p.m.ip ∧
    s.gpr .x6 = p.m.pp ∧ stackArg s 0 = p.m.qp ∧ stackArg s 2 = p.m.dpp ∧ stackArg s 4 = p.m.dqp ∧
    stackArg s 6 = p.m.qip ∧ (s.gpr .x7).toNat = p.m.pl ∧ (stackArg s 1).toNat = p.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.m.nb

theorem CCRel.x3 {p : CCPub} {s : State} (h : CCRel p s) : s.gpr .x3 = BitVec.ofNat 64 p.m.k := by
  rw [← h.2.2.2.2.1, ofNat_toNat64]

/-- After `entry` and the modulus' check, from `s`. -/
def HeadPost (s t : State) : Prop :=
  ∃ t₁, CrtHeadPost s t₁ ∧ t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) (s.gpr .x3).toNat).toNat ∧
    t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t

/-- `entry` and the modulus' check. -/
theorem crtHeadChk_ok {s : State} (c : CrtCtx s) : WP isa (.block (entry ++ invalid)) s (HeadPost s) := by
  have hk1 := c.hk1
  have hk2 := c.hk2
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  exact WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (h₁.keep.gpr .x2 (by decide))
    (by rw [h₁.keep.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
    (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ⟨t₁, h₁, hz₂, hm₂, k₂⟩

theorem head_split : entry ++ invalid = ([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ invalid) := rfl

/-- After `entry`'s first instruction. -/
def CC1 (p : CCPub) (t : State) : Prop :=
  ∃ s, CCRel p s ∧ t.gpr .x8 = p.m.B ∧ t.gpr .x2 = p.m.np ∧ t.gpr .x3 = BitVec.ofNat 64 p.m.k ∧
    WP isa (.block (entry.drop 1 ++ invalid)) t (HeadPost s)

/-- After `entry` and the modulus' check. -/
def CC3 (p : CCPub) (t : State) : Prop := ∃ s, CCRel p s ∧ HeadPost s t

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cc3_pre {p : CCPub} {t : State} (h : CC3 p t) :
    ∃ xb pb qb dpb dqb qib, CrtPre t p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp
      p.m.qip p.m.pl p.m.ql p.m.nb xb pb qb dpb dqb qib := by
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩, t₁, h, -, hm, k⟩ := h
  have := crtPre_of (crtCtx_of hpre) h hm k
  rw [hnb] at this
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at this
  exact ⟨_, _, _, _, _, _, this⟩

/-- The validity of `n`, in `x9`. -/
theorem cc3_x9 {p : CCPub} {t : State} (h : CC3 p t) :
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid p.m.N p.m.k).toNat := by
  obtain ⟨s, ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hnb⟩, t₁, -, hz, -⟩ := h
  rw [hz, hnb, hk]

variable (M : Mont)

/-- The public data of a state. -/
def ccPubOf (s : State) : CCPub :=
  ⟨⟨stackArg s 8, (stackArg s 9).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2, s.gpr .x4, s.gpr .x6,
    stackArg s 0, stackArg s 2, stackArg s 4, stackArg s 6, (s.gpr .x7).toNat, (stackArg s 1).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩, s.sp⟩

end VG.Proof.Bignum.AArch64
