module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowQ
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHeadCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
meta import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.CrtResult
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.CrtResult
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid

/-! ### `Bignum.AArch64.CrtCTCode`, which only this module used -/

section

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

/-- A state the contract allows, with the public data `p`, for a key whose
modulus and factors satisfy `G`. -/
def CCRel (G : Nat → Nat → Nat → Prop) (p : CCPub) (s : State) : Prop :=
  crtA.pre s ∧ s.sp = p.sp ∧ stackArg s 8 = p.m.B ∧ (stackArg s 9).toNat * 8 = p.m.Z ∧
    (s.gpr .x3).toNat = p.m.k ∧ s.gpr .x0 = p.m.op ∧ s.gpr .x2 = p.m.np ∧ s.gpr .x4 = p.m.ip ∧
    s.gpr .x6 = p.m.pp ∧ stackArg s 0 = p.m.qp ∧ stackArg s 2 = p.m.dpp ∧ stackArg s 4 = p.m.dqp ∧
    stackArg s 6 = p.m.qip ∧ (s.gpr .x7).toNat = p.m.pl ∧ (stackArg s 1).toNat = p.m.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.m.nb ∧
    G (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))

theorem CCRel.x3 {G : Nat → Nat → Nat → Prop} {p : CCPub} {s : State} (h : CCRel G p s) : s.gpr .x3 = BitVec.ofNat 64 p.m.k := by
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
def CC1 (G : Nat → Nat → Nat → Prop) (p : CCPub) (t : State) : Prop :=
  ∃ s, CCRel G p s ∧ t.gpr .x8 = p.m.B ∧ t.gpr .x2 = p.m.np ∧ t.gpr .x3 = BitVec.ofNat 64 p.m.k ∧
    WP isa (.block (entry.drop 1 ++ invalid)) t (HeadPost s)

/-- After `entry` and the modulus' check. -/
def CC3 (G : Nat → Nat → Nat → Prop) (p : CCPub) (t : State) : Prop := ∃ s, CCRel G p s ∧ HeadPost s t

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cc3_pre {G : Nat → Nat → Nat → Prop} {p : CCPub} {t : State} (h : CC3 G p t) :
    ∃ xb pb qb dpb dqb qib, CrtPre t p.m.B p.m.Z p.m.k p.m.op p.m.np p.m.ip p.m.pp p.m.qp p.m.dpp p.m.dqp
      p.m.qip p.m.pl p.m.ql p.m.nb xb pb qb dpb dqb qib ∧ G p.m.N (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) := by
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb, hg⟩, t₁, h, -, hm, k⟩ := h
  have := crtPre_of (crtCtx_of hpre) h hm k
  rw [hnb] at this hg
  rw [hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql] at this
  rw [hpp, hqp, hpl, hql] at hg
  exact ⟨_, _, _, _, _, _, this, hg⟩

/-- The validity of `n`, in `x9`. -/
theorem cc3_x9 {G : Nat → Nat → Nat → Prop} {p : CCPub} {t : State} (h : CC3 G p t) :
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid p.m.N p.m.k).toNat := by
  obtain ⟨s, ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hnb, -⟩, t₁, -, hz, -⟩ := h
  rw [hz, hnb, hk]

variable (M : Mont)

/-- The public data of a state. -/
def ccPubOf (s : State) : CCPub :=
  ⟨⟨stackArg s 8, (stackArg s 9).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2, s.gpr .x4, s.gpr .x6,
    stackArg s 0, stackArg s 2, stackArg s 4, stackArg s 6, (s.gpr .x7).toNat, (stackArg s 1).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩, s.sp⟩

end VG.Proof.Bignum.AArch64

end

end

/-! ### `Bignum.AArch64.CrtWindowDispatchCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowDispatch`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

abbrev alignedPrimes (pl ql : Nat) : Prop :=
  ((BitVec.ofNat 64 pl ||| BitVec.ofNat 64 ql) &&& 63) = 0

def guardValue (k pl ql : Nat) : BitVec 64 :=
  if alignedPrimes pl ql then BitVec.ofNat 64 k >>> 7 else 0

theorem pre_keep {s t : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hm : t.mem = s.mem) (hk : Keep [.x9,.x10,.x11] s t) :
    CrtPre t B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib := by
  have im : InScr B Z s.mem t.mem := by rw [hm]; exact InScr.refl _ _ _
  exact {
    scr := h.scr.congr hk.wr
    x0 := (hk.gpr .x0 (by decide)).trans h.x0
    z := h.z
    zk := h.zk
    k1 := h.k1
    k2 := h.k2
    hO := by simpa only [hm] using h.hO
    hN := by simpa only [hm] using h.hN
    hK := by simpa only [hm] using h.hK
    hIn := by simpa only [hm] using h.hIn
    hP := by simpa only [hm] using h.hP
    hPl := by simpa only [hm] using h.hPl
    hQ := by simpa only [hm] using h.hQ
    hQl := by simpa only [hm] using h.hQl
    hDp := by simpa only [hm] using h.hDp
    hDq := by simpa only [hm] using h.hDq
    hQi := by simpa only [hm] using h.hQi
    n := h.n.congrK im hk
    x := h.x.congrK im hk
    p := h.p.congrK im hk
    q := h.q.congrK im hk
    dp := h.dp.congrK im hk
    dq := h.dq.congrK im hk
    qi := h.qi.congrK im hk
    nl := h.nl
    xl := h.xl
    pbl := h.pbl
    qbl := h.qbl
    dpl := h.dpl
    dql := h.dql
    qil := h.qil
    pl1 := h.pl1
    pl2 := h.pl2
    ql1 := h.ql1
    ql2 := h.ql2
    out := by simpa only [hk.wr] using h.out
    outSep := h.outSep
  }

theorem exec_tst_x (s : State) (n m : Reg) :
    exec (.tst .x n m) s = some { s with
      nf := (s.read .x n &&& s.read .x m).msb
      zf := decide ((s.read .x n &&& s.read .x m) = 0)
      c := false
      vf := false } := rfl

theorem exec_csel_eq (s : State) (d n m : Reg) :
    exec (.cselc .x d n m .eq) s =
      some (s.write .x d (if s.zf then s.read .x n else s.read .x m)) := rfl

theorem lengthGuard_ok {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.lengthGuard) s fun t =>
      t.gpr .x9 = guardValue k pl ql ∧ t.mem = s.mem ∧ Keep [.x9,.x10,.x11] s t := by
  have hz := h.zk
  have hk := h.k1
  exact WP.mono (WP.keep [.x9,.x10,.x11] (Q := fun t => t.gpr .x9 = guardValue k pl ql ∧ t.mem = s.mem)
    (by brun [VG.Impl.Rsa.AArch64.WindowFive.lengthGuard,h.x0,hdr_enc (show Public.sK < 32 by decide),
      h.scr.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega_using [hz, hk]),h.hK,
      hdr_enc (show VG.Impl.Bignum.Crt.sPlen < 32 by decide),
      hdr_enc (show VG.Impl.Bignum.Crt.sQlen < 32 by decide),
      h.scr.ld (d := 8 * VG.Impl.Bignum.Crt.sPlen) (by unfold VG.Impl.Bignum.Crt.sPlen sFn; omega_using [hz, hk]),
      h.scr.ld (d := 8 * VG.Impl.Bignum.Crt.sQlen) (by unfold VG.Impl.Bignum.Crt.sQlen sFn; omega_using [hz, hk]),
      h.hPl,h.hQl,guardValue,alignedPrimes,CondCode.holds,exec_tst_x,exec_csel_eq,RegUpd.zf_write]
        simp only [decide_eq_true_eq]
        rfl)
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨hv,hm⟩,kk⟩ => ⟨hv,hm,kk⟩

theorem lengthGuard_zero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k >>> 7 == (0 : BitVec 64)) = decide (k < 128) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
  change k / 128 = 0 ↔ k < 128
  omega_using []

theorem guardValue_nonzero {k pl ql : Nat} (hk : k < 2 ^ 64)
    (h : (guardValue k pl ql == (0 : BitVec 64)) = false) : 128 ≤ k := by
  by_cases ha : alignedPrimes pl ql
  · simp only [guardValue,ite_eq_left ha,lengthGuard_zero hk] at h
    simpa using h
  · simp [guardValue,ha] at h

theorem dispatch_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.dispatchWith C W.code S.code M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.dispatchWith
  refine WP.seq (WP.mono (lengthGuard_ok h) fun t ⟨h9,hm,kk⟩ => ?_)
  have ht := pre_keep h hm kk
  have hk64 : k < 2 ^ 64 := by have := h.k2; omega_using [this]
  have finish : ∀ u r c, MainPost t u B Z k op r c → MainPost s u B Z k op r c := by
    intro u r c hp
    exact ⟨hp.bytes,hp.x0,fun x hx ho => by rw [hp.frame x hx ho,hm],
      (kk.trans hp.keep).mono (by decide)⟩
  refine WP.ite (guardValue k pl ql == (0 : BitVec 64)) (by rw [eval_zero,h9]) ?_ ?_
  · intro _
    exact WP.mono (VG.Proof.Bignum.AArch64.crtMain_ok M ht hv hC hG)
      fun u ⟨c,hp,hi⟩ => ⟨c,finish u _ _ hp,hi⟩
  · intro hk
    have h128 : 128 ≤ k := guardValue_nonzero hk64 hk
    exact WP.mono (crtMain_ok W M S ht h128 hv hC hG)
      fun u ⟨c,hp,hi⟩ => ⟨c,finish u _ _ hp,hi⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowConstantTime`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowFinCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowMainCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowPCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowPowCT`, which this module and modules that import it used -/

section

/-! Constant time for conversion followed by five-bit exponentiation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

def Wide (p : XPub) : Prop := p.o + slot p.wx 8 + CrtWindowFive.tabBytes32 p.wx ≤ p.Z

def PwPreWide (sl sd slen : Nat) (p : BPub) (s : State) : Prop :=
  PwPre sl sd slen p s ∧ Wide p.x

def P1Wide (sd slen : Nat) (p : BPub) (s : State) : Prop :=
  CrtCTQ.P1 sd slen p s ∧ Wide p.x

def PowCT (W : Window) (M : Mont) (S : Selector) (sl sd slen : Nat) : Prop :=
  RelCT isa (Two (PwPreWide sl sd slen))
    (seqs (powSteps W.code S.code M.mm sl sd slen)) (fun _ _ => True)

theorem blk_p1_wide {sl sd slen : Nat} {p : BPub} {s : State} (h : PwPreWide sl sd slen p s) :
    WP isa (.block [ldh .x0 sl]) s (P1Wide sd slen p) :=
  WP.mono (CrtCTQ.blk_p1 h.1) fun _ ht => ⟨ht,h.2⟩

theorem redc_ePre_wide (M : Mont) {sd slen : Nat} {p : BPub} {s : State}
    (h : P1Wide sd slen p s) :
    WP isa (seqs (redc M.mm Public.aY)) s (EPreWide sd slen p) :=
  WP.mono (CrtCTQ.redc_ePre M h.1) fun _ ht => ⟨ht,h.2⟩

theorem pow_ct (W : Window) (M : Mont) (S : Selector) {sl sd slen : Nat}
    (hR : RedcCT M Public.aY)
    (hE : RelCT isa (Two (EPreWide sd slen))
      (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen) (fun _ _ => True))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x0 sl]) hc).isSome = true) :
    PowCT W M S sl sd slen := by
  unfold PowCT powSteps
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq
    (two_piece (Ψ := P1Wide sd slen) [.x0]
      (pins_x0B (fun p : BPub => p.x.B) fun _ _ ⟨⟨_,_,_,_,_,_,hg,_⟩,_⟩ => hg.x0)
      hT fun _ _ h => blk_p1_wide h) ?_)
  exact RelCT.seqs_append (by simp [redc]) (by simp) (RelCT.seq
    (two_post (Ψ := EPreWide sd slen)
      (two_map BPub.x (fun _ _ ⟨⟨mx,X,_,hc,_,hX,hwx2,hwx,hw28,hX1,_⟩,_⟩ =>
        ⟨mx,X,hc,hX,hwx2,hwx,by omega_using [hw28],hX1,by decide⟩) hR)
      fun _ _ h => redc_ePre_wide M h) hE)

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-!
# RSA with the CRT on AArch64: constant time, `p`'s phase

`pPhase` is constant time (`pPhase_ct`) given its pieces' claims: before
each piece, a predicate (`PO0` … `PO4`, then `hSteps`' `H0`) carries the
piece's hypotheses and what correctness gives after it; `o0_of` proves the
first from `PPre`, as `p`'s phase runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

def PPreWide (p : PPhasePub) (s : State) : Prop := PPre p s ∧ Wide p.pw.x

def PPhaseCT (W : Window) (M : Mont) (S : Selector) : Prop :=
  RelCT isa (Two PPreWide)
    (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) (fun _ _ => True)

/-- Before the way back to the modulus' workspace. -/
def PO4 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  s.gpr .x0 = off p.ph.B p.ph.o ∧ WP isa (.block [leave]) s (H0 M p.h)

/-- Before the exponentiation. -/
def PO3 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  PwPreWide sWsP sDp sPlen p.pw s ∧ WP isa (seqs (powSteps W.code S.code M.mm sWsP sDp sPlen)) s (PO4 M p)

/-- Before `c G mod N`. -/
def PO2 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (PO3 W M S p)

/-- Before `m_q G mod N`. -/
def PO1 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (PO2 W M S p)

/-- Before `pPhase`. -/
def PO0 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s (PO1 W M S p)

/-- From before the exponentiation: `PO3`, as `p`'s phase runs the rest. -/
theorem o3_of (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (hwide : o + slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hcg : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hpl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hpy : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    PO3 W M S ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have ho64 : o < 2 ^ 64 := by omega_using [hhi, hn, hX8]
  -- `c^dP R_p mod p`.
  refine ⟨⟨⟨minv, mx, N, X, C, eb, hg, hw28, hlo, hhi, hwx2, hwx, by decide, hslv, hws, hX, hX1, hXodd, hcg, hpl,
      hpy, by decide, by decide, hep, hel, rfl, hL1, hL2, he⟩,hwide⟩,
    WP.mono (powPhase_ok W M S hg hw28 hlo hwide hwx2 hwx (sl := sWsP) (by decide) hslv hws hX hX1 hXodd hcg hpl hpy
      (sd := sDp) (slen := sPlen) (by decide) (by decide) hep hel hL1 hL2 he)
      fun s₄ ⟨hc₄, hX₄, hlt₄, _, hM₄, fx₄, k₄⟩ => ?_⟩
  -- Back to the modulus'.
  refine ⟨hc₄.x0, WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₄.mem)
    (by brun [leave, hc₄.x0, hdr_enc (show sLink < 32 by decide), hc₄.ld' (show sLink < 32 by decide), hc₄.link'])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_⟩
  have fx₅ : Frm B [CrtWindowFive.xRange32 o wx] s.mem s₅.mem := by rw [hm₅]; exact fx₄
  have k05 := k₄.trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s.mem B d := fun d hd => CrtWindowFive.x_below32 fx₅ hd ho64
  have hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.wr, hdi₅, ⟨(hb₅ _ (by unfold sW; omega_using [hlo, h8])).trans hg.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega_using [hlo, h8])).trans hg.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_using [hj]); omega_using [hlo, this])).trans
      (hg.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm fx₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [CrtWindowFive.xRange32]; omega_using [hwide, hX8]
  -- `h`.
  have a1 : word s₅.mem B (8 * sWsP) = off B o := by rw [hb₅ _ (by unfold sWsP sFn; omega_using [hlo, h8])]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by rw [hm₅, hM₄]; exact hmask
  have a6 : word s₅.mem B (8 * sQinv) = qp := by rw [hb₅ _ (by unfold sQinv sFn; omega_using [hlo, h8])]; exact hqp
  have a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₅ _ (by unfold sPlen sFn; omega_using [hlo, h8]), hql]; exact hel
  have := h_chain M hg₅ hw28 hlo hhi hwx2 hwx a1 a2 hX₅ hX1 a3 a5 a6 a7 (hqs.congrK i05 k05) (by omega_using [hL1, hql])
    (by omega_using [hL2, hql]) hqw hqi
  rw [hql] at this
  exact this

/-- The hypotheses of `p`'s phase give `PO0`. -/
theorem o0_of (W : Window) (M : Mont) (S : Selector) {p : PPhasePub} {s : State} (h : PPreWide p s) : PO0 W M S p s :=
  -- `o0_of`'s proof with this exponentiation, whose `o3_of` also takes `Wide`: `tabBytes32` is `wsTab`.
  o0_gen M (PO3 W M S) (fun hg hw28 hlo hhi hwx2 hwx hslv hws hX hX1 hXodd hcg hpl hpy hep hel hL1 hL2 he hmask hqp
    hql hqs hqw hqi => o3_of W M S hg hw28 hlo hhi hhi hwx2 hwx hslv hws hX hX1 hXodd hcg hpl hpy hep hel hL1 hL2 he
      hmask hqp hql hqs hqw hqi) h.1

/-- `p`'s phase is constant time, given its pieces' claims. -/
theorem pPhase_ct (W : Window) (M : Mont) (S : Selector) (hU : UnitCT M sWsP) (hP : PowCT W M S sWsP sDp sPlen) (hRX : RedcCT M Public.aX)
    (hL : LoadCT aChunk sQinv sPlen) : PPhaseCT W M S := by
  unfold PPhaseCT
  refine two_map id (fun _ _ h => o0_of W M S h) ?_
  rw [pPhase_eq]
  refine ct_steps (by simp [unitSteps]) (by simp [mqSteps]) PPhasePub.u (fun _ _ h => h.1) (fun _ _ h => h.2)
    hU ?_
  refine ct_steps (by simp [mqSteps]) (by simp) PPhasePub.mq (fun _ _ h => h.1) (fun _ _ h => h.2) (mq_ct M) ?_
  refine ct_steps (by simp) (by simp [powSteps]) PPhasePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [powSteps]) (by simp) PPhasePub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) hP ?_
  refine RelCT.seqs_append (by simp) (by simp [hSteps]) (ct_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact two_map PPhasePub.h (fun _ _ h => h) (h_ct M hRX hL)

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowSetupCT`, which only this module used -/

section

/-!
# RSA with the CRT on AArch64: constant time of the primes' setup

`WindowFive.primesSetup` is the code of `Crt.primesSetup`, and its
precondition is `SetupPre`'s (`offQ32` is `offQ`, `tabBytes32` is `wsTab`):
`setup_ct` is the 4-bit setup's.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive

def SetupPre (p : SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ32 p.w p.pl + slot (wsWords p.ql) 8 + tabBytes32 (wsWords p.ql) ≤ p.Z ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word s.mem p.B (8 * sP) = p.pp ∧ word s.mem p.B (8 * sQ) = p.qp ∧ word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two SetupPre) (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) fun _ _ => True

theorem setup_ct : SetupCT := VG.Proof.Bignum.AArch64.setup_ct

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowQCT`, which only this module used -/

section

/-! Constant time for the q phase with the wider window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

def QPreWide (p : PhasePub) (s : State) : Prop := QPre p s ∧ Wide (CrtCTQ.sp p).x

def Q1Wide (p : PhasePub) (s : State) : Prop := CrtCTQ.Q1 p s ∧ Wide (CrtCTQ.sp p).x

def QPhaseCT (W : Window) (M : Mont) (S : Selector) : Prop :=
  RelCT isa (Two QPreWide)
    (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) (fun _ _ => True)

theorem unit_q1_wide (M : Mont) {p : PhasePub} {s : State} (h : QPreWide p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (Q1Wide p) :=
  WP.mono (CrtCTQ.unit_q1 M h.1) fun _ ht => ⟨ht,h.2⟩

theorem mm_pwPre_wide (M : Mont) {p : PhasePub} {s : State} (h : Q1Wide p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p)) :=
  WP.mono (CrtCTQ.mm_pwPre M h.1) fun _ ht => ⟨ht,h.2⟩

theorem pow_q3_wide (W : Window) (M : Mont) (S : Selector) {p : PhasePub} {s : State}
    (h : PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p) s) :
    WP isa (seqs (powSteps W.code S.code M.mm sWsQ sDq sQlen)) s (CrtCTQ.Q3 p) := by
  obtain ⟨h,hwide⟩ := h
  obtain ⟨_,mx,_,X,_,eb,hg,hw28,hlo,_,hwx2,hwx,hsl,hslv,hws,hX,hX1,hXodd,hnY,hyl,hyc,hsd,
    hsln,hep,hel,_,hL1,hL2,he⟩ := h
  exact WP.mono (powPhase_ok W M S hg hw28 hlo hwide hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc
    hsd hsln hep hel hL1 hL2 he) fun _ ⟨hc,hX',_⟩ =>
      ⟨mx,X,hc,hX',hX1,hwx2,(by omega_using [hw28, hwx] : (CrtCTQ.sp p).x.wx < 2 ^ 28)⟩

theorem qPhase_ct (W : Window) (M : Mont) (S : Selector) (hU : UnitCT M sWsQ)
    (hP : PowCT W M S sWsQ sDq sQlen) : QPhaseCT W M S := by
  unfold QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps,gPow]) (by simp) (RelCT.seq
    (two_post (Ψ := Q1Wide) (two_map CrtCTQ.up (fun _ _ h => CrtCTQ.uPre h.1) hU)
      fun _ _ h => unit_q1_wide M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq
    (two_post (Ψ := fun p => PwPreWide sWsQ sDq sQlen (CrtCTQ.sp p))
      (two_map (fun p : PhasePub => (⟨p.B,p.Z,p.w⟩ : Ws))
        (fun _ _ ⟨⟨_,_,_,hg,_,_,hlo,hhi,_⟩,_⟩ => ⟨_,hg,by dsimp only; omega_using [hlo, hhi]⟩)
        (M.ct (by unfold MmUse; decide))) fun _ _ h => mm_pwPre_wide M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq
    (two_post (Ψ := CrtCTQ.Q3) (two_map CrtCTQ.sp (fun _ _ h => h) hP)
      fun _ _ h => pow_q3_wide W M S h) (CrtCTQ.mmLeave_ct M))

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-!
# RSA with the CRT on AArch64: `main` in constant time

`main` leaks the same in runs that agree on the public data (`CrtPub`: the
working space, the pointers, the lengths and `n`), from the constant time of
its parts (`crtMain_ct`). Its states between the parts are those of a run
from a state `CrtPre` describes (`Stage`), where the correctness lemmas of
the parts (`nPart_ok`, `setupPart_ok`, …) give what each part's claim needs.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32)
open VG.Proof.MlKem.AArch64 (Keep)

structure CrtPreWide (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr)
    (pl ql : Nat) (nb xb pb qb dpb dqb qib : List Byte) : Prop
    extends CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib where
  wide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z

/-- What holds of a state of a run from a state `σ` that `CrtPre` describes
with the public data `p`, the input `xb` and the private key. -/
abbrev StageRel := CrtPub → State → List Byte → List Byte → List Byte → List Byte → List Byte → List Byte →
  State → Prop

/-- A state satisfying `R` from such a start. -/
def Stage (R : StageRel) (p : CrtPub) (t : State) : Prop :=
  ∃ (σ : State) (xb pb qb dpb dqb qib : List Byte),
    CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ R p σ xb pb qb dpb dqb qib t

/-- A part constant time from a stage, with its correctness, goes to the
next stage. -/
theorem stage_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (Stage R)) c (Two (Stage R')) :=
  two_post hct fun p t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ =>
    WP.mono (hw p σ xb pb qb dpb dqb qib t h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h'⟩

theorem stage_forget {G : Nat → Nat → Nat → Prop} {R : StageRel} {p : CrtPub} {t : State}
    (h : Stage (RG G R) p t) : Stage R p t :=
  let ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, _, hr⟩ := h; ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩

theorem stage_true {R : StageRel} {p : CrtPub} {t : State} (h : Stage R p t) :
    Stage (RG (fun _ _ _ => True) R) p t :=
  let ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩ := h; ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, trivial, hr⟩

/-! ## The stages -/

def R0 : StageRel := fun _ σ _ _ _ _ _ _ t => t = σ

def R1 : StageRel := fun p σ xb _ _ _ _ _ t => ∃ minv, NReady σ t p.B p.Z p.w minv p.N (Spec.Rsa.os2ip xb)

def R2 : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, PReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)

def R3 : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, CrtReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

def R4 : StageRel := fun p σ xb pb qb _ dqb qib t => ∃ minv mp mq, QReady σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb (p.mask xb pb qb qib)

def R5 : StageRel := fun p σ xb pb qb dpb dqb qib t => ∃ minv mp mq, PDone σ t p.B p.Z p.w p.pl p.ql minv mp mq
  (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb (p.mask xb pb qb qib)

/-- `-n⁻¹` is the same in runs that agree on `n`. -/
theorem nv_minv {t t' : State} {B : Addr} {w : Nat} {mi mi' : BitVec 64} {N : Nat} (h : NVals t B w mi N)
    (h' : NVals t' B w mi' N) (hodd : N % 2 = 1) (hw : 1 ≤ w) : mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64}, NVals t B w mi N →
      (word t.mem B (slot w Public.aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-! ## From the stages to the parts' claims -/

/-- Runs at a stage agree on what a part needs, with `-n⁻¹` (the same in both
runs) among its public data. -/
theorem two_stage {R : StageRel} {α : Type} {Φ : α → State → Prop} (f : CrtPub → BitVec 64 → α)
    (m : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPreWide σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      ∃ minv, NVals t p.B p.w minv p.N ∧ Φ (f p minv) t)
    {s₁ s₂ : State} (h : Two (Stage R) s₁ s₂) : Two Φ s₁ s₂ := by
  obtain ⟨p, ⟨σ₁, xb₁, pb₁, qb₁, dpb₁, dqb₁, qib₁, h₁, hv, r₁⟩, ⟨σ₂, xb₂, pb₂, qb₂, dpb₂, dqb₂, qib₂, h₂, hv₂, r₂⟩, hsp⟩ := h
  obtain ⟨m₁, n₁, φ₁⟩ := m p _ _ _ _ _ _ _ _ h₁ hv r₁
  obtain ⟨m₂, n₂, φ₂⟩ := m p _ _ _ _ _ _ _ _ h₂ hv₂ r₂
  obtain ⟨hodd, -, -⟩ := valid_facts hv h₁.k1
  have := h₁.k1
  obtain rfl := nv_minv n₁ n₂ hodd (show 1 ≤ p.w by simp only [CrtPub.w]; omega_arith)
  exact ⟨_, φ₁, φ₂, hsp⟩

/-- The primes' setup leaks the same in runs that agree on the public data. -/
theorem setupS_ct (G : Nat → Nat → Nat → Prop) (hS : SetupCT) :
    RelCT isa (Two (Stage (RG G R1))) (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) (Two (Stage (RG G R2))) := by
  refine stage_step (hS.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.pl, p.ql, p.pp, p.qp,
    p.qip⟩ : SetupPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨_, minv, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨hg, minv, hr⟩ => WP.mono (setupPart_ok h.toCrtPre h.wide hr)
      fun _ h' => ⟨hg, minv, h'⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, pb, qb, qib, hr.good, by simp only [CrtPub.w]; omega_arith, by simp only [CrtPub.w]; omega_arith, hZq,
    by rw [hh _ (by decide) (by decide)]; exact h.hPl, by rw [hh _ (by decide) (by decide)]; exact h.hQl,
    by rw [hh _ (by decide) (by decide)]; exact h.hP, by rw [hh _ (by decide) (by decide)]; exact h.hQ,
    by rw [hh _ (by decide) (by decide)]; exact h.hQi, h.p.congrK hr.iscr hr.keep, h.q.congrK hr.iscr hr.keep,
    h.qi.congrK hr.iscr hr.keep, h.pbl, h.qbl, h.qil, h.pl1, ?_, h.ql1, ?_⟩
  · have := h.pl2; simp only [CrtPub.w]; omega_arith
  · have := h.ql2; simp only [CrtPub.w]; omega_arith

/-- The checks `C` leak the same in runs that agree on the public data. -/
theorem checksS_ct {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    RelCT isa (Two (Stage (RG G R2))) (seqs C) (Two (Stage R3)) := by
  refine stage_step (hC.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : ChecksPub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨_, minv, mp, mq, hr⟩ =>
      ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨hg, minv, mp, mq, hr⟩ =>
      WP.mono (checksPart_ok h.toCrtPre h.wide hv hr hok hg) fun _ ⟨mp', mq', h'⟩ => ⟨minv, mp', mq', h'⟩
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega_arith
  refine ⟨minv, hr.n.nv, ?_⟩
  unfold ChecksPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, _, _, hr.n.good, by omega_arith, by omega_arith,
    show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from Nat.le_refl _, by unfold offQ32 offP; omega_arith, by omega_arith, hwp2,
    wsWords_le (by have := h.pl2; omega_arith) (by omega_arith), hwq2, wsWords_le (by have := h.ql2; omega_arith) (by omega_arith),
    hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.n.nv.n, hr.n.msk, hr.pv, hr.qv, hr.qiv, hodd⟩

/-- `q`'s phase leaks the same in runs that agree on the public data. -/
theorem qS_ct (W : Window) (M : Mont) (S : Selector) (hQ : QPhaseCT W M S) : RelCT isa (Two (Stage R3)) (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) (Two (Stage R4)) := by
  refine stage_step (hQ.mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offQ32 p.w p.pl,
    wsWords p.ql, p.dqp, p.ql⟩ : PhasePub)) (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h)
      fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (qPart_ok W M S h.toCrtPre h.wide hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h.toCrtPre hv
  obtain ⟨-, -, hQ'⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hql1 := h.ql1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega_arith
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  refine ⟨?_,hZq⟩
  unfold QPre
  dsimp only [CrtPub.w]
  exact ⟨mq, _, _, dqb, hr.good, by omega_arith, by omega_arith,
    by unfold offQ32; omega_arith, by omega_arith, hwq2, wsWords_le (by omega_arith) (by omega_arith), hr.wsQ, hr.qws, hr.nv,
    hodd, hN1, hr.xm, hr.qxv, hQ'.1, hQ'.2, by rw [hh _ (by decide) (by decide)]; exact h.hDq,
    by rw [hh _ (by decide) (by decide), h.dql]; exact h.hQl, h.dql, by rw [h.dql]; omega_arith,
    by rw [h.dql]; omega_arith, h.dq.congrK hr.iscr hr.keep⟩

/-- `p`'s phase leaks the same in runs that agree on the public data. -/
theorem pS_ct (W : Window) (M : Mont) (S : Selector) (hP : PPhaseCT W M S) : RelCT isa (Two (Stage R4)) (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) (Two (Stage R5)) := by
  refine stage_step (hP.mono (fun _ _ h => two_stage (fun p minv => (⟨⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    wsWords p.pl, p.dpp, p.pl⟩, offQ32 p.w p.pl, wsWords p.ql, p.qip⟩ : PPhasePub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => WP.mono (pPart_ok W M S h.toCrtPre h.wide hv hr rfl) fun _ h' =>
      ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h.toCrtPre hv
  obtain ⟨hMk', hP', -⟩ := mask_facts (Mk := p.mask xb pb qb qib) rfl hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_arith
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_arith
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_arith
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega_arith
  have hh : ∀ i < 32, hFixed i = true → word t.mem p.B (8 * i) = word σ.mem p.B (8 * i) := hr.hfix
  refine ⟨minv, hr.nv, ?_⟩
  refine ⟨?_,?_⟩
  swap
  · change offP p.w + slot (wsWords p.pl) 8 + tabBytes32 (wsWords p.pl) ≤ p.Z
    unfold offQ32 at hZq
    dsimp only [CrtPub.w]
    unfold offP
    omega_arith
  unfold PPre
  dsimp only [CrtPub.w]
  refine ⟨mp, mq, _, _, dpb, qib, p.mask xb pb qb qib, hr.good, by omega_arith,
    by omega_arith, show slot ((p.k + 7) / 8) 8 ≤ offP ((p.k + 7) / 8) from Nat.le_refl _, by unfold offQ32 offP; omega_arith, by omega_arith, hwp2,
    wsWords_le (by omega_arith) (by omega_arith), by unfold wsWords; omega_arith,
    wsWords_le (by omega_arith) (by omega_arith), hr.wsP, hr.pws, hr.wsQ, hr.qws, hr.nv, hodd, hN1, hr.xm,
    hr.pxv, hP'.1, hP'.2, hr.pmask, fun hm => ?_, by rw [hh _ (by decide) (by decide)]; exact h.hDp,
    by rw [hh _ (by decide) (by decide), h.dpl]; exact h.hPl, h.dpl, by rw [h.dpl]; omega_arith, by rw [h.dpl]; omega_arith,
    h.dp.congrK hr.iscr hr.keep, by rw [hh _ (by decide) (by decide)]; exact h.hQi, by rw [h.qil, h.dpl],
    h.qi.congrK hr.iscr hr.keep, by rw [h.qil]; unfold wsWords; omega_arith, fun hm => ?_⟩
  · obtain ⟨_, hpq, _⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact ⟨_, hpq.symm⟩
  · obtain ⟨_, _, hqi⟩ := hMk' hm; simp only [hm, ↓reduceIte]; exact hqi

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem crtMain_ct (W : Window) (M : Mont) (S : Selector) (hN : RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) fun _ _ => True)
    {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop}
    (hS : SetupCT) (hC : ChecksCTOf C) (hok : ChecksOk C G) (hQ : QPhaseCT W M S) (hP : PPhaseCT W M S)
    (hF : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True) :
    RelCT isa (Two (Stage (RG G R0))) (VG.Impl.Rsa.AArch64.WindowFive.mainWith C W.code S.code M.mm) fun _ _ => True := by
  rw [crtMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) hok.ne
      (RelCT.seq (R := Two (Stage (RG G R2))) ?_ (checksS_ct hC hok))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.primesSetup])
      (RelCT.seq (R := Two (Stage (RG G R1))) ?_ (setupS_ct G hS))
    exact stage_step (two_map id (fun _ _ h => stage_forget h) hN) fun p σ xb _ _ _ _ _ t h hv ⟨hg, ht⟩ => by
      subst ht; exact WP.mono (nPart_ok M h.toCrtPre hv) fun _ ⟨minv, hr⟩ => ⟨hg, minv, hr⟩
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (RelCT.seq (qS_ct W M S hQ) ?_)
  exact RelCT.seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (by simp [finish]) (RelCT.seq (pS_ct W M S hP) hF)

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-!
# RSA with the CRT on AArch64: the result in constant time

`finish` sums `m_q + q h` into the modulus' accumulators (`finishSum`), whose
parts keep the header and the primes' workspaces (`FA`), and stores it masked
(`outArr_ct`): `crtFinish_ct`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32)

/-- `finishSum`'s hypotheses after `p`'s phase. -/
theorem stage5_fa {p : CrtPub} {t : State} (h : Stage R5 p t) :
    FA ⟨p.B, p.Z, p.w, offP p.w, offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ t := by
  unfold CrtPub.w
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_using []
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_using []
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega_using []
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega_using []
  have hwq := wsWords_le (len := p.ql) (w := (p.k + 7) / 8) (by omega_using [hql2]) (by omega_using [hk1])
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ32 at hZq; omega_using [hZq]
  unfold FA RowsPre
  dsimp only
  exact ⟨⟨minv, hr.good, hZ⟩, ⟨hr.good.scr, hr.good.x0, hr.good.hdr.harr aAcc (by decide), hr.wsP, hr.wsQ,
      by rw [← word_off]; exact hr.pws.hdr.hw, by rw [← word_off]; exact hr.qws.hdr.hw,
      by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off],
      by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by decide, Nat.le_refl _,
      by unfold offQ32 offP; omega_using [], by omega_using [hZq]⟩,
    by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by omega_using [hwq2], hwq, by omega_using [hk2]⟩

/-- `finishSum` leaves what the store needs. -/
theorem finSum_out {p : CrtPub} {t₂ : State} (h : Stage R5 p t₂) :
    WP isa (seqs finishSum) t₂ (OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩) := by
  have hfa := stage5_fa h
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := hfa
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hpl1 := h.pl1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega_using []
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega_using []
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega_using []
  have hwp := wsWords_le (len := p.pl) (w := (p.k + 7) / 8) (by omega_using [hpl2]) (by omega_using [hk1])
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ32 at hZq; omega_using [hZq]
  refine WP.mono (finishSum_ok hr.good (by unfold CrtPub.w at hw; omega) hr.wsP hr.wsQ
    (by rw [← word_off]; exact hr.pws.hdr.hw) (by rw [← word_off]; exact hr.qws.hdr.hw)
    (by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off]) (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off]) (Nat.le_refl _) (by unfold offQ32 offP; omega_using [ewp]) (by dsimp only [CrtPub.w]; omega_using [hZq, ewq])
    (by omega_using [hwp2]) hwp (by omega_using [hwq]) hwq') fun t₃ ⟨_, ho₃, k₃⟩ => ?_
  have hacc := accs_le ((p.k + 7) / 8)
  have hb₃ : ∀ i < 32, word t₃.mem p.B (8 * i) = word t₂.mem p.B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((p.k + 7) / 8) Public.aAcc hi; omega)) (by omega_using [hi])
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem p.B (8 * i) = word σ.mem p.B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have k03 := hr.keep.trans k₃
  unfold OPreW
  dsimp only
  exact ⟨minv, p.mask xb pb qb qib, ⟨hr.good.scr.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans hr.good.x0,
      ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
        fun j hj => (hb₃ _ (by unfold sArr; omega_using [hj])).trans (hr.good.hdr.harr j hj)⟩⟩, rfl, hZ, by omega_using [hk1],
    by omega_using [hk2], by rw [hfx _ (by decide) (by decide)]; exact h.hO, by rw [hfx _ (by decide) (by decide)]; exact h.hK,
    by rw [hb₃ _ (by decide)]; exact hr.msk, fun j hj => by rw [k03.wr]; exact h.out j hj, h.outSep⟩

/-- `finish` leaks the same in runs that agree on the public data. -/
theorem crtFinish_ct : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True := by
  rw [finish_out]
  refine RelCT.seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr])
    (RelCT.seq (R := Two OPreW) ?_ (outArr_ct (j := Public.aAcc) (by decide) (by taint_decide)))
  refine (two_post (Ψ := fun (p : CrtPub) t => OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩ t)
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offP p.w, offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : RowsPub))
      (fun _ _ h => stage5_fa h) finSum_ct) fun p t h => finSum_out h).mono (fun _ _ h => h)
    fun _ _ h => two_bind (fun (p : CrtPub) _ _ h₁ h₂ => ⟨(⟨p.B, p.Z, p.w, p.k, p.op⟩ : OPubW), h₁, h₂⟩) h

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Complete constant-time composition of the wider-window CRT computation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

theorem nSetup_ct (M : Mont) :
    RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) (fun _ _ => True) :=
  two_map id (fun _ _ ⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,hr⟩ =>
    ⟨σ,xb,pb,qb,dpb,dqb,qib,h.toCrtPre,hv,hr⟩) (VG.Proof.Bignum.AArch64.nSetup_ct M)

theorem main_ct (W : Window) (M : Mont) (S : Selector) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop}
    (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    RelCT isa (Two (Stage (RG G R0)))
      (VG.Impl.Rsa.AArch64.WindowFive.mainWith C W.code S.code M.mm) (fun _ _ => True) :=
  crtMain_ct W M S (nSetup_ct M) setup_ct hC hok
    (qPhase_ct W M S (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct W M S (redc_ct_Y M) (expLoop_ct W M S (by taint_decide)) (by taint_decide)))
    (pPhase_ct W M S (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct W M S (redc_ct_Y M) (expLoop_ct W M S (by taint_decide)) (by taint_decide))
      (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

end VG.Proof.Bignum.AArch64.WindowFive

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (eval_zero)

abbrev OldStage (G : Nat → Nat → Nat → Prop) :=
  VG.Proof.Bignum.AArch64.Stage (VG.Proof.Bignum.AArch64.RG G VG.Proof.Bignum.AArch64.R0)

theorem baselineMain_ct (M : Mont) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksCTOf C)
    (hok : ChecksOk C G) : RelCT isa (Two (OldStage G)) (VG.Impl.Rsa.AArch64.Crt.mainWith C M.mm)
    (fun _ _ => True) :=
  VG.Proof.Bignum.AArch64.crtMain_ct M (VG.Proof.Bignum.AArch64.nSetup_ct M)
    VG.Proof.Bignum.AArch64.setup_ct hC hok
    (VG.Proof.Bignum.AArch64.qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (VG.Proof.Bignum.AArch64.pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (VG.Proof.Bignum.AArch64.pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (VG.Proof.Bignum.AArch64.pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide))
      (redc_ct_X M) loadArr_ct_pI)
    VG.Proof.Bignum.AArch64.crtFinish_ct

def GuardPost (G : Nat → Nat → Nat → Prop) (p : CrtPub) (s : State) : Prop :=
  OldStage G p s ∧ s.gpr .x9 = guardValue p.k p.pl p.ql

theorem guard_post {G : Nat → Nat → Nat → Prop} {p : CrtPub} {s : State} (h : OldStage G p s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.lengthGuard) s (GuardPost G p) := by
  obtain ⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,hg,rfl⟩ := h
  exact WP.mono (lengthGuard_ok h) fun t ⟨h9,hm,kk⟩ =>
    ⟨⟨t,xb,pb,qb,dpb,dqb,qib,pre_keep h hm kk,hv,hg,rfl⟩,h9⟩

theorem guarded_wide {G : Nat → Nat → Nat → Prop} {p : CrtPub} {s : State}
    (h : GuardPost G p s ∧ isa.eval (.zero .x .x9) s = some false) : Stage (RG G R0) p s := by
  obtain ⟨⟨⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,hg,rfl⟩,h9⟩,he⟩ := h
  have hk64 : p.k < 2 ^ 64 := by have := h.k2; omega_using [this]
  rw [eval_zero,h9] at he
  have hk128 : 128 ≤ p.k := guardValue_nonzero hk64 (Option.some.inj he)
  have hwide : CrtWindowFive.offQ32 p.w p.pl + slot (wsWords p.ql) 8 + CrtWindowFive.tabBytes32 (wsWords p.ql) ≤ p.Z :=
    Nat.le_trans (CrtWindowFive.prime_scratch32_fits hk128 h.pl2 h.ql2) (by have := h.zk; omega_using [this])
  exact ⟨s,xb,pb,qb,dpb,dqb,qib,⟨h,hwide⟩,hv,hg,rfl⟩

theorem dispatch_ct (W : Window) (M : Mont) (S : Selector) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop}
    (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    RelCT isa (Two (OldStage G)) (VG.Impl.Rsa.AArch64.WindowFive.dispatchWith C W.code S.code M.mm)
      (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.dispatchWith
  refine RelCT.seq (two_piece (Ψ := GuardPost G) [.x0]
    (pins_x0B CrtPub.B fun _ _ ⟨_,_,_,_,_,_,_,h,_,_,rfl⟩ => h.x0)
    (by taint_decide) fun _ _ h => guard_post h) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero,eval_zero,h₁.2,h₂.2]) ?_ ?_
  · exact two_map id (fun _ _ h => h.1.1) (baselineMain_ct M hC hok)
  · exact two_map id (fun _ _ h => guarded_wide h) (main_ct W M S hC hok)

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-!
# `vg_rsa_private_crt` on AArch64: constant time

`entry` and the modulus' check leak the same in runs that agree on the
public data (the arguments but the input and the key's values, and `n`),
and so do `fail` and `main` (`crtMain_ct`): `crtCode_ct`, and the contract's
`ConstantTime` (`crtCode_constantTime_of`), given that `n`'s setup is
constant time.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Rsa.AArch64 (crtA stackArgs_ten)

/-- `vg_rsa_private_crt` with the key checks `C` leaks the same in runs that
agree on the public data, for keys with `G`. -/
theorem crtCode_ct (W : Window) (M : Mont) (S : Selector) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop}
    (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    RelCT isa (Two (CCRel G)) (VG.Impl.Rsa.AArch64.WindowFive.codeWith C W.code S.code M.mm) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.codeWith
  refine RelCT.seq (R := Two (CC3 G)) ?_ ?_
  · rw [head_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1 G) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
      · rw [h₁.x3, h₂.x3]) (by taint_decide) ?_)
      (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]
        · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := crtCtx_of hs.1
    have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ (entry.drop 1 ++ invalid))) s (HeadPost s) := by
      rw [← head_split]; exact crtHeadChk_ok c
    have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
    have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
    have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
    refine WP.mono (wp_and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
      (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
        ⟨s, hs, h8.trans hs.2.2.1, (k.gpr .x2 (by decide)).trans hs.2.2.2.2.2.2.1,
          (k.gpr .x3 (by decide)).trans hs.x3, hw⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, cc3_x9 h₁, cc3_x9 h₂]) ?_ ?_
  · -- `fail`.
    unfold Precomputed.fail
    have pin : ∀ p t, (CC3 G p t ∧ isa.eval (.zero .x .x9) t = some true) → t.gpr .x0 = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre, -⟩ := cc3_pre h
      exact hpre.x0
    refine RelCT.seq (two_piece (Ψ := fun (p : CCPub) t => t.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.m.k ∧ t.gpr .x0 = p.m.B) [.x0]
      (pins_x0B (fun p : CCPub => p.m.B) pin) (by taint_decide) ?_)
      (two_taint [.x1, .x2, .x0] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre, -⟩ := cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega_using [hZq, h8]
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega_using [hZ, hi])
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.m.op + BitVec.ofNat 64 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 p.m.k) (by
      brun [hpre.x0, hdr_enc (show Public.sOut < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sOut (by decide), hl Public.sK (by decide), hpre.hO, hpre.hK]) (by decide) (by decide)
      (by decide +kernel))
      fun t' ⟨⟨h1, h2⟩, k'⟩ => ⟨h1, h2, (k'.gpr .x0 (by decide)).trans hpre.x0⟩
  · -- `main`.
    have toM : ∀ p t, CC3 G p t ∧ isa.eval (.zero .x .x9) t = some false → OldStage G p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre, hg⟩ := cc3_pre h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        rw [eval_zero, cc3_x9 h] at he
        revert he
        cases Spec.Rsa.modulusValid p.m.N p.m.k <;> decide
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, hg, rfl⟩
    exact (dispatch_ct W M S hC hok).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- The key of a state has `G`. -/
def KeyG (G : Nat → Nat → Nat → Prop) (s : State) : Prop :=
  G (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))

/-- `vg_rsa_private_crt` with the key checks `C` is constant time for keys
with `G`. -/
theorem crtCodeWith_constantTime (W : Window) (M : Mont) (S : Selector) {C : List (Prog isa)}
    {G : Nat → Nat → Nat → Prop} (hC : ChecksCTOf C) (hok : ChecksOk C G) :
    ConstantTime isa (fun s => crtA.pre s ∧ KeyG G s) crtA.pub
      (VG.Impl.Rsa.AArch64.WindowFive.codeWith C W.code S.code M.mm) := by
  refine RelCT.constantTime ((crtCode_ct W M S hC hok).mono
    (fun s₁ s₂ ⟨⟨h₁, g₁⟩, ⟨h₂, g₂⟩, hp⟩ => ⟨ccPubOf s₁, ?_, ?_, hp.2.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, g₁⟩
  · obtain ⟨hr, hsp, ha, hn⟩ := hp
    simp only [stackArgs_ten, List.cons.injEq, and_true] at ha
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
    have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, hsp.symm, a8.symm, by rw [← a9]; rfl, by rw [r .x3 (by decide)]; rfl, r .x0 (by decide), r .x2 (by decide),
      r .x4 (by decide), r .x6 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, by rw [r .x7 (by decide)]; rfl,
      by rw [← a1]; rfl, hn.symm, g₂⟩

/-- `vg_rsa_private_crt` is constant time, given that `main`'s parts are. -/
theorem crtCode_constantTime_of (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa crtA.pre crtA.pub (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm) :=
  fun _ _ _ _ _ _ h₁ h₂ => crtCodeWith_constantTime W M S checks_ct checks_okG _ _ _ _ _ _ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩


end VG.Proof.Bignum.AArch64.WindowFive
