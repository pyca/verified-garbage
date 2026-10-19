module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries

import VerifiedGarbage.Proof.Dsa.X86_64.SmallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SmallCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointTableInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointTableInit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa

/-! # Constant-time construction of the joint power table -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def JointBuildPre (j : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (n g y : Nat), JointCtx s (off p.B p.o) p.wx n minv ∧
    JointBuildValues s.mem (off p.B p.o) p.wx n g y j ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ 0 < n ∧ Nat.Coprime (2 ^ (64 * p.wx)) n

theorem JointBuildPre.goodW {j : Nat} {p : XPub} {s : State} (h : JointBuildPre j p s) : GoodW p.ws s :=
  let ⟨minv, _, _, _, hc, _⟩ := h; ⟨minv, hc.mod.good, Nat.le_refl _⟩

theorem jointAdvance_ct (M : Mont) (j : Nat) :
    RelCT isa (Two (JointBuildPre j)) (Joint.advance M.mm j) (fun _ _ => True) := by
  unfold Joint.advance
  split
  · refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.ws s)
      (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW) (M.ct (by unfold MmUse; decide))) ?_)
      (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
        (copyArr_ct (o := aY) (a := aX) (by decide) (by decide) (by taint_decide)))
    rintro p s ⟨minv, n, g, y, hc, hv, hw, hw', hn, hR⟩
    exact WP.mono (jointProduct_ok M hc hw hw' (by unfold MmUse; decide)
      (by rw [hv.gen]; exact Nat.mod_lt _ hn)) fun t ⟨ht, _⟩ => ⟨minv, ht.mod.good, Nat.le_refl _⟩
  · exact two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW) (M.ct (by unfold MmUse; decide))

def JointBuildCTInv (j : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (n g y : Nat), JointBuildInv t₀ (off p.B p.o) p.wx n g y minv j s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ 0 < n ∧ Nat.Coprime (2 ^ (64 * p.wx)) n

theorem jointBuildStep_ct (M : Mont) (j : Nat) (hj : j < 16) :
    RelCT isa (Two (JointBuildCTInv j)) (Joint.buildStep M.mm j) (fun _ _ => True) := by
  unfold Joint.buildStep
  refine RelCT.seq (two_post (Ψ := JointBuildPre j) ?_ ?_) (jointAdvance_ct M j)
  · refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.B p.o)
      (two_map (fun p : XPub => (p, j)) ?_ (toEnt_ct (n := 16) (a := aY) (by taint_decide))) ?_) ?_
    · rintro p s ⟨t₀, minv, n, g, y, hI, hw, hw', hn, hR⟩
      exact ⟨⟨minv, n, _, hI.ctx.exp, by rw [hI.vals.gen]; exact Nat.mod_lt _ hn, hw, hw'⟩,
        hI.ent, hj, by decide⟩
    · rintro p s ⟨t₀, minv, n, g, y, hI, hw, hw', hn, hR⟩
      exact WP.mono (toEnt_ok hI.ctx.exp hw hw' (by decide) hj hI.ent)
        fun t ⟨_, _, hk⟩ => (hk.gpr (by decide)).trans hI.ctx.mod.good.rdi
    · exact rdi_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide)
  · rintro p s ⟨t₀, minv, n, g, y, hI, hw, hw', hn, hR⟩
    refine WP.mono (jointStore_ok hI.ctx hw hw' hj hI.ent) fun t ⟨ht, harr, _, _, _, _, _, _⟩ => ?_
    exact ⟨minv, n, g, y, ht, hI.vals.congr harr, hw, hw', hn, hR⟩

theorem jointBuildSteps_ct (M : Mont) (j count : Nat) (hcount : j + count ≤ 16) :
    RelCT isa (Two (JointBuildCTInv j)) (Joint.buildSteps M.mm j count) (fun _ _ => True) := by
  induction count generalizing j with
  | zero =>
    exact rdi_ct (fun p : XPub => off p.B p.o)
      (fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.mod.good.rdi) (by simp only [Joint.buildSteps]; taint_decide)
  | succ count ih =>
    unfold Joint.buildSteps
    refine RelCT.seq (two_post (Ψ := JointBuildCTInv (j + 1)) (jointBuildStep_ct M j (by omega)) ?_)
      (ih (j + 1) (by omega))
    rintro p s ⟨t₀, minv, n, g, y, hI, hw, hw', hn, hR⟩
    exact WP.mono (jointBuildStep_ok M hw hw' hn hR (by omega) hI)
      fun t ht => ⟨t₀, minv, n, g, y, ht, hw, hw', hn, hR⟩

theorem jointBuild_ct (M : Mont) :
    RelCT isa (Two (JointBuildPre 0)) (Joint.build M.mm) (fun _ _ => True) := by
  unfold Joint.build seqs
  refine RelCT.seq (two_post (Ψ := JointBuildCTInv 0)
    (rdi_ct (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.mod.good.rdi)
      (by unfold Joint.tableInit; taint_decide)) ?_) ?_
  · rintro p s ⟨minv, n, g, y, hc, hv, hw, hw', hn, hR⟩
    exact WP.mono (jointTableInit_ok hc hv)
      fun t ht => ⟨t, minv, n, g, y, ht, hw, hw', hn, hR⟩
  refine RelCT.seq (two_post (Ψ := JointBuildPre 16) (jointBuildSteps_ct M 0 16 (by decide)) ?_) ?_
  · rintro p s ⟨t₀, minv, n, g, y, hI, hw, hw', hn, hR⟩
    exact WP.mono (jointBuildSteps_ok M hw hw' hn hR (by decide) hI)
      fun t ht => ⟨minv, n, g, y, ht.ctx, ht.vals, hw, hw', hn, hR⟩
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.ws s)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW)
      (copyArr_ct (o := aY) (a := aOne) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · rintro p s ⟨minv, n, g, y, hc, hv, hw, hw', hn, hR⟩
    exact WP.mono (jointCopy_ok hc hw hw' (by decide) (by decide) (by decide) (by decide))
      fun t ⟨ht, _⟩ => ⟨minv, ht.mod.good, Nat.le_refl _⟩
  exact two_map (fun p : XPub => p.ws) (fun _ _ h => h)
    (smallW_ct (a := aOne) (by decide) (by taint_decide))

end VG.Proof.Dsa.X86_64
