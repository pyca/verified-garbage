module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre

/-! ### `MlDsa.AArch64.Message.OptimizedCallTiming`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)

abbrev rootsAt (s : State) : Addr × Addr :=
  (s.syms "VG_MLDSA_NTT_EXPANDED",s.syms "VG_MLDSA_INV_FOLDED")
abbrev rootPairRegions (tab : Addr × Addr) : List Region := [⟨tab.1,3904⟩,⟨tab.2,3904⟩]
theorem rootsAt_syms {s t : State} (h : t.syms=s.syms) : rootsAt t=rootsAt s := by simp only [rootsAt,h]

variable {p : Params}
end VG.Proof.MlDsa.AArch64.Message.Optimized

end

end

/-! ## From `RootedCachedVerifyRel.lean` -/

@[expose] public section

/-! ## From `RootedCachedVerifyHash.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots)
open Message.Optimized (rootsAt rootsAt_syms)
variable {p : Params}

/-- The cached digest is readable and survives the hashing workspace. -/
structure TrSide (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  read : ∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R
  x : L.XS.Disjoint ⟨L.rnd, 64⟩
  stack : L.STK.Disjoint ⟨L.rnd, 64⟩

theorem TrSide.parts {L : VG.Proof.MlDsa.AArch64.Message.Lay} (h : TrSide L) :
    (∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R) ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.ST, 200⟩ ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.KS, 640⟩ ∧ L.STK.Disjoint ⟨L.rnd, 64⟩ :=
  ⟨h.read, h.x.symm.sub_right (Region.sub_prefix (by decide)),
    h.x.symm.sub_right (within_off L.X (d := 200) (n := 640) (k := 1024) (by omega_using [])).sub, h.stack⟩

theorem cachedTr_val {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m} {t : State} (h : Ctx L g vv m t) :
    (VG.Impl.MlDsa.AArch64.Message.Arg.slot fRnd).val t = L.rnd := by
  rw [h.slotV (f := fRnd) (j := 5) rfl (by omega_using [])]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify

end

/-! ## From `RootedCachedVerifyBodyTiming.lean` -/

/-! ## From `RootedCachedVerifyCT.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open Message.Optimized (rootRegions rootsAt rootsAt_syms)
variable {p : Params}

theorem enterV_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x6]) (.block (enter .x6 p cachedVerifySaves)) (.block [])).isSome=true := rfl

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify

end
