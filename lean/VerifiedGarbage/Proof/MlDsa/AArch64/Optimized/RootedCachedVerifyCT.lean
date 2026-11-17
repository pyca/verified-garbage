module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

/-! ### `MlDsa.AArch64.Message.OptimizedRel`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message

abbrev MovedS (as : List (Reg × Arg)) (t u : State) : Prop := Moved as t u ∧ u.syms=t.syms

variable {I : Lay → Mem → Mem → Prop}
theorem call_tr {Φ : Lay → Mem → State → Prop} {as : List (Reg × Arg)} (hok : argsOk as = true) {n : String}
    {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hnd : c.all (fun i => !i.touchesDit) = true)
    (hpd : ∀ s d, k.pre s → k.pre (s.withDit d)) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g v m₀ (t t1 : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t → MovedS as t t1 →
      k.pre (t1.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b a1 b1 : State), L.Ok → I L m₁ m₂ → Ctx L g₁ v₁ m₁ a →
      Ctx L g₂ v₂ m₂ b → Φ L m₁ a → Φ L m₂ b → MovedS as a a1 → MovedS as b b1 →
      k.ditFree.pub (a1.callEntry.withRegions (rd L) (wr L)) (b1.callEntry.withRegions (rd L) (wr L)))
    (hcov : ∀ (L : Lay) g v m₀ (t : State), L.Ok → Ctx L g v m₀ t → Φ L m₀ t →
      Covers (rd L++wr L) (L.rd++L.wr) ∧ Covers (wr L) L.wr) :
    RelCT isa (Two I Φ) (callA n c as) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun a1 b1 => ∃ a b, Two I Φ a b ∧ MovedS as a a1 ∧ MovedS as b b1)
    (block_x28_tr (setArgs_xOnly hok) fun _ _ h => h.x28)
    (fun x y ⟨L, _, _, _, _, _, _, hL, _, c₁, c₂, _, _⟩ =>
      ⟨WP.mono_syms (setArgs_ok as hok x (c₁.xOk hL)) (fun _ h hy=>⟨h,hy⟩),
        WP.mono_syms (setArgs_ok as hok y (c₂.xOk hL)) (fun _ h hy=>⟨h,hy⟩)⟩)
    fun x y x1 y1 hp f₁ f₂ => ⟨x, y, hp, f₁, f₂⟩) ?_
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ a b, (∃ (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
      (m₁ m₂ : Mem), L.Ok ∧ I L m₁ m₂ ∧ Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ Φ L m₁ a ∧ Φ L m₂ b) ∧
      MovedS as a a1 ∧ MovedS as b b1)
    (RelCT.exists_ fun L => RelCT.callDit hv hct hnd hpd (rd L) (wr L) fun a1 b1 ⟨a, b, hp, f₁, f₂⟩ => ?_)
    (fun a1 b1 ⟨a, b, ⟨L, hp⟩, f₁, f₂⟩ => ⟨L, a, b, hp, f₁, f₂⟩) fun _ _ h => h
  obtain ⟨g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := hp
  obtain ⟨hr, hw⟩ := hcov L g₁ v₁ m₁ a hL c₁ φ₁
  have cov : ∀ {t t1 : State} {g v m₀}, Ctx L g v m₀ t → MovedS as t t1 →
      Covers (rd L ++ wr L) (t1.rd ++ t1.wr) ∧ Covers (wr L) t1.wr := fun hc f => by
    rw [f.1.2.rd, f.1.2.wr, hc.rd, hc.wr]
    exact ⟨hr,hw⟩
  exact ⟨hpre L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁, hpre L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂,
    hpub L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂, (cov c₁ f₁).1, (cov c₁ f₁).2,
    (cov c₂ f₂).1, (cov c₂ f₂).2⟩

end VG.Proof.MlDsa.AArch64.Message.Optimized

end

end

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
