import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyRel

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
variable {p : Params}

/-- The cached digest is readable and survives the hashing workspace. -/
structure TrSide (L : VG.Proof.MlDsa.AArch64.Message.Lay) : Prop where
  read : ∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R
  x : L.XS.Disjoint ⟨L.rnd, 64⟩
  stack : L.STK.Disjoint ⟨L.rnd, 64⟩

theorem VOk.trSide {L : VG.Proof.MlDsa.AArch64.Message.Lay} {m : Mem} (h : VOk p L m) : TrSide L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨⟨⟨σ.gpr .x7, 64⟩, by simp [cachedLay, hσ.rd], within_self _⟩,
    hσ.trScr.symm.sub_left (cachedLay_X p σ).sub, hσ.stkTr⟩

theorem TrSide.parts {L : VG.Proof.MlDsa.AArch64.Message.Lay} (h : TrSide L) :
    (∃ R ∈ L.rd ++ L.wr, Within ⟨L.rnd, 64⟩ R) ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.ST, 200⟩ ∧
    Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.KS, 640⟩ ∧ L.STK.Disjoint ⟨L.rnd, 64⟩ :=
  ⟨h.read, h.x.symm.sub_right (Region.sub_prefix (by decide)),
    h.x.symm.sub_right (within_off L.X (d := 200) (n := 640) (k := 1024) (by omega)).sub, h.stack⟩

theorem cachedTr_val {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m} {t : State} (h : Ctx L g vv m t) :
    (VG.Impl.MlDsa.AArch64.Message.Arg.slot fRnd).val t = L.rnd := by
  rw [h.slotV (f := fRnd) (j := 5) rfl (by omega)]
  rfl

theorem VOk.digest {L : VG.Proof.MlDsa.AArch64.Message.Lay} {g vv m} {t : State}
    (h : VOk p L m) (hc : Ctx L g vv m t) : bytesAt t.mem L.rnd 64 = H (bytesAt m L.key p.pkLen) 64 := by
  rw [hc.bytesAt_eq h.trSide.x h.trSide.stack (by decide)]
  obtain ⟨σ, hσ, _, rfl, rfl⟩ := h
  exact hσ.digest

/-- Reusing the digest retains the public-input-only leakage contract. -/
theorem cachedMu_tr (v : Proof.Sha3.AArch64.Permutation) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p L m) (muHash v.callee (.slot fRnd))
      (Two (verifyI p) fun L m t => VOk p L m ∧ VMuOk p L m t) := by
  have mh := muHash_tr_of v (I := verifyI p) (Φ := fun L m _ => VOk p L m) (G := TrSide)
    (tr := .slot fRnd) (by decide) rfl (fun L => L.rnd)
    (fun _ _ _ _ _ hc => cachedTr_val hc) (fun _ _ h => h.parts)
  have mh' : RelCT isa (Two (verifyI p) fun L m _ => VOk p L m) (muHash v.callee (.slot fRnd))
      (fun _ _ => True) := RelCT.mono mh (fun _ _ h => by
        obtain ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩ := h
        exact ⟨L, g₁, g₂, v₁, v₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁.trSide, φ₁⟩, ⟨φ₂.trSide, φ₂⟩⟩)
        (fun _ _ _ => trivial)
  exact two_wp mh' fun L g vv m t hL hc hφ => by
    obtain ⟨a, b, c, d⟩ := hφ.trSide.parts
    refine WP.mono (muHash_ok v hL hc (tr := .slot fRnd) (by decide) rfl
      (fun _ hc' => cachedTr_val hc') a b c d) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
    unfold VMuOk
    rw [hμ, hφ.digest hc]

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
