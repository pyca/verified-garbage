import VerifiedGarbage.Proof.Blowfish.AArch64.KeyMain
import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem initConsts_eq : initConsts = [(initSym, Impl.Blowfish.initWords)] := rfl

theorem initWords_length : Impl.Blowfish.initWords.length = 521 := by simp [Impl.Blowfish.initWords]

/-- Key expansion's contract as the code sees it. -/
def keyC : Contract isa where
  pre s := KeyPre s
  post s s' := scheduleAt s'.mem (s.gpr .x2) =
    Spec.Blowfish.expandKey (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := PublicRegs [.x0, .x1, .x2] s₁ s₂ ∧ s₁.syms initSym = s₂.syms initSym

theorem expandKey_ok (s : State) (hs : keyC.pre s) :
    ∃ t s', Exec isa Impl.Blowfish.AArch64.expandKey s t s' ∧ abiPreserved s s' ∧ keyC.post s s' := by
  obtain ⟨t, s', he, ⟨hk, hv⟩, hg⟩ := WP.gprs (c := Impl.Blowfish.AArch64.expandKey) (expandKey_correct hs)
    (rs := preserved) (by lit_decide) rfl
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, hv⟩, hk⟩

/-- The memory of the contract's witness: the table at `0x10000` (irreducible: unfolding it in a
definitional check would evaluate the table). -/
@[irreducible] def keySatMem : Mem := constMem 0x10000 Impl.Blowfish.initWords

theorem keySatMem_held : ∀ i < Impl.Blowfish.initWords.length,
    keySatMem.readW (0x10000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [initWords_length]; omega)

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 4 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem := keySatMem
  rd := [⟨0x1000, 4⟩, ⟨0x10000, 4168⟩]
  wr := [⟨0x3000, 4168⟩]
  syms _ := 0x10000

/-- The shared contract's precondition, from its facts. -/
theorem key_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.syms initSym, 4168⟩])
    (hw : s.wr = [⟨s.gpr .x2, 4168⟩])
    (ks : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩)
    (f0 : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64) (f2 : (s.gpr .x2).toNat + 4168 ≤ 2 ^ 64)
    (valid : validKey (s.gpr .x1).toNat)
    (held : ∀ i < Impl.Blowfish.initWords.length,
      s.mem.readW (s.syms initSym + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWords.getD i 0)
    (fitT : (s.syms initSym).toNat + 4168 ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, (⟨s.syms initSym, 4168⟩ : Region).Disjoint r) :
    (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)).pre s := by
  sig_pre [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
    Spec.Blowfish.expandKeyPre, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  rw [initWords_length]
  exact ⟨by rw [hrd]; rfl, fun i hi => held i (by rw [initWords_length]; exact hi), fitT, hdw,
    by rw [hrd]; rfl, hw, ks, f0, f2, valid⟩

theorem expandKey_implies :
    keyC.Implies (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)) where
  pre s h := by
    sig_pre [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      Spec.Blowfish.expandKeyPre, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts,
      Abi.constRegions, Abi.constsHeld, stackBelow] at h
    rw [initWords_length] at h
    obtain ⟨hd, held, fitT, hdw, ht, hw, ks, -, fitS, valid⟩ := h
    have tw : ∀ r ∈ s.wr, (⟨s.syms initSym, 4168⟩ : Region).Disjoint r := hdw
    refine ⟨valid, ?_, hw, ks, fitS, held, fitT, tw _ (by rw [hw]; exact List.mem_cons_self)⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      Spec.Blowfish.expandKeyPost, AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig,
      AArch64.abi, AArch64.argRegs, initConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, hsy⟩
  sat := ⟨keySatState, key_spec_pre rfl rfl (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) keySatMem_held (by decide) (fun r hr => by
      simp only [keySatState, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact Region.disjoint_of_sep (by decide))⟩

theorem expandKey_verified : Verified target Impl.Blowfish.AArch64.expandKey
    (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts initConsts)) :=
  Verified.of_correct expandKey_ok (expandKey_constantTime _) expandKey_implies

end VG.Proof.Blowfish.AArch64
