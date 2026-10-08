import VerifiedGarbage.Proof.Cast5.AArch64.Ecb
import VerifiedGarbage.Proof.Cast5.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# CAST5 ECB on AArch64: verified against the shared contracts
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The contract the proofs of the ECB functions are written against. -/
def ecbX (d : Spec.Cast5.Direction) : Contract isa where
  pre s := EPre s
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat d
        (Spec.Cast5.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

/-- The registers the ECB functions write. -/
def ecbRegs : List Reg := blockRegs ++ [.x2, .x3]

theorem preserved_ecbRegs : ∀ r ∈ preserved, r ∉ ecbRegs := by decide

theorem ecb_correct (d : Spec.Cast5.Direction) {blk : Prog isa}
    {f : Spec.Cast5.Schedule → Nat → Spec.Cast5.Block → Spec.Cast5.Block}
    (hblk : ∀ u k n, BPre u k n → WP isa blk u (BPost u (f k n (Spec.Cast5.blockAt u.mem (u.gpr .x2)))))
    (hf : ∀ k n xs, Spec.Cast5.ecb k n d xs = xs.map (f k n))
    (hw : writesOnly ecbRegs (ecb blk) = true) (hn : (ecb blk).noCalls = true)
    (hv : (ecb blk).allInstrs keepsV = true) (s : State) (h : (ecbX d).pre s) :
    ∃ t s', Exec isa (ecb blk) s t s' ∧ abiPreserved s s' ∧ (ecbX d).post s s' := by
  obtain ⟨t, s', he, hpost, hk⟩ := WP.keep ecbRegs (ecb_ok hblk s h) hw hn hv
  exact ⟨t, s', he, ⟨fun r hr => hk.gpr r (preserved_ecbRegs r hr), hk.sp, hk.vcs⟩,
    by show _ = _; rw [hpost, hf]⟩

/-- The public registers. -/
def ecbPub : List Reg := [.x0, .x1, .x2, .x3, .x4]

theorem ecb_agree (d : Spec.Cast5.Direction) (s₁ s₂ : State) (_ : (ecbX d).pre s₁) (_ : (ecbX d).pre s₂)
    (h : (ecbX d).pub s₁ s₂) : VG.AArch64.Taint.AgreeS [s1234Sym] (Taint.ofRegs ecbPub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp, hsy⟩ := h
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · have hr := Taint.mem_ofRegs.mp hr
    simp only [ecbPub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem ecbEncrypt_ct : ConstantTime isa (ecbX .encrypt).pre (ecbX .encrypt).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs ecbPub) (ecb_agree .encrypt)
    (by taint_decide)

theorem ecbDecrypt_ct : ConstantTime isa (ecbX .decrypt).pre (ecbX .decrypt).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs ecbPub) (ecb_agree .decrypt)
    (by taint_decide)

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the contracts' witness: the table at `0x100000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := constMem 0x100000 s1234

theorem ecbSatMem_held : ∀ i < 512,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  unfold ecbSatMem
  intro i hi
  exact constMem_held _ _ (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi)

/-- A state satisfying the ECB functions' precondition: 16 rounds, one block. -/
def ecbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem EPre.spec_pre (d : Spec.Cast5.Direction) {s : State} (h : EPre s) :
    (Spec.Cast5.ecbContract (AArch64.abi.withConsts ecbConsts) d).pre s := by
  sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, AArch64.abi, AArch64.argRegs,
    ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  refine ⟨by rw [h.rd]; rfl, h.held, h.fitT, fun r hr => ?_, by rw [h.rd]; rfl, h.wr, h.dKD, h.dKS,
    h.dDS, h.fK, h.fD, h.fS, h.rounds⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTD
  · exact h.dTS

theorem ecb_implies (d : Spec.Cast5.Direction) :
    (ecbX d).Implies (Spec.Cast5.ecbContract (AArch64.abi.withConsts ecbConsts) d) where
  pre s h := by
    sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, AArch64.abi, AArch64.argRegs,
      ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length] at h
    obtain ⟨hdr, hheld, hfit, hdw, htk, hw, dKD, dKS, dDS, fK, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dKD, dKS, dDS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ h := by
    sig_post [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPost, AArch64.abi, AArch64.argRegs,
      ecbConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, AArch64.abi, AArch64.argRegs, ecbConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h2, h3, h4, h5, hsp, hsy⟩
  sat := ⟨ecbSat, EPre.spec_pre d ⟨rfl, rfl, ecbSatMem_held, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩⟩

theorem ecbEncrypt_verified :
    Verified AArch64.target ecbEncrypt (Spec.Cast5.ecbEncryptContract (AArch64.abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_correct .encrypt (fun _ _ _ h => encryptBlock_ok h) (fun _ _ _ => rfl)
    (by lit_decide) (by lit_decide) (by lit_decide)) ecbEncrypt_ct (ecb_implies .encrypt)

theorem ecbDecrypt_verified :
    Verified AArch64.target ecbDecrypt (Spec.Cast5.ecbDecryptContract (AArch64.abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_correct .decrypt (fun _ _ _ h => decryptBlock_ok h) (fun _ _ _ => rfl)
    (by lit_decide) (by lit_decide) (by lit_decide)) ecbDecrypt_ct (ecb_implies .decrypt)

end VG.Proof.Cast5.AArch64
