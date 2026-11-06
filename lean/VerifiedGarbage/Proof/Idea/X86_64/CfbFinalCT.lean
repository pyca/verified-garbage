module

public import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalVerified
public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalCT
import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalLit
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalVerified
meta import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalCT
meta import VerifiedGarbage.Proof.Idea.X86_64.CfbFinalLit
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# IDEA-CFB64 of a message's last piece on x86-64 in constant time

`cfbEncryptFinal_ct`, `cfbDecryptFinal_ct`: the modes' final function in
constant time (`Proof.Modes.X86_64.cfbFinal_ct`), from IDEA's CFB64
functions' (by the taint analysis, as in `FbVerified.lean`) and the taint
analysis of its own pieces: the precondition gives `cfbFinal_wp`'s
hypotheses (`finalHyps`), and the public arguments the inlined functions'
public data, which their states the correctness proof describes pin to the
same values in both runs.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64
open VG.Proof.Modes.X86_64 (FinalOk FinalHyps FinalTaint Call₁ Call₂ After₁ frameRegion blockAddr slotsRegion
  frameSp slots_sub_frame block_slots cfbFinal_ct lenOf dataOf)

theorem slotsW_ok {s₀ : State} (hp : finalPre s₀) : ∀ r ∈ wrW s₀, r.Disjoint (slotsRegion s₀) := by
  have hfr := finalPre_frame hp
  have fK : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint (slotsRegion s₀) r := fun r hr => (hfr r hr).sub_left (slots_sub_frame s₀)
  have hsubD : Region.Sub ⟨s₀.gpr .rdx, 8 * ((s₀.gpr .rcx).toNat / 8)⟩ ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩ :=
    Region.sub_prefix (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  intro r hr
  simp only [wrW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (fK _ (by simp)).symm
  · exact ((fK _ (by simp)).sub_right hsubD).symm
  · exact (fK _ (by simp)).symm

theorem slotsE_ok {s₀ : State} (hp : finalPre s₀) : ∀ r ∈ wrE s₀, r.Disjoint (slotsRegion s₀) := by
  have hfr := finalPre_frame hp
  have fK : ∀ r ∈ ([⟨s₀.gpr .rdi, 104⟩, ⟨s₀.gpr .rsi, 8⟩, ⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩, ⟨s₀.gpr .r8, 8 * 22⟩] :
      List Region), Region.Disjoint (slotsRegion s₀) r := fun r hr => (hfr r hr).sub_left (slots_sub_frame s₀)
  intro r hr
  simp only [wrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (fK _ (by simp)).symm
  · exact block_slots s₀ (by decide)
  · exact (fK _ (by simp)).symm

theorem dataOf_final (s : State) : dataOf finalArgs s = s.gpr .rdx := rfl
theorem lenOf_final (s : State) : lenOf finalArgs s = (s.gpr .rcx).toNat := rfl

/-- The final encryption's precondition gives `cfbFinal_wp`'s hypotheses. -/
theorem finalHyps_enc {s₀ : State} (hp : finalPre s₀) :
    FinalHyps finalArgs cfbEncrypt cfbEncX86_64 cfbEncX86_64 rdW wrW rdW wrE s₀ := by
  have hp' := hp
  obtain ⟨⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, fitD, -⟩, h80, -⟩ := hp'
  have hfr := finalPre_frame hp
  exact ⟨h80, by rw [hwr, dataOf_final, lenOf_final]; simp, by rw [dataOf_final, lenOf_final]; exact fitD,
    by rw [dataOf_final, lenOf_final]; exact (hfr _ (by simp)).symm, fun u hu => call₁_pre hp hu, slotsW_ok hp,
    fun u₁' v u hA _ vrd vwr hu => call₂_pre hp (.inl hA) vrd vwr hu, slotsE_ok hp⟩

/-- The final decryption's precondition gives `cfbFinal_wp`'s hypotheses. -/
theorem finalHyps_dec {s₀ : State} (hp : finalPre s₀) :
    FinalHyps finalArgs cfbDecrypt cfbDecX86_64 cfbEncX86_64 rdW wrW rdW wrE s₀ := by
  have hp' := hp
  obtain ⟨⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, fitD, -⟩, h80, -⟩ := hp'
  have hfr := finalPre_frame hp
  exact ⟨h80, by rw [hwr, dataOf_final, lenOf_final]; simp, by rw [dataOf_final, lenOf_final]; exact fitD,
    by rw [dataOf_final, lenOf_final]; exact (hfr _ (by simp)).symm, fun u hu => call₁_pre hp hu, slotsW_ok hp,
    fun u₁' v u hA _ vrd vwr hu => call₂_pre hp (.inr hA) vrd vwr hu, slotsE_ok hp⟩

theorem finalTaint : FinalTaint finalArgs :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX86_64.pre cfbEncX86_64.pub cfbEncrypt :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX86_64.pre cfbDecX86_64.pub cfbDecrypt :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem final_pub {s₁ s₂ : State} (hq : fbPub s₁ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < finalArgs.regs.length, s₁.gpr (finalArgs.arg i) = s₂.gpr (finalArgs.arg i) := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hq
  refine ⟨p6, fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp only [finalArgs, List.length] at hi; omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem final_pubW {s₁ s₂ u₁ u₂ : State} (hq : fbPub s₁ s₂)
    (c₁ : Call₁ finalArgs s₁ (lenOf finalArgs s₁) u₁) (c₂ : Call₁ finalArgs s₂ (lenOf finalArgs s₂) u₂) :
    fbPub (u₁.withRegions (rdW s₁) (wrW s₁)) (u₂.withRegions (rdW s₂) (wrW s₂)) := by
  have hq' := hq
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hq'
  have e : ∀ i < 5, i ≠ 3 → u₁.gpr (finalArgs.arg i) = u₂.gpr (finalArgs.arg i) := fun i hi h3 =>
    (c₁.args i hi h3).trans (((final_pub hq).2 i hi).trans (c₂.args i hi h3).symm)
  have hb : u₁.gpr .rcx = u₂.gpr .rcx := by
    have h₁ := c₁.blocks; have h₂ := c₂.blocks
    rw [lenOf_final] at h₁ h₂
    exact h₁.trans (p4 ▸ h₂.symm)
  exact ⟨e 0 (by decide) (by decide), e 1 (by decide) (by decide), e 2 (by decide) (by decide), hb,
    e 4 (by decide) (by decide), c₁.rsp.trans (p6 ▸ c₂.rsp.symm)⟩

theorem final_pubE {s₁ s₂ v₁ v₂ u₁ u₂ : State} (hq : fbPub s₁ s₂)
    (c₁ : Call₂ finalArgs s₁ v₁ u₁) (c₂ : Call₂ finalArgs s₂ v₂ u₂) :
    fbPub (u₁.withRegions (rdW s₁) (wrE s₁)) (u₂.withRegions (rdW s₂) (wrE s₂)) := by
  have hq' := hq
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hq'
  have e : ∀ i < 5, i ≠ 3 → i ≠ 2 → u₁.gpr (finalArgs.arg i) = u₂.gpr (finalArgs.arg i) := fun i hi h3 h2 =>
    (c₁.args i hi h3 h2).trans (((final_pub hq).2 i hi).trans (c₂.args i hi h3 h2).symm)
  have hd : blockAddr s₁ = blockAddr s₂ := by simp only [blockAddr, p6]
  exact ⟨e 0 (by decide) (by decide) (by decide), e 1 (by decide) (by decide) (by decide),
    c₁.data.trans (hd ▸ c₂.data.symm), c₁.blocks.trans c₂.blocks.symm,
    e 4 (by decide) (by decide) (by decide), c₁.rsp.trans (p6 ▸ c₂.rsp.symm)⟩

/-- `vg_idea_cfb64_encrypt_final` on x86-64 runs in constant time. -/
theorem cfbEncryptFinal_ct : ConstantTime isa finalPre fbPub cfbEncryptFinal :=
  cfbFinal_ct finalArgs_ok cfbEncrypt_correct cfbEncrypt_correct cfbEncrypt_spSafe cfbEncrypt_spSafe
    (by rw [cfbEncrypt_depth]; decide) (by rw [cfbEncrypt_depth]; decide) cfbEncrypt_ct cfbEncrypt_ct finalTaint
    (fun _ hp => finalHyps_enc hp) (fun _ _ _ _ hq => final_pub hq)
    (fun _ _ _ _ _ _ hq c₁ c₂ => final_pubW hq c₁ c₂) (fun _ _ _ _ _ _ _ _ hq c₁ c₂ => final_pubE hq c₁ c₂)

/-- `vg_idea_cfb64_decrypt_final` on x86-64 runs in constant time. -/
theorem cfbDecryptFinal_ct : ConstantTime isa finalPre fbPub cfbDecryptFinal :=
  cfbFinal_ct finalArgs_ok cfbDecrypt_correct cfbEncrypt_correct cfbDecrypt_spSafe cfbEncrypt_spSafe
    (by rw [cfbDecrypt_depth]; decide) (by rw [cfbEncrypt_depth]; decide) cfbDecrypt_ct cfbEncrypt_ct finalTaint
    (fun _ hp => finalHyps_dec hp) (fun _ _ _ _ hq => final_pub hq)
    (fun _ _ _ _ _ _ hq c₁ c₂ => final_pubW hq c₁ c₂) (fun _ _ _ _ _ _ _ _ hq c₁ c₂ => final_pubE hq c₁ c₂)

/-! ## Verified -/

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 22⟩]

/-- IDEA's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Idea.cipher (Spec.Idea.scheduleAt m k)

/-- The final functions' signature with their scratch buffer. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 104 8

theorem cfbEncryptFinal_verified :
    Verified X86_64.target cfbEncryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 22
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 80) :=
  Verified.of_correct (k := cfbEncFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbEncryptFinal_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalX86_64, finalPre, frameRegion, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [finalSat] using finalSat)

theorem cfbDecryptFinal_verified :
    Verified X86_64.target cfbDecryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 22
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 80) :=
  Verified.of_correct (k := cfbDecFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbDecryptFinal_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalX86_64, finalPre, frameRegion, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [finalSat] using finalSat)

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cfbEncryptFinal)
      (Spec.Idea.cfbEncryptFinalContract X86_64.abi 264) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 80)
    (bytes := 184) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.encFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cfbDecryptFinal)
      (Spec.Idea.cfbDecryptFinalContract X86_64.abi 264) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 80)
    (bytes := 184) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.decFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Idea.X86_64
