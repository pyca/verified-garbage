module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.Rounds
meta import VerifiedGarbage.Impl.AesCbc.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Spec.Cbc.Contract
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CBC on PPC64LE: `Verified`

Correctness and constant time, a state satisfying the precondition, and the
shared contracts of `Spec/Cbc/Contract.lean` (with no stack: a call stores
nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

/-! ## Decryption, eight blocks at a time -/

/-- CBC decryption extends its output one block at a time. -/
theorem cbcDec_steps : Steps (cbcMode false) fun R w x c => Spec.Cbc.xor (Spec.Cbc.aesInvWith R w x) c := by
  intro R w iv xs x
  simp only [cbcMode_out, cbcMode_chain, cbc, ciphOf, cts, Bool.false_eq_true, ite_false, decrypt_snoc]

/-- The chaining value after block `i` is block `i`. -/
theorem cbcDec_chain (s₀ : State) {i : Nat} (hi : i < N s₀) :
    chainK (cbcMode false) s₀ (i + 1) = blkOf s₀ i := by
  simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blkOf s₀ hi, next_snoc]

theorem decGroup_ok : GroupOk (cbcMode false) decGroup := by
  intro s₀ hp k hk s h
  have hR := h.regs hp
  have hW := h.wrs hp
  refine WP.seq (saveSlots_wp hp (m := 8) (by decide) hk h fun s₁ g₁ rd₁ wr₁ f₁ e₀ e₁ =>
    callArgs8_wp fun s₂ r3₂ r4₂ r5₂ r6₂ r7₂ o₂ mem₂ rd₂ wr₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, h9, -⟩ := preserved_ne hr
    rw [o₂ r (by simp [argRegs5, h3, h4, h5, h6, h7]), g₁ r h9]
  have pre := hp.callPre8 hk (by rw [r3₂, g₁ _ (by decide), h.r14]) (by rw [r4₂, g₁ _ (by decide), h.r15])
    (by rw [r5₂, g₁ _ (by decide), h.r17]) r6₂ (by rw [r7₂, g₁ _ (by decide), h.r19])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr])
  refine WP.seq (WP.mono (blk_call8 Proof.Aes.PPC64LE.decryptBlocks_framed decryptBlocks_noFrames pre)
    fun s₃ c => ?_)
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [c.rd, c.wr, rd₂, wr₂, rd₁, wr₁, hR]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, wr₂, wr₁, hW]
  rw [fixSlots, List.append_assoc]
  refine fixes_wp hp 8 (by decide) hk (by rw [g₃ _ (by decide), h.r17]) (by rw [g₃ _ (by decide), h.r19])
    hR₃ hW₃ fun s₄ g₄ rd₄ wr₄ f₄ e₄ => ?_
  have hR₄ : s₄.rd ++ s₄.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₄, wr₄, hR₃]
  have hW₄ : s₄.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₄, hW₃]
  have g₄' (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₄ r h9 h10, g₃ r hr]
  refine copy_wp (P := Iv s₀) (Q := sl s₀ 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₄' _ (by decide), h.r16, ofNat_zero_add]) (by rw [g₄' _ (by decide), h.r16])
    (by rw [g₄' _ (by decide), h.r19]) (by rw [g₄' _ (by decide), h.r19, sl8])
    (by rw [hR₄]; exact in_rw (by simp) (cSl s₀ (by decide)))
    (by rw [hR₄]; exact in_rw (by simp) (cSl8 s₀ (by decide)))
    (by rw [hW₄]; exact in_rw (by simp) cIv0) (by rw [hW₄]; exact in_rw (by simp) cIv8)
    fun s₅ g₅ mem₅ rd₅ wr₅ => advance8_regs (s := s₅) hk
      (by rw [g₅ _ (by decide), g₄' _ (by decide), h.r17]) (by rw [g₅ _ (by decide), g₄' _ (by decide), h.r18])
      fun s₆ r17₆ r18₆ keep₆ mem₆ rd₆ wr₆ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₆.gpr r = s.gpr r := by
    rw [keep₆ r h17 h18, g₅ r (preserved_ne hr).2.2.2.2.2.1, g₄' r hr]
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  -- The slots after the call.
  have slot (j : Nat) (hj : j ≤ 8) : bytesAt s₃.mem (sl s₀ j) 16 = chainK (cbcMode false) s₀ (k + j) := by
    rw [bytesAt_frame c.frame (one_disj (hp.dSB hj (by omega))) (by decide), mem₂]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact e₀
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [e₁ i (by omega), ← Nat.add_assoc, cbcDec_chain s₀ (by omega)]
  -- The blocks after the call.
  have dec (j : Nat) (hj : j < 8) : bytesAt s₃.mem (blk s₀ (k + j)) 16 =
      Spec.Cbc.aesInvWith (R s₀) (wK s₀) (blkOf s₀ (k + j)) := by
    have := c.out j hj
    rw [blk_add] at this
    rw [this, ← aesInvWith_state, mem₂, UPre.sched_bytes hp big₁,
      bytesAt_frame f₁ (one_disj (hp.dBG (by omega))) (by decide), h.blockAt (by omega) (by omega)]
  refine group_step cbcDec_steps hp hk h ?_ ?_ ?_ r17₆ r18₆ ?_ (fun r hr hv => ?_) ?_ ?_ ?_ (fun j hj => ?_) ?_
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · exact g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e]))
  · rw [rd₆, rd₅, rd₄, c.rd, rd₂, rd₁]
  · rw [wr₆, wr₅, wr₄, c.wr, wr₂, wr₁]
  · rw [mem₆, mem₅]
    refine (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩).trans ?_
    refine (by rw [← mem₂]; exact (c.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩) :
      Frame [⟨blk s₀ k, 128⟩, ivR s₀, ⟨S s₀, 2064⟩] s₁.mem s₃.mem).trans ?_
    refine (f₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans ?_
    exact (copyMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩
  · rw [mem₆, mem₅, copyMem_other _ (hp.blk_iv (by omega)), e₄ j hj, dec j hj, slot j (by omega)]
  · rw [mem₆, mem₅, copyMem_bytes _ (hp.dIS (by decide)),
      bytesAt_frame f₄ (one_disj (hp.dSB (by decide) (by omega))) (by decide), slot 8 (by decide)]

/-- The code before the call of a group leaves the call's arguments. -/
theorem decA8_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block (saveSlots 8 ++ callArgs8)) s fun s₂ =>
      CallPre8 s₂ (W s₀) (blk s₀ k) (S s₀) (R s₀) ∧ ∀ r ∈ preserved, s₂.gpr r = s.gpr r :=
  saveSlots_wp hp (m := 8) (by decide) hk h fun s₁ g₁ rd₁ wr₁ _ _ _ =>
    callArgs8_wp fun s₂ r3₂ r4₂ r5₂ r6₂ r7₂ o₂ _ rd₂ wr₂ =>
      ⟨hp.callPre8 hk (by rw [r3₂, g₁ _ (by decide), h.r14]) (by rw [r4₂, g₁ _ (by decide), h.r15])
        (by rw [r5₂, g₁ _ (by decide), h.r17]) r6₂ (by rw [r7₂, g₁ _ (by decide), h.r19])
        (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]), fun r hr => by
          obtain ⟨h3, h4, h5, h6, h7, h9, -⟩ := preserved_ne hr
          rw [o₂ r (by simp [argRegs5, h3, h4, h5, h6, h7]), g₁ r h9]⟩

theorem decGroupPre_taint : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (saveSlots 8 ++ callArgs8)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroupPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (fixSlots ++ copy .r16 0 .r19 (slot 8) ++ advance8)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_ct : GroupCt (cbcMode false) decGroup :=
  fun hp hp' hq k => group_ct (D := fun s₀ k => blk s₀ k) (Sc := S) (fun hq k => pub_blk hq k)
    (fun hq => pub_S hq) Proof.Aes.PPC64LE.decryptBlocks_correct Proof.Aes.PPC64LE.decryptBlocks_framed
    Proof.Aes.PPC64LE.decryptBlocks_ct decryptBlocks_noFrames decGroupPre_taint decGroupPost_taint
    (@fun _ hp _ hk _ h => decA8_wp hp hk h) hp hp' hq k

theorem encrypt_correct (s : State) (hs : (cbcPPC64LE true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cbcPPC64LE true).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cbcPPC64LE false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cbcPPC64LE false).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp decGroup_ok decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified : Verified PPC64LE.target encrypt (Proof.AesCbc.encryptRoundsContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Proof.AesCbc.encryptRoundsContract, Spec.Cbc.aesSig, cbcPPC64LE, modePPC64LE, cbcMode,
      ciphOf, cbc, cts, PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Proof.AesCbc.decryptRoundsContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct (batched_ct decGroup_ok decGroup_ct decBody_ok decBody_ct) (by
    sig_implies [Proof.AesCbc.decryptRoundsContract, Spec.Cbc.aesSig, cbcPPC64LE, modePPC64LE, cbcMode,
      ciphOf, cbc, cts, PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

end VG.Proof.AesCbc.PPC64LE
