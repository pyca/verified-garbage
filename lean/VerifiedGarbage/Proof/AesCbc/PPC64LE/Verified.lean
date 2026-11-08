module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Vec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Vec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
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

section
open VG.Proof.Aes.PPC64LE.Crypto (aesState result schedule batchFacts breg_mem load_state)
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs)

theorem decGroup_ok : GroupOk (cbcMode false) decGroup := by
  intro s₀ hp k hk s h
  have hR := h.regs hp
  have hW := h.wrs hp
  have facts := batchFacts ⟨8, by decide⟩
  rw [decGroup]
  simp only [List.append_assoc]
  refine WP.seq (saveSlots_wp hp (m := 8) (by decide) hk h fun s₁ g₁ rd₁ wr₁ f₁ e₀ e₁ => ?_)
  refine read8_wp hp hk (by rw [g₁ _ (by decide), h.r14]) (by rw [g₁ _ (by decide), h.r15])
    (by rw [g₁ _ (by decide), h.r17]) (by rw [rd₁, wr₁, hR]) fun u hu => wp_nil ?_
  refine WP.seq (WP.mono (Proof.Aes.PPC64LE.Crypto.aes_ok true (batchRegs 8) facts.1 facts.2.1 facts.2.2.1
    hu.inp) fun v ⟨hv, hl⟩ => ?_)
  have gv (r : Reg) (hr : r ∈ preserved) : v.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, -⟩ := pres_ne hr
    rw [hl.keep.gpr (by simp [h9, h10]), hu.g r hr, g₁ r h9]
  have h0 : v.gpr .r0 = 0 := (hl.keep.gpr (by decide)).trans hu.inp.zero
  have hm := (hl.v _ (by simp [facts.2.2.1])).trans hu.inp.mask
  have rwv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hl.keep.2.1, hl.keep.2.2, hu.rd, hu.wr, rd₁, wr₁]
  have mv : v.mem = s₁.mem := by rw [hl.mem, hu.mem]
  rw [WP.block_append_iff]
  refine WP.mono (xorSlots_ok s₀ v (by rw [gv _ (by decide), h.r19]) h0 hm fun j hj => by
    rw [rwv, hR]; exact in_rw (by simp) (cSl16 s₀ hj)) fun x hx => ?_
  have r6x : x.gpr .r6 = blk s₀ k := by
    rw [hx.loc.keep.gpr (by decide), hl.keep.gpr (by decide), hu.r6]
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok x r6x ((hx.loc.keep.gpr (by decide)).trans h0)
    ((hx.loc.v _ (by simp [facts.2.2.1])).trans hm) fun j hj => ?_) fun y hy => ?_
  · rw [hx.loc.keep.2.2, hl.keep.2.2, hu.wr, wr₁, hW, blk_add]
    exact in_rw (by simp) (cBlk16 hp (by omega))
  have gy (r : Reg) (hr : r ∈ preserved) : y.gpr r = s.gpr r := by
    obtain ⟨-, -, -, h6, h7, -⟩ := pres_ne hr
    rw [hy.keep.gpr (by simpa using h6), hx.loc.keep.gpr (by simpa using h7), gv r hr]
  have rwy : y.rd ++ y.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [hy.keep.2.1, hy.keep.2.2, hx.loc.keep.2.1, hx.loc.keep.2.2, rwv, hR]
  have wy : y.wr = [ivR s₀, dataR s₀, scrR s₀] := by
    rw [hy.keep.2.2, hx.loc.keep.2.2, hl.keep.2.2, hu.wr, wr₁, hW]
  refine copy_wp (P := Iv s₀) (Q := sl s₀ 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [gy _ (by decide), h.r16, ofNat_zero_add]) (by rw [gy _ (by decide), h.r16])
    (by rw [gy _ (by decide), h.r19]) (by rw [gy _ (by decide), h.r19, sl8])
    (by rw [rwy]; exact in_rw (by simp) (cSl s₀ (by decide)))
    (by rw [rwy]; exact in_rw (by simp) (cSl8 s₀ (by decide)))
    (by rw [wy]; exact in_rw (by simp) cIv0) (by rw [wy]; exact in_rw (by simp) cIv8)
    fun z gz mz rdz wrz => advance8_regs (s := z) hk
      (by rw [gz _ (by decide), gy _ (by decide), h.r17]) (by rw [gz _ (by decide), gy _ (by decide), h.r18])
      fun w r17 r18 keep mw rdw wrw => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : w.gpr r = s.gpr r := by
    rw [keep r h17 h18, gz r (pres_ne hr).2.2.2.2.2.2.1, gy r hr]
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have hw : schedule (R s₀) u = wK s₀ := by
    rw [Proof.Aes.PPC64LE.Crypto.schedule, hu.r3, hu.mem, UPre.sched_bytes hp big₁]
  have slot (j : Nat) (hj : j ≤ 8) : bytesAt s₁.mem (sl s₀ j) 16 = chainK (cbcMode false) s₀ (k + j) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact e₀
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [e₁ i (by omega), ← Nat.add_assoc, cbcDec_chain s₀ (by omega)]
  have mx : x.mem = s₁.mem := by rw [hx.loc.mem, mv]
  refine group_step cbcDec_steps hp hk h ?_ ?_ ?_ r17 r18 ?_ (fun r hr hv => ?_) ?_ ?_ ?_ (fun j hj => ?_) ?_
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · exact g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e]))
  · rw [rdw, rdz, hy.keep.2.1, hx.loc.keep.2.1, hl.keep.2.1, hu.rd, rd₁]
  · rw [wrw, wrz, hy.keep.2.2, hx.loc.keep.2.2, hl.keep.2.2, hu.wr, wr₁]
  · rw [mw, mz]
    refine (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩).trans ?_
    refine (mx ▸ hy.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans ?_
    exact (copyMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩
  · have hi : k + j < N s₀ := by omega
    rw [mw, mz, copyMem_other _ (hp.blk_iv hi), ← blk_add, AesCbc.bytesAt_toList,
      hy.processed.stateAt (j := j) hj (Nat.le_refl _), hx.val j hj, ite_eq_left hj, st_xor,
      hv _ (breg_mem hj), hu.val j hj, hw, mv, load_state, load_state, ← AesCbc.bytesAt_toList,
      slot j (by omega), ← h.blockAt (by omega) hi, ← bytesAt_frame f₁ (one_disj (hp.dBG hi)) (by decide),
      AesCbc.aesInvWith_state]
    simp only [result, ite_true]
  · rw [mw, mz, copyMem_bytes _ (hp.dIS (by decide)),
      bytesAt_frame hy.frame (one_disj (hp.dSB (j := 8) (m := 8) (by decide) hk)) (by decide), mx,
      slot 8 (by decide)]

end

theorem decGroup_taint : ∃ h, (vectorTaint.check (Taint.ofRegs vars) decGroup h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decGroup_ct : GroupCt (cbcMode false) decGroup := by
  intro s₀ s₀' _ _ hq k
  obtain ⟨_, ht⟩ := decGroup_taint
  exact RelCT.taint (A := vectorTaint) (Taint.ofRegs vars)
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, pub_sp hq],
      fun r h' => LInv.agree hq h.2.1.1 h.2.2.1 r (Taint.mem_ofRegs.mp h')⟩) ht

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
