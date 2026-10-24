module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashCT
import VerifiedGarbage.Proof.AesOcb.PPC64LE.BodyCT
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.BodyCT
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesOcb.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# AES-OCB on PPC64LE: `seal` and `open` up to the tag are constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 112`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`entry_rel`). After it, the environment of each run is
its own registers (`EntryPost`), which agree on the public ones
(`agree_entry`). Then `nonce_rel`, `hash_rel`, `body_rel` and `tag_rel`,
each from the states the correctness proofs describe (`Seal.lean`), and the
code after the tag, which has no calls, from the public registers
(`front_rel`). As on AArch64 (`Proof/AesOcb/AArch64/SealCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.PPC64LE (oneA_ok in_off add_ofNat_assoc)

/-- Two runs of `front; tail` are two runs of `front`'s pieces, then `tail`. -/
theorem rel_front {P Q : State → State → Prop} {e n h b t tail : Prog isa}
    (hr : RelCT isa P (.seq e (.seq n (.seq h (.seq b (.seq t tail))))) Q) :
    RelCT isa P (.seq (.seq e (.seq n (.seq h (.seq b t)))) tail) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq f₁ r₁ => cases f₁ with | seq a₁ f₁ => cases f₁ with | seq b₁ f₁ =>
  cases f₁ with | seq c₁ f₁ => cases f₁ with | seq d₁ g₁ =>
  cases e₂ with | seq f₂ r₂ => cases f₂ with | seq a₂ f₂ => cases f₂ with | seq b₂ f₂ =>
  cases f₂ with | seq c₂ f₂ => cases f₂ with | seq d₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq g₁ r₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq g₂ r₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- The entry's stack arguments are where the state may read them. -/
theorem argsIn {s : State} (hA : Covers [⟨s.sp + BitVec.ofNat 64 96, 24⟩] (s.rd ++ s.wr)) {i : Nat} (hi : i < 3) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (96 + 8 * i)) 8 := by
  have := in_off hA (d := 8 * i) (n := 8) (by omega) (by decide)
  rwa [add_ofNat_assoc] at this

/-- The entry of `seal` and `open`, in two runs with the same arguments. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hA₁ : Covers [⟨σ₁.sp + BitVec.ofNat 64 96, 24⟩] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [⟨σ₂.sp + BitVec.ofNat 64 96, 24⟩] (σ₂.rd ++ σ₂.wr)) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  simp only [entry, Impl.AesGcm.PPC64LE.openEntry, Impl.AesGcm.PPC64LE.oneEntry, List.append_assoc]
  refine RelCT.block_append (rel_seq (rel_taint [] qsp (by agree_ppc []) ⟨_, by taint_decide⟩)
    (oneA_ok (off := 112) (W := W) (.inr rfl) (argsIn hA₁ (i := 2) (by decide)) (by rw [← hW₁, stackArg_eq']))
    (oneA_ok (off := 112) (W := W) (.inr rfl) (argsIn hA₂ (i := 2) (by decide)) (by rw [← hW₂, stackArg_eq']))
    fun τ₁ τ₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ => ?_)
  refine rel_taint [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] (by rw [k₁.sp, k₂.sp, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h12 : r = .r12
  · subst h12; rw [a₁, a₂]
  · rw [g₁ r h12, g₂ r h12]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h12] at hr ⊢; exact hr)

/-- `nonce`, in two runs with the same nonce's address and length. -/
theorem nonce_rel {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) nonce TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold nonce
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.r24, .r25] (by agree_ppc [h24, h25]) ⟨_, by taint_decide⟩)
    [.r0, .r3, .r4, .r5, .r6] (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The registers after the entry agree on the public ones in two runs with
the same arguments. -/
theorem agree_entry {σ₁ σ₂ τ₁ τ₂ : State} {W T : Addr} (P₁ : EntryPost W T σ₁ τ₁) (P₂ : EntryPost W T σ₂ τ₂)
    (hq : ∀ r ∈ [Reg.r3, .r4, .r6, .r7, .r8, .r9, .r10], σ₁.gpr r = σ₂.gpr r) (ht : stackArg σ₁ 1 = stackArg σ₂ 1) :
    Agree τ₁.gpr τ₂.gpr := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true] at hq
  obtain ⟨q3, q4, q6, q7, q8, q9, q10⟩ := hq
  simp only [Agree, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  exact ⟨by rw [P₁.r18, P₂.r18, q6], by rw [P₁.r19, P₂.r19, ht], by rw [P₁.r20, P₂.r20],
    by rw [P₁.r21, P₂.r21, q7], by rw [P₁.r22, P₂.r22, q8], by rw [P₁.r23, P₂.r23, q10],
    by rw [P₁.r27, P₂.r27, q9], by rw [P₁.r28, P₂.r28, q4], by rw [P₁.r29, P₂.r29, q3],
    by rw [P₁.r31, P₂.r31]⟩

/-- What `HASH` needs after the entry and `nonce`. -/
theorem hctx_of {s₀ s₁ s₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (h3 : s₀.gpr .r3 = K) {o : Block}
    (P₂ : NonceOk s₁.gpr s₀.sp o s₁ s₂) :
    HCtx (s₁.gpr .r29) (s₁.gpr .r31) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s₂ ∧
      blockAtMem s₂.mem (s₁.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar s₀.mem K) 0 := by
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  have hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  have F₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have F₁₂ := F₁.trans (frameW pf₂ (nonceR_W W))
  refine ⟨{
      lay := by rw [hK₁, hW₁]; exact Ar.lay
      rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans P₁.keeps.rd) (P₂.wr.trans P₁.keeps.wr)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := by rw [hK₁]; exact Ar.data.k
      dw := by rw [hW₁]; exact Ar.data.w }, ?_⟩
  rw [P₂.keep (by decide) (by decide), hW₁, P₁.l0, h3]

/-- `front enc d` and then code without calls, in two runs with the same
arguments. -/
theorem front_rel (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa}
    (hk : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) k h).isSome = true)
    {σ₁ σ₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (A₁ : FnArgs σ₁ K W N A D R nl al n tl T) (A₂ : FnArgs σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (hT₁ : stackArg σ₁ 0 = T) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h3₁ : σ₁.gpr .r3 = K) (h4₁ : σ₁.gpr .r4 = BitVec.ofNat 64 R) (h5₁ : σ₁.gpr .r5 = N)
    (h6₁ : σ₁.gpr .r6 = BitVec.ofNat 64 nl) (h7₁ : σ₁.gpr .r7 = A) (h8₁ : σ₁.gpr .r8 = BitVec.ofNat 64 al)
    (h9₁ : σ₁.gpr .r9 = D) (h10₁ : σ₁.gpr .r10 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (hT₂ : stackArg σ₂ 0 = T) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h3₂ : σ₂.gpr .r3 = K) (h4₂ : σ₂.gpr .r4 = BitVec.ofNat 64 R) (h5₂ : σ₂.gpr .r5 = N)
    (h6₂ : σ₂.gpr .r6 = BitVec.ofNat 64 nl) (h7₂ : σ₂.gpr .r7 = A) (h8₂ : σ₂.gpr .r8 = BitVec.ofNat 64 al)
    (h9₂ : σ₂.gpr .r9 = D) (h10₂ : σ₂.gpr .r10 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have L₁ : Lay (σ₁.gpr .r3) W := by rw [h3₁]; exact A₁.lay
  have L₂ : Lay (σ₂.gpr .r3) W := by rw [h3₂]; exact A₂.lay
  have hC₁ : Covers [⟨σ₁.gpr .r3, 256⟩] (σ₁.rd ++ σ₁.wr) := by rw [h3₁]; exact A₁.perm.k
  have hC₂ : Covers [⟨σ₂.gpr .r3, 256⟩] (σ₂.rd ++ σ₂.wr) := by rw [h3₂]; exact A₂.perm.k
  unfold front
  refine rel_front (rel_seq (entry_rel hW₁ hW₂ A₁.args A₂.args qsp
      (by agree_ppc [h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂, h8₁, h8₂, h9₁, h9₂, h10₁, h10₂]))
    (entry_ok L₁ A₁.perm.w hC₁ hW₁ hT₁ A₁.args A₁.argsW) (entry_ok L₂ A₂.perm.w hC₂ hW₂ hT₂ A₂.args A₂.argsW)
    fun τ₁ τ₂ P₁ P₂ => ?_)
  have hV : Agree τ₁.gpr τ₂.gpr := agree_entry P₁ P₂
    (by agree_ppc [h3₁, h3₂, h4₁, h4₂, h6₁, h6₂, h7₁, h7₂, h8₁, h8₂, h9₁, h9₂, h10₁, h10₂]) (by rw [htl₁, htl₂])
  have E₁ := P₁.env
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have L : Lay (τ₁.gpr .r29) (τ₁.gpr .r31) := by rw [P₁.r29, P₁.r31, h3₁]; exact A₁.lay
  have h28 : τ₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4₁
  have h28₂ : τ₂.gpr .r28 = BitVec.ofNat 64 R := P₂.r28.trans h4₂
  have L₂' : Lay (τ₂.gpr .r29) (τ₂.gpr .r31) := hV.lay L
  have hn1 := A₁.n1
  have hn15 := A₁.n15
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega
  -- `nonce` and `HASH`
  refine RelCT.assoc (rel_seq (rel_seq (nonce_rel L hV A₁.rounds h28 E₁ E₂ (by rw [P₁.r24, P₂.r24, h5₁, h5₂])
      (by rw [P₁.r25, P₂.r25, h6₁, h6₂]))
    (nonce_ok L A₁.rounds h28 E₁ (P₁.r24.trans h5₁) (P₁.r25.trans h6₁) (P₁.r19.trans htl₁) hn1 hn15 ht
      (by rw [P₁.r31]; exact A₁.nonce.of_eq P₁.keeps.rd P₁.keeps.wr) (by rw [P₁.r29, h3₁]; exact A₁.data.k))
    (nonce_ok L₂' A₁.rounds h28₂ E₂ (P₂.r24.trans h5₂) (P₂.r25.trans h6₂) (P₂.r19.trans htl₂) hn1 hn15 ht
      (by rw [P₂.r31]; exact A₂.nonce.of_eq P₂.keeps.rd P₂.keeps.wr) (by rw [P₂.r29, h3₂]; exact A₂.data.k))
    fun u₁ u₂ Q₁ Q₂ => ?_) (preRest_wp A₁ P₁ htl₁ h3₁ h4₁ h5₁ h6₁ h7₁ h8₁)
    (preRest_wp A₂ P₂ htl₂ h3₂ h4₂ h5₂ h6₂ h7₂ h8₂) fun w₁ w₂ R₁ R₂ => ?_)
  · have E₂' := Q₂.env
    rw [qsp] at Q₂
    obtain ⟨C₁, l0₁⟩ := hctx_of A₁ P₁ h3₁ Q₁
    obtain ⟨C₂, l0₂⟩ := hctx_of A₂ P₂ h3₂ Q₂
    exact hash_rel hV C₁ C₂ h28 (by rw [length_bytesAt, length_bytesAt]) Q₁.env E₂'
      (P₁.r21.trans h7₁) (by rw [P₁.r22, h8₁, length_bytesAt]) l0₁ l0₂
  -- the data and the tag
  have F₁ := R₁.env
  have F₂ := R₂.env
  rw [← qsp] at F₂
  have h23 : τ₁.gpr .r23 = BitVec.ofNat 64 n := P₁.r23.trans h10₁
  have h23₂ : τ₂.gpr .r23 = BitVec.ofNat 64 n := P₂.r23.trans h10₂
  have hD₁ : DBuf (τ₁.gpr .r29) (τ₁.gpr .r31) w₁ (τ₁.gpr .r27) n := by
    rw [P₁.r29, P₁.r31, P₁.r27, h3₁, h9₁]; exact A₁.data.of_eq R₁.rd R₁.wr
  have hD₂ : DBuf (τ₂.gpr .r29) (τ₂.gpr .r31) w₂ (τ₂.gpr .r27) n := by
    rw [P₂.r29, P₂.r31, P₂.r27, h3₂, h9₂]; exact A₂.data.of_eq R₂.rd R₂.wr
  have l0₁ : blockAtMem w₁.mem (τ₁.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₁.mem (τ₁.gpr .r29)) 0 := by
    rw [P₁.r31, P₁.r29, R₁.l0, h3₁, ctxLstar_W A₁.lay R₁.frame]
  have l0₂ : blockAtMem w₂.mem (τ₂.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₂.mem (τ₂.gpr .r29)) 0 := by
    rw [P₂.r31, P₂.r29, R₂.l0, h3₂, ctxLstar_W A₂.lay R₂.frame]
  have o₁ := R₁.ofs
  have o₂ := R₂.ofs
  have z₁ := R₁.o0
  have z₂ := R₂.o0
  have c₁ := R₁.ck
  have c₂ := R₂.ck
  rw [← P₁.r31] at o₁ z₁ c₁
  rw [← P₂.r31] at o₂ z₂ c₂
  cases enc
  · refine rel_seq (body_rel L hV A₁.rounds h28 false F₁ F₂ h23 hD₁ hD₂
        (wholeEnv_open L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁)
        (wholeEnv_open L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂))
      (WP.mono (bodyOpen_ok L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁) fun _ B => B.env)
      (WP.mono (bodyOpen_ok L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂) fun _ B => B.env) fun y₁ y₂ G₁ G₂ => ?_
    refine rel_seq (tag_rel L hV A₁.rounds h28 G₁ G₂ hd) (tag_ok L G₁ A₁.rounds h28 hd)
      (tag_ok L₂' G₂ A₁.rounds h28₂ hd) fun x₁ x₂ T₁ T₂ => ?_
    exact rel_env T₁.env T₂.env hV [] (by agree_ppc []) hk
  · refine rel_seq (body_rel L hV A₁.rounds h28 true F₁ F₂ h23 hD₁ hD₂
        (wholeEnv_seal L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁)
        (wholeEnv_seal L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂))
      (WP.mono (bodySeal_ok L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁) fun _ B => B.env)
      (WP.mono (bodySeal_ok L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂) fun _ B => B.env) fun y₁ y₂ G₁ G₂ => ?_
    refine rel_seq (tag_rel L hV A₁.rounds h28 G₁ G₂ hd) (tag_ok L G₁ A₁.rounds h28 hd)
      (tag_ok L₂' G₂ A₁.rounds h28₂ hd) fun x₁ x₂ T₁ T₂ => ?_
    exact rel_env T₁.env T₂.env hV [] (by agree_ppc []) hk

end VG.Proof.AesOcb.PPC64LE
