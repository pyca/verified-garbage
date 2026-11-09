module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: correctness

After the call (`AfterCall`), the status is kept in the frame, `encode`
writes the encoding of the hash value to `EM₂`, and the result is whether it
is `EM₁` (`compare`), masked with the status (`afterPub_ok`): if `pre` holds
the modulus' values, RFC 8017 §8.2.2 (`verifyId_true_iff`). As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/VerifyCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint)

/-! ## The specification -/

/-- Verification is RFC 8017 §8.2.2: the signature is `k` bytes, RSAVP1
succeeds and its result is the encoding of the hash value. -/
theorem verifyId_true_iff (nB eB H sig : List Byte) (x : Nat) :
    Spec.RsaPkcs1Sig.verifyId nB eB x H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, Spec.Rsa.publicOpChecked nB eB sig = some em ∧ encodeId x H nB.length = some em := by
  unfold Spec.RsaPkcs1Sig.verifyId encodeId
  cases hid : Spec.RsaPkcs1Sig.Hash.ofId x with
  | none => simp
  | some h => dsimp only; rw [Proof.RsaPkcs1Sig.verify_true]

/-- The hash function's number. -/
abbrev hid (s : State) : Nat := ((s.gpr .a4).setWidth 32).toNat

/-- What the function returns, from its entry state. -/
def verOut (s : State) : Bool :=
  Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (hid s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- The encoding of the hash value, from the entry state. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId (hid s) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (s.gpr .a1).toNat

theorem verOut_eq {s : State} (hsig : stackArg s 0 = s.gpr .a1) :
    verOut s = match pubOut s, encOut s with
      | some em, some em' => em == em'
      | _, _ => false := by
  apply Bool.eq_iff_iff.mpr
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length, hsig]
  unfold pubOut encOut
  cases hp : Spec.Rsa.publicOpChecked _ _ _ <;> cases he : encodeId _ _ _ <;> simp <;> exact eq_comm

theorem verOut_len {s : State} (h : stackArg s 0 ≠ s.gpr .a1) : verOut s = false := by
  apply Bool.eq_false_iff.mpr
  intro hv
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length] at hv
  exact h (BitVec.eq_of_toNat_eq hv.1)

theorem encodeId_length {x : Nat} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-! ## The steps -/

theorem ite01 (c : Prop) [Decidable c] : (if c then (1 : BitVec 64) else 0).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem ret0_ok (t : State) : WP isa (.block ret0) t fun w => Only [.a0] t w ∧ w.gpr .a0 = 0 :=
  wp_li (imm := 0) (by decide) fun w o e => wp_nil ⟨o, by rw [e]; rfl⟩

theorem mask_ok {s y : State} (hp : PreV s) {st : BitVec 64} (b : Bool) (hm : VMid s y)
    (hst : y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st) (hr : y.gpr .a0 = if b then 1 else 0) :
    WP isa (.seq (.block mask) (.block restore)) y fun w => abiPreserved s (freed frameBytes w) ∧
      w.gpr .a0 = (if b then 1 else 0) &&& st := by
  have hfa := fb_al hp.spal hp.sp1
  unfold mask
  refine WP.seq (wp_addSp fun y₁ o₁ e₁ => ?_)
  rw [hm.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by decide)) fun y₂ o₂ e₂ =>
    wp_and fun y₃ o₃ e₃ => wp_nil ?_
  refine WP.mono (restore_ok (hm.only (o₁.trans (o₂.trans o₃))).saves (by omega)) fun w ⟨habi, h3, _⟩ =>
    ⟨habi, ?_⟩
  rw [h3, e₃, o₂.get .a0, o₁.get .a0, hr, e₂, o₁.mem, hst]

/-- The result: the padding check's, masked with the status. -/
theorem final_eq {s t : State} (hsig : stackArg s 0 = s.gpr .a1) (b : Bool)
    (hb : b = match encOut s with
      | some em' => Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat == em'
      | none => false)
    (hres : Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat ((t.gpr .a0).setWidth 32)
      (pubOut s)) :
    ((if b then (1 : BitVec 64) else 0) &&& t.gpr .a0).setWidth 32 = if verOut s then 1 else 0 := by
  rw [BitVec.setWidth_and, ite01, verOut_eq hsig, hb]
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hres
    rw [hres.1]
    cases encOut s <;> simp
  | some em =>
    rw [hpo] at hres
    rw [hres.1, hres.2]
    cases encOut s with
    | none => simp
    | some em' => by_cases h : em = em' <;> simp [h]

/-- The result of the function, if `pre` holds the modulus' values, and the
calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → (s'.gpr .a0).setWidth 32 = if verOut s then 1 else 0)

/-- After the call: the status kept, the padding check, the mask and the
restores. -/
theorem afterPub_ok {s t : State} (hp : PreV s) (hsig : stackArg s 0 = s.gpr .a1) (ha : AfterCall s t) :
    WP isa (.seq (.block encArgs) (.seq encode (.seq tail (.seq (.block mask) (.block restore))))) t
      fun w => Post s (freed frameBytes w) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  unfold encArgs
  refine WP.seq (wp_addSp fun u₁ o₁ e₁ => ?_)
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_sd (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide)) fun u₂ m₂ => ?_
  refine wp_addi (imm := oEM2) fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ =>
    wp_mov fun u₆ o₆ e₆ => wp_mov fun u₇ o₇ e₇ => wp_nil ?_
  have fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₂ : VMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  have O₇ : Only [.a1, .a2, .a3, .a4, .a5] u₂ u₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  have mid₇ : VMid s u₇ := mid₂.only O₇
  have r4₇ : u₇.gpr .a1 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, e₃, m₂.gpr, e₁]
  have r5₇ : u₇.gpr .a2 = s.gpr .a1 := by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, e₄, o₃.get .s1, mid₂.s1]
  have r6₇ : u₇.gpr .a3 = zx (s.gpr .a4) := by
    rw [o₇.get .a3, o₆.get .a3, e₅, o₄.get .s2, o₃.get .s2, mid₂.s2]
  have r7₇ : u₇.gpr .a4 = s.gpr .a5 := by rw [o₇.get .a4, e₆, o₅.get .s3, o₄.get .s3, o₃.get .s3, mid₂.s3]
  have r8₇ : u₇.gpr .a5 = s.gpr .a6 := by rw [e₇, o₆.get .s4, o₅.get .s4, o₄.get .s4, o₃.get .s4, mid₂.s4]
  have slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .a0]
  have hd1 : (em1R s).Disjoint ⟨fb s + BitVec.ofNat 64 oSt, 8⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega_arith) (by decide)
  have em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂ hd1 (by dsimp only; omega_arith)
  have hdk : (dR s).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, (s.gpr .a1).toNat⟩ :=
    (hp.kd.sub_left (frame_sub s (by unfold oEM2 frameBytes; omega_arith))).symm
  have hpre : EPre u₇ (hid s) (s.gpr .a1).toNat := {
    r6 := by rw [r6₇, zx_toNat]
    hk := by rw [r5₇]
    kle := hk2
    buf := fun i hi => by
      rw [mid₇.wr, r4₇, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr s _ (by unfold oEM2 frameBytes; omega_arith)
    rd := fun j hj => by
      rw [r8₇] at hj
      rw [mid₇.rd, r7₇]
      exact ⟨dR s, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by have := hp.wd; omega_arith)⟩
    sep := fun j hj i hi => by
      rw [r8₇] at hj
      rw [r7₇, r4₇]
      exact ne_of_disjoint hdk (by have := hp.wd; omega_arith) (by omega_arith) hj hi }
  have hH : Spec.Rsa.bytesAt u₇.mem (u₇.gpr .a4) (u₇.gpr .a5).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat := by
    rw [r7₇, r8₇, bytes_of_frame mid₇.mem hp.kd hp.ds.symm (by have := hp.wd; omega_arith)]
  refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
  rw [hH] at hout
  change EOut u₇ w (encOut s) at hout
  have hfin : ∀ y : State, ∀ b : Bool, VMid s y → y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 →
      y.gpr .a0 = (if b then 1 else 0) →
      (b = match encOut s with
        | some em' => Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat == em'
        | none => false) →
      WP isa (.seq (.block mask) (.block restore)) y fun w => Post s (freed frameBytes w) :=
    fun y b hy hst hr hb => WP.mono (mask_ok hp b hy hst hr) fun w ⟨habi, h3⟩ => ⟨habi, fun hc => by
      show (w.gpr .a0).setWidth 32 = _
      rw [h3]; exact final_eq hsig b hb (ha.res hc)⟩
  refine WP.seq ?_
  unfold tail
  cases heo : encOut s with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hme⟩ := hout
    refine WP.ite true ((eval_zero w .a0).trans (by rw [h0]; rfl)) (fun _ => WP.mono (ret0_ok w) fun y ⟨o, e⟩ =>
      hfin y false ((mid₇.frameW1 hK hp.ks (e := oEM2) (n := 1024) (by decide) (by decide)
        (by rw [hme]; exact Frame.refl _ _)).only o)
        (by rw [o.mem, hme, O₇.mem, slot₂]) (by rw [e]; rfl) (by rw [heo])) (by simp)
  | some em' =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero w .a0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    have hl' : em'.length = (s.gpr .a1).toNat := encodeId_length heo
    have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₇.mem w.mem := by
      rw [hme, r4₇]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    have midw : VMid s w := mid₇.frameW1 hK hp.ks (by decide) (by decide) fw
    have slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), O₇.mem, slot₂]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi (imm := oEM1) fun v₂ p₂ f₂ =>
      wp_addi (imm := oEM2) fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    have P₄ : Only [.t0, .a1, .a2, .a3] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    have midv : VMid s v₄ := midw.only P₄
    have x4 : v₄.gpr .a1 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .a1, p₃.get .a1, f₂, f₁]
    have x5 : v₄.gpr .a2 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .a2, f₃, p₂.get .t0, f₁]
    have x6 : v₄.gpr .a3 = BitVec.ofNat 64 (s.gpr .a1).toNat := by
      rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, midw.s1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hin : ∀ {d : Nat}, d + (s.gpr .a1).toNat ≤ frameBytes → ∀ j < (s.gpr .a1).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun hd j hj => by
      rw [midv.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr' s _ _ (by omega_arith)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .a1).toNat) (by omega_arith) (by omega_arith) x6
      (fun j hj => by rw [x4]; exact hin (by unfold oEM1 frameBytes; omega_arith) j hj)
      (fun j hj => by rw [x5]; exact hin (by unfold oEM2 frameBytes; omega_arith) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    unfold result
    refine wp_subi (imm := 1) fun z₁ q₁ g₁ => wp_srl fun z₂ q₂ g₂ => wp_nil ?_
    have hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat := by
      rw [P₄.mem, hme, r4₇, O₇.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega_arith)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith)
        (by unfold oEM2; omega_arith)
    have hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .a1).toNat = em' := by
      rw [P₄.mem, hme, r4₇, ← hl', bytesAt_writeBytes _ _ _ (by omega_arith)]
    rw [x4, x5, hb1, hb2] at hiff
    refine hfin z₂ (Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat == em')
      (((midv.only oy).only q₁).only q₂) (by rw [q₂.mem, q₁.mem, oy.mem, P₄.mem, slotw]) ?_ (by rw [heo])
    rw [g₂, g₁, borrow1 hlt]
    by_cases h : y.gpr .t4 = 0
    · rw [ite_eq_left h, ite_eq_left (beq_iff_eq.mpr (hiff.mp h))]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr (beq_iff_eq.mp h')))]

/-! ## The whole function -/

theorem lenCheck_ok {s : State} (hp : PreV s) :
    WP isa (.block (lenCheck .a1)) s fun t₁ => Only [.t0] s t₁ ∧ t₁.gpr .t0 = stackArg s 0 - s.gpr .a1 := by
  refine wp_addSp fun t₀ o₀ e₀ => wp_ld (a := stackArgAddr s 0) (by rw [e₀, BitVec.add_zero]; rfl)
    (arg_al hp.spal 0) (by rw [o₀.rd, o₀.wr]; exact arg_rd hp _ (by decide)) fun t₁ o₁ e₁ =>
    wp_sub fun t₂ o₂ e₂ => wp_nil ⟨(o₀.trans (o₁.trans o₂)).mono, ?_⟩
  rw [e₂, e₁, o₁.get .a1, o₀.get .a1, o₀.mem]; rfl

theorem eval_len {s t : State} (e : t.gpr .t0 = stackArg s 0 - s.gpr .a1) :
    isa.eval (.nonzero .t0) t = some (decide (stackArg s 0 ≠ s.gpr .a1)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .a1).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega_arith
  · apply BitVec.eq_of_toNat_eq; omega_arith

theorem code_ok {s : State} (hp : PreV s) : WP isa code s (Post s) := by
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .a1
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.allocLe (by decide) (by rw [o₁.sp]; exact hp.sp1) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by show t₁.sp - _ = _; rw [o₁.sp])
      (by show (⟨t₁.sp - _, _⟩ :: t₁.wr) = _; rw [o₁.sp, o₁.wr])
      (by show t₁.rd = _; rw [o₁.rd])
      (by show Frame _ _ t₁.mem; rw [o₁.mem]; exact Frame.refl _ _)
      (fun r hr => o₁.gpr r hr)) fun t₂ h₂ => ?_)
    exact WP.seq (WP.mono (call_ok hp h₂ hsig) fun t₃ h₃ => afterPub_ok hp hsig h₃)
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (ret0_ok t₁) fun w ⟨o, e⟩ =>
      ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun _ => ?_⟩) (by simp)
    · exact (o₁.trans o).gpr r (by revert r; decide)
    · rw [o.sp, o₁.sp]
    · exact (o₁.trans o).gpr .ra (by decide)
    · rw [e, verOut_len hsig]; rfl

/-- The correctness of `vg_rsa_pkcs1_verify_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preV_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver
