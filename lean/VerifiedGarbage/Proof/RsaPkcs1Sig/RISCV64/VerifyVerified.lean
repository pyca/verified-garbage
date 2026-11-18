module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-! ### `RsaPkcs1Sig.RISCV64.VerifyCorrect`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: correctness

After the call (`AfterCall`), the status is kept in the frame, `encode`
writes the encoding of the hash value to `EM₂`, and the result is whether it
is `EM₁` (`compare`), masked with the status (`afterPub_ok`): if `pre` holds
the modulus' values, RFC 8017 §8.2.2 (`verifyId_true_iff`). As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/VerifyVerified.lean`).
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
  obtain hfa := fb_al hp.spal hp.sp1
  unfold mask
  refine WP.seq (wp_addSp fun y₁ o₁ e₁ => ?_)
  rw [hm.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by decide)) fun y₂ o₂ e₂ =>
    wp_and fun y₃ o₃ e₃ => wp_nil ?_
  refine WP.mono (restore_ok (hm.only (o₁.trans (o₂.trans o₃))).saves (by omega_using [hfa])) fun w ⟨habi, h3, _⟩ =>
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
  obtain hk1 := hp.k1; have hk2 := hp.k2
  unfold encArgs
  refine WP.seq (wp_addSp fun u₁ o₁ e₁ => ?_)
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_sd (a := fb s + BitVec.ofNat 64 oSt) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.wr, ha.wr]; exact in_fr s _ (by decide)) fun u₂ m₂ => ?_
  refine wp_addi (imm := oEM2) fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ =>
    wp_mov fun u₆ o₆ e₆ => wp_mov fun u₇ o₇ e₇ => wp_nil ?_
  obtain fr₂ : Frame [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem u₂.mem := by
    rw [m₂.mem, o₁.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain mid₂ : VMid s u₂ := ha.toMid.frameW1 (o₁.keep.trans m₂.keep) hp.ks (by decide) (by decide) fr₂
  obtain O₇ : Only [.a1, .a2, .a3, .a4, .a5] u₂ u₇ := (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  obtain mid₇ : VMid s u₇ := mid₂.only O₇
  obtain r4₇ : u₇.gpr .a1 = fb s + BitVec.ofNat 64 oEM2 := by
    rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, e₃, m₂.gpr, e₁]
  obtain r5₇ : u₇.gpr .a2 = s.gpr .a1 := by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, e₄, o₃.get .s1, mid₂.s1]
  obtain r6₇ : u₇.gpr .a3 = zx (s.gpr .a4) := by
    rw [o₇.get .a3, o₆.get .a3, e₅, o₄.get .s2, o₃.get .s2, mid₂.s2]
  obtain r7₇ : u₇.gpr .a4 = s.gpr .a5 := by rw [o₇.get .a4, e₆, o₅.get .s3, o₄.get .s3, o₃.get .s3, mid₂.s3]
  obtain r8₇ : u₇.gpr .a5 = s.gpr .a6 := by rw [e₇, o₆.get .s4, o₅.get .s4, o₄.get .s4, o₃.get .s4, mid₂.s4]
  obtain slot₂ : u₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
    rw [m₂.mem, Mem.readW_writeW_self64, o₁.get .a0]
  obtain hd1 : (em1R s).Disjoint ⟨fb s + BitVec.ofNat 64 oSt, 8⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by unfold oEM1; omega_arith) (by decide)
  obtain em1₂ : Spec.Rsa.bytesAt u₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat :=
    Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) fr₂ hd1 (by dsimp only; omega_arith)
  obtain hdk : (dR s).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, (s.gpr .a1).toNat⟩ :=
    (hp.kd.sub_left (frame_sub s (by unfold oEM2 frameBytes; omega_arith))).symm
  obtain hpre : EPre u₇ (hid s) (s.gpr .a1).toNat := {
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
  obtain hH : Spec.Rsa.bytesAt u₇.mem (u₇.gpr .a4) (u₇.gpr .a5).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat := by
    rw [r7₇, r8₇, bytes_of_frame mid₇.mem hp.kd hp.ds.symm (by have := hp.wd; omega_arith)]
  refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
  rw [hH] at hout
  change EOut u₇ w (encOut s) at hout
  obtain hfin : ∀ y : State, ∀ b : Bool, VMid s y → y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 →
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
    obtain hl' : em'.length = (s.gpr .a1).toNat := encodeId_length heo
    obtain fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] u₇.mem w.mem := by
      rw [hme, r4₇]
      exact (frame_writeBytes _ _ _).sub fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩
    obtain midw : VMid s w := mid₇.frameW1 hK hp.ks (by decide) (by decide) fw
    obtain slotw : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .a0 := by
      rw [fw.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)) (by decide), O₇.mem, slot₂]
    unfold cmpArgs
    refine WP.seq (wp_addSp fun v₁ p₁ f₁ => wp_addi (imm := oEM1) fun v₂ p₂ f₂ =>
      wp_addi (imm := oEM2) fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_)
    rw [midw.sp, BitVec.add_zero] at f₁
    obtain P₄ : Only [.t0, .a1, .a2, .a3] w v₄ := p₁.trans (p₂.trans (p₃.trans p₄))
    obtain midv : VMid s v₄ := midw.only P₄
    obtain x4 : v₄.gpr .a1 = fb s + BitVec.ofNat 64 oEM1 := by rw [p₄.get .a1, p₃.get .a1, f₂, f₁]
    obtain x5 : v₄.gpr .a2 = fb s + BitVec.ofNat 64 oEM2 := by rw [p₄.get .a2, f₃, p₂.get .t0, f₁]
    obtain x6 : v₄.gpr .a3 = BitVec.ofNat 64 (s.gpr .a1).toNat := by
      rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, midw.s1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    obtain hin : ∀ {d : Nat}, d + (s.gpr .a1).toNat ≤ frameBytes → ∀ j < (s.gpr .a1).toNat,
        InRegions (v₄.rd ++ v₄.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun hd j hj => by
      rw [midv.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_fr' s _ _ (by omega_arith)
    refine WP.seq (WP.mono (compare_ok (s := v₄) (n := (s.gpr .a1).toNat) (by omega_arith) (by omega_arith) x6
      (fun j hj => by rw [x4]; exact hin (by unfold oEM1 frameBytes; omega_arith) j hj)
      (fun j hj => by rw [x5]; exact hin (by unfold oEM2 frameBytes; omega_arith) j hj))
      fun y ⟨oy, hiff, hlt⟩ => ?_)
    unfold result
    refine wp_subi (imm := 1) fun z₁ q₁ g₁ => wp_srl fun z₂ q₂ g₂ => wp_nil ?_
    obtain hb1 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat := by
      rw [P₄.mem, hme, r4₇, O₇.mem, ← em1₂]
      refine Proof.RsaPkcs1Sig.bytes_apart (R := em1R s) (frame_writeBytes _ _ _) ?_ (by dsimp only; omega_arith)
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1; omega_arith)
        (by unfold oEM2; omega_arith)
    obtain hb2 : Spec.Rsa.bytesAt v₄.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .a1).toNat = em' := by
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
  obtain hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .a1
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.allocLe (by decide) (by rw [o₁.sp]; exact hp.sp1) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by show t₁.sp - _ = _; rw [o₁.sp])
      (by show (⟨t₁.sp - _, _⟩ :: t₁.wr) = _; rw [o₁.sp, o₁.wr])
      (by show t₁.rd = _; rw [o₁.rd])
      (by show Frame _ _ t₁.mem; rw [o₁.mem]; exact Frame.refl _ _)
      (fun r hr => o₁.gpr r hr)) fun t₂ h₂ => ?_)
    -- The postcondition reads none of the memory, so the bytes the `free` loses do not matter.
    exact WP.seq (WP.mono (call_ok hp h₂ hsig) fun t₃ h₃ => WP.mono (afterPub_ok hp hsig h₃)
      fun w h _ _ _ => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2⟩)
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

end

end

/-! ### `RsaPkcs1Sig.RISCV64.VerifyCT`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: the taint checks

The code between the call and the branches, checked by the taint analysis
from the stack pointer and, after the call, the registers holding `k`, the
zero-extended `hash`, `digest` and `digest_len` (`s1`–`s4`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (lenCheck .a1)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ret0_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block ret0) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint (h : Pins Φ [.s1, .s2, .s3, .s4]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode (.seq tail (.seq (.block mask) (.block restore)))))
      fun _ _ => True :=
  two_taint [.s1, .s2, .s3, .s4] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver

end

end

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: `Verified`

Correctness (`code_correct`), constant time (`code_ct`: the code between
the call and the branches checked by the taint analysis, from the stack
pointer and the registers holding public values; the call of
`vg_rsa_public_precomputed_checked` by its contract, `pdCallCT`; the length
check's branch, on public lengths) and a state meeting the precondition.
As on PPC64LE (`Proof/RsaPkcs1Sig/PPC64LE/VerifyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, `hash`, the bytes of `n`, `e`, the hash value and the
signature, and the precomputed values. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a5, .a6, .a7], s.gpr r = a.gpr r
  h4 : (s.gpr .a4).setWidth 32 = (a.gpr .a4).setWidth 32
  args : ∀ i < 5, stackArg s i = stackArg a i
  be : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem leak_eqW {a b c d a' b' c' d' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length) (hc : c.length = c'.length) (hd : d.length = d'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) ++ w.map (·.toNat) =
      (a' ++ b' ++ c' ++ d').map (·.toNat) ++ w'.map (·.toNat)) :
    b = b' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb, hc, hd])
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  obtain ⟨h₃, -⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₄, -⟩ := List.append_inj h₃ (by simp [ha, hb])
  obtain ⟨-, e⟩ := List.append_inj h₄ ha
  exact ⟨e, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubV_of {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi S).pub s₁ s₂) : PubV s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨he, hw⟩ := leak_eqW (by simp [bytesAt_length, h4]) (by simp [bytesAt_length, h6])
    (by simp [bytesAt_length, h9]) (by simp [bytesAt_length, a0]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h7.symm, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := PreV s ∧ PubV a s

/-! ## Constant time -/

theorem fb_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by
  simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg}
    (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a5, .a6, .a7] := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 5 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

/-- Two calls of `vg_rsa_public_precomputed_checked` from `AtCall` agree on
what the callee may leak. -/
theorem call_ct :
    RelCT isa (Two fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AtCall s t) pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pdOk_of h₁.1 c₁ g₁,
    pdOk_of h₂.1 c₂ g₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, fb_eq h₁ h₂]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, fb_eq h₁ h₂]
    · rw [c₁.g1, c₂.g1, gpr_eq h₁ h₂]
    · rw [c₁.g2, c₂.g2, arg_eq h₁ h₂]
    · rw [c₁.g3, c₂.g3, arg_eq h₁ h₂]
    · rw [c₁.g4, c₂.g4, gpr_eq h₁ h₂]
    · rw [c₁.g5, c₂.g5, gpr_eq h₁ h₂]
    · rw [c₁.g6, c₂.g6, gpr_eq h₁ h₂]
    · rw [c₁.g7, c₂.g7, gpr_eq h₁ h₂]
  · rw [c₁.sa0, c₂.sa0, arg_eq h₁ h₂]
  · rw [c₁.sa1, c₂.sa1, arg_eq h₁ h₂]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_of_frame c₁.mem h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame c₂.mem h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5, bytes_of_frame c₁.mem h₁.1.ke h₁.1.es.symm (by have := h₁.1.we; omega_using []),
      bytes_of_frame c₂.mem h₂.1.ke h₂.1.es.symm (by have := h₂.1.we; omega_using []), h₁.2.be, h₂.2.be]

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ Only [.t0] s t ∧
      t.gpr .t0 = stackArg s 0 - s.gpr .a1)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, arg_eq h₁ h₂ (i := 0), gpr_eq h₁ h₂ (r := .a1)])
    (ret0_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AtCall s t)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show u₁.sp - _ = u₂.sp - _; rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .a1 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_ok h.1 (by show t.sp - _ = _; rw [o.sp])
      (by show (⟨t.sp - _, _⟩ :: t.wr) = _; rw [o.sp, o.wr])
      (by show t.rd = _; rw [o.rd])
      (by show Frame _ _ t.mem; rw [o.mem]; exact Frame.refl _ _)
      (fun r hr => o.gpr r hr)) fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ stackArg s 0 = s.gpr .a1 ∧ AfterCall s t) call_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (call_ok h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine afterPub_taint fun _ _ _ ⟨s₁, h₁, _, a₁⟩ ⟨s₂, h₂, _, a₂⟩ => ⟨?_, fun r hr => ?_⟩
  · rw [a₁.sp, a₂.sp, fb_eq h₁ h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.s1, a₂.s1, gpr_eq h₁ h₂]
    · rw [a₁.s2, a₂.s2, zx, zx, h₁.2.h4, h₂.2.h4]
    · rw [a₁.s3, a₂.s3, gpr_eq h₁ h₂]
    · rw [a₁.s4, a₂.s4, gpr_eq h₁ h₂]

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preV_of h₁, ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl⟩⟩, preV_of h₂, pubV_of hp⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- A modulus of 64 bytes at `0x1000`, `e`, the hash value and the signature
of a byte each, 112 words of working space and 16 precomputed words; the
stack arguments at `sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 1 | .a5 => 0x3000 | .a6 => 1 | .a7 => 0x4000
    | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000000 then 1
    else bif Nat.beq a.toNat 0x1000000000A then 1 else bif Nat.beq a.toNat 0x10000000010 then 0x70
    else bif Nat.beq a.toNat 0x10000000019 then 0x50 else bif Nat.beq a.toNat 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 112 ∧
    stackArg satState 3 = 0x5000 ∧ stackArg satState 4 = 16 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : frameBytes = 2127 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, ha]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by unfold Spec.Rsa.lenValid; decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified RISCV64.target Precomputed.code
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver
