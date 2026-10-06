import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-!
# `vg_rsa_pkcs1_verify` on AArch64: correctness

After the call (`AfterCall`), the padding check (`afterPub_ok`): if RSAVP1
failed, 0; otherwise `encode` writes the encoding of the hash value to
`EM₂`, and the result is whether it is `EM₁` (`compare`), which is
RFC 8017 §8.2.2 (`verifyId_true_iff`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_subImm wp_lsr eval_nonzero ne_zero_iff)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov EPre EPost EOut encodeId encode_ok compare_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint)

/-! ## The specification -/

/-- Verification is RFC 8017 §8.2.2: the signature is `k` bytes, RSAVP1
succeeds and its result is the encoding of the hash value. -/
theorem verifyId_true_iff (nB eB H sig : List Byte) (x : BitVec 32) :
    Spec.RsaPkcs1Sig.verifyId nB eB x.toNat H sig = true ↔
      sig.length = nB.length ∧
        ∃ em, Spec.Rsa.publicOpChecked nB eB sig = some em ∧ encodeId x H nB.length = some em := by
  unfold Spec.RsaPkcs1Sig.verifyId encodeId
  cases hid : Spec.RsaPkcs1Sig.Hash.ofId x.toNat with
  | none => simp
  | some h => dsimp only; rw [Proof.RsaPkcs1Sig.verify_eq_verifyRfc, Proof.RsaPkcs1Sig.verifyRfc_true]

/-- What the function returns, from its entry state. -/
def verOut (s : State) : Bool :=
  Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((s.gpr .x4).setWidth 32).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- The encoding of the hash value, from the entry state. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .x4).setWidth 32) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) (s.gpr .x1).toNat

theorem verOut_eq {s : State} (hsig : stackArg s 0 = s.gpr .x1) :
    verOut s = match pubOut s, encOut s with
      | some em, some em' => em == em'
      | _, _ => false := by
  apply Bool.eq_iff_iff.mpr
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length, hsig]
  unfold pubOut encOut
  cases hp : Spec.Rsa.publicOpChecked _ _ _ <;> cases he : encodeId _ _ _ <;> simp <;> exact eq_comm

/-! ## The steps -/

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`. -/
theorem Mid.only {K : Nat} {s t w : State} {rs : List Reg} (h : Mid K s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid K s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x19
  x20 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x20
  x21 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x21
  x22 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x22
  hi := fun r hr => (o.gpr _ fun h' => hrs _ h' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h])).trans (h.hi r hr)
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  mem := by rw [o.mem]; exact h.mem
  sv := by rw [o.mem]; exact h.sv

theorem ret0_ok (t : State) : WP isa ret0 t fun w => Only [.x0] t w ∧ w.gpr .x0 = 0 :=
  wp_movz fun w o e => wp_nil ⟨o, by rw [e]; rfl⟩

theorem Only.of_keep {rs : List Reg} {t w : State} (k : Keep rs t w) (hm : w.mem = t.mem) : Only rs t w :=
  ⟨k.gpr, hm, k.rd, k.wr, k.sp, k.vcs⟩

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`
and memory within `EM₂`. -/
theorem Mid.em2 {K : Nat} {s t w : State} {rs : List Reg} (h : Mid K s t) (o : Keep rs t w)
    (hm : Frame [⟨fb s + BitVec.ofNat 64 oEM2, 1024⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid K s w :=
  have hw : Mid K s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    mem := h.mem.trans (hm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub K s (by decide)⟩)
    sv := h.sv.frame_in saved_offs hm fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by decide) (by decide) (by decide) }

theorem encodeId_length {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- The borrow of `x - 1`, for `x < 256`: whether `x` is 0. -/
theorem borrow1 {x : BitVec 64} (h : x.toNat < 256) :
    ((x - BitVec.ofNat 64 1) >>> 63).setWidth 32 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub]
    simp; omega

theorem eval_zero' (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem afterPub_ok {K : Nat} {s t : State} (hp : PreV K s) (hsig : stackArg s 0 = s.gpr .x1)
    (ha : AfterCall K s t) :
    WP isa afterPub t fun w => Mid K s w ∧ (w.gpr .x0).setWidth 32 = if verOut s then 1 else 0 := by
  rw [verOut_eq hsig]
  have hres := ha.res
  have hk1 := hp.k1; have hk2 := hp.k2
  unfold afterPub
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hres
    obtain ⟨hr, -⟩ := hres
    refine WP.ite true (by simp [eval, State.read, hr]) (fun _ => WP.mono (ret0_ok t) fun w ⟨o, e⟩ =>
      ⟨ha.toMid.only o, by rw [e]; rfl⟩) (by simp)
  | some em =>
    rw [hpo] at hres
    obtain ⟨hr, hem⟩ := hres
    refine WP.ite false (by simp [eval, State.read, hr]) (by simp) fun _ => ?_
    unfold encArgs
    refine WP.seq (wp_addSp (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
      wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_nil ?_)
    have O₅ : Only [.x8, .x9, .x10, .x11, .x12] t u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    have x8 : u₅.gpr .x8 = fb s + BitVec.ofNat 64 oEM2 := by
      rw [o₅.get .x8, o₄.get .x8, o₃.get .x8, o₂.get .x8, e₁, ha.sp]
    have x9 : u₅.gpr .x9 = s.gpr .x1 := by
      rw [o₅.get .x9, o₄.get .x9, o₃.get .x9, e₂, o₁.get .x19, ha.x19]
    have x10 : u₅.gpr .x10 = s.gpr .x4 := by
      rw [o₅.get .x10, o₄.get .x10, e₃, o₂.get .x20, o₁.get .x20, ha.x20]
    have x11 : u₅.gpr .x11 = s.gpr .x5 := by
      rw [o₅.get .x11, e₄, o₃.get .x21, o₂.get .x21, o₁.get .x21, ha.x21]
    have x12 : u₅.gpr .x12 = s.gpr .x6 := by
      rw [e₅, o₄.get .x22, o₃.get .x22, o₂.get .x22, o₁.get .x22, ha.x22]
    have mid₅ : Mid K s u₅ := ha.toMid.only O₅
    have hdk : (dR s).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, (s.gpr .x1).toNat⟩ :=
      (hp.kd.sub_left (frame_sub K s (by unfold oEM2 frameBytes; omega))).symm
    have hpre : EPre u₅ ((s.gpr .x4).setWidth 32) (s.gpr .x1).toNat := {
      x10 := by rw [x10]
      hk := by rw [x9]
      kle := hk2
      buf := fun i hi => by
        rw [mid₅.wr, x8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact in_frame _ _ (by unfold oEM2 frameBytes; omega)
      rd := fun j hj => by
        rw [mid₅.rd, x11]
        exact ⟨dR s, List.mem_append_left _ (by rw [hp.hrd]; simp),
          Offset.contains_base _ (by rw [x12] at hj; omega) (by have := hp.wd; omega)⟩
      sep := fun j hj i hi => by
        rw [x11, x8]
        exact ne_of_disjoint hdk (by have := hp.wd; omega) (by omega) (by rw [x12] at hj; exact hj) hi }
    have hH : Spec.Rsa.bytesAt u₅.mem (u₅.gpr .x11) (u₅.gpr .x12).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat := by
      rw [x11, x12, bytes_of_frame mid₅.mem hp.kd hp.ds.symm (by have := hp.wd; omega)]
    refine WP.seq (WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_)
    rw [hH] at hout
    change EOut u₅ w (encOut s) at hout
    unfold tail
    cases heo : encOut s with
    | none =>
      rw [heo] at hout
      obtain ⟨h0, hm⟩ := hout
      refine WP.ite true ((eval_zero' w .x0).trans (by rw [h0]; rfl)) (fun _ => WP.mono (ret0_ok w) fun w' ⟨o, e⟩ =>
        ⟨(mid₅.only (Only.of_keep hK hm)).only o, by rw [e]; rfl⟩) (by simp)
    | some em' =>
      rw [heo] at hout
      obtain ⟨h1, hm⟩ := hout
      refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
      have hl' : em'.length = (s.gpr .x1).toNat := encodeId_length heo
      have midw : Mid K s w := mid₅.em2 hK (by
        rw [hm, x8]
        exact (frame_writeBytes _ _ _).sub fun r hr => by
          rw [List.mem_singleton.mp hr, hl']; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix hk2⟩)
      unfold cmpArgs
      refine WP.seq (wp_addSp (by decide) fun v₁ p₁ f₁ => wp_addSp (by decide) fun v₂ p₂ f₂ =>
        wp_mov fun v₃ p₃ f₃ => wp_nil ?_)
      have P₃ : Only [.x14, .x15, .x13] w v₃ := (p₁.trans (p₂.trans p₃)).mono
      have midv : Mid K s v₃ := midw.only P₃
      have x14 : v₃.gpr .x14 = fb s + BitVec.ofNat 64 oEM1 := by
        rw [p₃.get .x14, p₂.get .x14, f₁, ← midw.sp]
      have x15 : v₃.gpr .x15 = fb s + BitVec.ofNat 64 oEM2 := by
        rw [p₃.get .x15, f₂, p₁.sp, ← midw.sp]
      have x13 : v₃.gpr .x13 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
        rw [f₃, p₂.get .x19, p₁.get .x19, midw.x19, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hin : ∀ {d : Nat}, d + (s.gpr .x1).toNat ≤ frameBytes → ∀ j < (s.gpr .x1).toNat,
          InRegions (v₃.rd ++ v₃.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun hd j hj => by
        rw [midv.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact InRegions_append_cons (xs := v₃.rd) |>.mpr (.inl (by
          exact (Offset.contains_base _ (by omega) (by unfold frameBytes at hd; omega))))
      refine WP.seq (WP.mono (compare_ok (s := v₃) (n := (s.gpr .x1).toNat) (by omega) (by omega) x13
        (fun j hj => by rw [x14]; exact hin (by unfold oEM1 frameBytes; omega) j hj)
        (fun j hj => by rw [x15]; exact hin (by unfold oEM2 frameBytes; omega) j hj)) fun y ⟨oy, hiff, hlt⟩ => ?_)
      refine wp_subImm (by decide) fun z₁ q₁ g₁ => wp_lsr (by decide) fun z₂ q₂ g₂ => wp_nil
        ⟨(midv.only oy).only (q₁.trans q₂), ?_⟩
      rw [g₂, g₁]
      have hb1 : Spec.Rsa.bytesAt v₃.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x1).toNat = em := by
        rw [P₃.mem, hm, x8, ← hem, ← O₅.mem]
        simp only [Spec.Rsa.bytesAt]
        refine List.map_congr_left fun i hi => (frame_writeBytes _ _ _).bytes
          (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x1).toNat⟩) (fun r hr => ?_) (by dsimp only; omega)
          (List.mem_range.mp hi)
        rw [List.mem_singleton.mp hr, hl']
        exact Offset.disjoint _ (by unfold oEM1 oEM2; omega) (by unfold oEM1; omega) (by unfold oEM2; omega)
      have hb2 : Spec.Rsa.bytesAt v₃.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x1).toNat = em' := by
        rw [P₃.mem, hm, x8, ← hl', bytesAt_writeBytes _ _ _ (by omega)]
      rw [x14, x15, hb1, hb2] at hiff
      rw [borrow1 hlt]
      by_cases he : em = em'
      · simp [he, hiff.mpr he]
      · have : ¬ y.gpr .x12 = 0 := fun h => he (hiff.mp h)
        simp [he]; exact this

/-! ## The restores, and the whole function -/

/-- The restores, then the frame's release: the caller's registers are back,
and `x0` is kept. -/
theorem restore_ok {K : Nat} {s w : State} (hm : Mid K s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hm.wr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega) (by have := saved_offs p hp'; omega))))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_⟩
  · simp only [freed]
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact hr.gpr p hp'
    · have hr'' : r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | decide | simp_all [saved]
      have h16 : r ∉ [Reg.x16] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'' ⊢
        rcases hr'' with h | h | h | h | h | h <;> subst h <;> decide
      rw [hr.other r hs, o₁.gpr r h16]
      exact hm.hi r hr''
  · simp only [freed]
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hm.v r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]

/-- `vg_rsa_pkcs1_verify`'s result, and the calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (s'.gpr .x0).setWidth 32 = if verOut s then 1 else 0

theorem verOut_len {s : State} (h : stackArg s 0 ≠ s.gpr .x1) : verOut s = false := by
  apply Bool.eq_false_iff.mpr
  intro hv
  rw [verOut, verifyId_true_iff, bytesAt_length, bytesAt_length] at hv
  exact h (BitVec.eq_of_toNat_eq hv.1)

theorem code_ok (c : PubChecked) {s : State} (hp : PreV c.stack s) :
    WP isa (code c.name c.code) s (Post s) := by
  unfold code lenCheck
  have blk : WP isa (.block [.ldrSp .x8 0, .sub .x .x8 .x8 .x1]) s fun t₁ => Only [.x8] s t₁ ∧
      t₁.gpr .x8 = stackArg s 0 - s.gpr .x1 := by
    refine VG.Proof.RsaPkcs1Sig.AArch64.wp_ldrSp (by decide) ?_ fun t₀ o₀ e₀ =>
      VG.Proof.MlKem.AArch64.wp_sub fun t₁ o₁ e₁ => wp_nil ⟨(o₀.trans o₁).mono, ?_⟩
    · have h := arg_in (s := s) (j := 0) (rs := s.rd ++ s.wr) hp (Covers.left (Covers.refl _)) (by decide)
      simpa [stackArgAddr] using h
    · rw [e₁, e₀, o₀.get .x1, BitVec.add_zero, ← sa0 s]; rfl
  refine WP.seq (WP.mono blk fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne : isa.eval (.nonzero .x .x8) t₁ = some (decide (stackArg s 0 ≠ s.gpr .x1)) := by
    rw [eval_nonzero, e₁, ne_zero_iff, BitVec.toNat_sub]
    have := (stackArg s 0).isLt; have := (s.gpr .x1).isLt
    refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
    · rw [e] at h; omega
    · apply BitVec.eq_of_toNat_eq; omega
  by_cases hsig : stackArg s 0 = s.gpr .x1
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; have := hp.sp1; unfold stk at this; omega) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by simp [allocated, o₁.sp]) (by simp [allocated, o₁.rd])
      (by simp [allocated, o₁.sp, o₁.wr]) (by simp [allocated, o₁.mem]) (fun r hr => by
        simp only [allocated]; exact o₁.gpr r (by simpa using hr)) (fun r hr => o₁.vcs r hr))
      fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (call_ok c hp h₂ hsig) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (afterPub_ok hp hsig h₃) fun t₄ ⟨m₄, r₄⟩ => ?_)
    exact WP.mono (restore_ok m₄) fun w ⟨habi, hx0⟩ => ⟨habi, by rw [hx0]; exact r₄⟩
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (ret0_ok t₁) fun w ⟨o, e⟩ =>
      ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩) (by simp)
    · have h8 : r ∉ [Reg.x8] ++ [Reg.x0] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      exact (o₁.trans o).gpr r h8
    · rw [o.sp, o₁.sp]
    · rw [o.vcs r hr, o₁.vcs r hr]
    · rw [e, verOut_len hsig]; rfl

end VG.Proof.RsaPkcs1Sig.AArch64.Ver
