import VerifiedGarbage.Proof.AesOcb.AArch64.Seal
import VerifiedGarbage.Proof.AesOcb.AArch64.CmpMask

/-!
# AES-OCB on AArch64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`), the tag at
`W + t2O` (`tag`), its comparison with the received tag at `W` (`cmp`), the
mask of the data (`mask`), the result and `restore` (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W N A D R nl al n tl) (hW : stackArg s 0 = W) (htl : stackArg s 1 = BitVec.ofNat 64 tl)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (h2 : s.gpr .x2 = N)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 nl) (h4 : s.gpr .x4 = A) (h5 : s.gpr .x5 = BitVec.ofNat 64 al)
    (h6 : s.gpr .x6 = D) (h7 : s.gpr .x7 = BitVec.ofNat 64 n) :
    WP isa («open» (callees v)) s fun s' => GprAbi s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem W tl) with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  have hn := Ar.data.lt
  unfold «open»
  refine pre_wp v Ar hW htl h0 h1 h2 h3 h4 h5 h6 h7 fun s₃ P₃ => ?_
  have hD₃ : DBuf K W s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  have c₃ : ctxCiph s₃.mem K R = ctxCiph s.mem K R := ctxCiph_W L P₃.frame Ar.rounds
  have i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := ctxInv_W L P₃.frame Ar.rounds
  have l₃ : ctxLstar s₃.mem K = ctxLstar s.mem K := ctxLstar_W L P₃.frame
  have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := bytesAt_W Ar.data.w hn P₃.frame
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env Ar.rounds hD₃ P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, l₃]))
    fun s₄ B => ?_)
  have F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut B.frame
  have cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans c₃
  have ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.seq (WP.mono (tag_ok v L B.env Ar.rounds (.inr rfl)) fun s₅ T => ?_)
  have F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (by decide) T.frame
  have S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok T.env Ar.t1 Ar.t16 S₅.tl) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ := T.env.others g₆ sp₆ rd₆ wr₆
  have F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hD₆ : DBuf K W s₆ D n := hD₃.of_eq (rd₆.trans (T.rd.trans B.rd)) (wr₆.trans (T.wr.trans B.wr))
  let c : Bool := decide (bytesAt s₅.mem W tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ hD₆ (c := c)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨g₇, sp₇, rd₇, wr₇, m₇⟩ => ?_)
  have E₇ := E₆.others g₇ sp₇ rd₇ wr₇
  have F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have F₃₇ : Frame (mutR W D n) s₃.mem s₇.mem :=
    ((F₄.trans F₅).trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide))).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact in_mutD fun _ h => h)
  -- The result, and `restore`.
  have ok₇ : s₇.mem.readW W 64 = if c then 1#64 else 0#64 := by
    have e : s₆.mem.readW W 64 = if c then 1#64 else 0#64 := by
      have := Mem.readW_writeW_self64 s₅.mem (W + BitVec.ofNat 64 tagO)
        (if bytesAt s₅.mem W tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64)
      rw [← m₆] at this
      simp only [tagO, BitVec.add_zero] at this
      rw [this]; simp only [c, decide_eq_true_eq]
    rw [F₇.readW (r := ⟨W, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide), e]
  have r₀ : InRegions (s₇.rd ++ s₇.wr) W 8 := by simpa using E₇.perm.wR (d := 0) (n := 8) (by decide)
  obtain ⟨s₈, run₈, x0₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .x0 .x19 tagO] s₇ = some s₈ ∧
      s₈.gpr .x0 = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ∉ [Reg.x0] → s₈.gpr r = s₇.gpr r) ∧
      s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.x19, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp [gpr_write]
    · rfl
    · simp only [List.mem_singleton] at h
      simp [gpr_write, h]
    all_goals rfl
  have E₈ := E₇.others g₈ sp₈ rd₈ wr₈
  have sv₈ : Spill.Saved W s.gpr saved s₈.mem := by
    rw [m₈]; exact saved_mut L Ar.data.w P₃.saved F₃₇
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  refine WP.mono (restore_wp' E₈ sv₈) fun s₉ Rs => ⟨restore_abi Rs E₈.sp, ?_⟩
  -- The plaintext and the comparison.
  have x0₉ : s₉.gpr .x0 = if c then 1#64 else 0#64 := by rw [Rs.other _ (by decide), x0₈]
  have hout := B.out
  rw [c₃, i₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [l₃] at hofs
  have hck := B.ck
  rw [c₃, i₃, l₃, d₃] at hck
  have w16 : bytesAt s₅.mem W 16 = bytesAt s.mem W 16 := by
    have dw : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 2560 → (⟨W, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => Offset.base_disjoint W h₁ (by have := L.ww; omega)
    rw [Proof.Cmac.bytesAt_frame T.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact dw (by decide) (by decide)) (by decide),
      Proof.Cmac.bytesAt_frame B.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dw (by decide) (by decide)
        · exact dw (by decide) (by decide)
        · exact dw (by decide) (by decide)
        · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide), P₃.tagIn]
  have recv : bytesAt s₅.mem W tl = bytesAt s.mem W tl := by
    rw [bytesAt_take_block _ _ Ar.t16, bytesAt_take_block s.mem _ Ar.t16, blockAtMem, blockAtMem, w16]
  have tagv := T.val
  rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
  have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
    have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by omega),
        Proof.Cmac.bytesAt_frame T.frame (tag_data Ar.data.w (by decide)) (by omega)]
    rw [Rs.mem, m₈, m₇, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
  rw [x0₉, d₉, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem W tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, hx, decide_eq_true_iff, eq_comm]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openAArch64.pre s) :
    WP isa («open» (callees v)) s fun s' => GprAbi s s' ∧ openAArch64.post s s' :=
  open_wp' v (args_of h) rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.AArch64
