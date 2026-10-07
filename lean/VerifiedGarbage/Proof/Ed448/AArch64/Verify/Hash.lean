import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Body

/-!
# Ed448 verification on AArch64: the hash

`H(dom4(0, C) ‖ R ‖ A ‖ M)` into the locals at `fH` (`hash_ok`): the state
zeroed, the header of `dom4` (kept in the locals), the context, `R`, the
public key and the message absorbed in turn, each from the position the
previous one returned, the padding, and 114 bytes squeezed.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  readW_eq_read Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed: `dom4(0, C) ‖ R ‖ A ‖ M`. -/
abbrev hashIn (L : Lay) (m : Mem) : List Byte :=
  hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ Spec.Sha3.bytesAt m L.sig 57 ++
    Spec.Sha3.bytesAt m L.pk 57 ++ Spec.Sha3.bytesAt m L.msg L.len.toNat

theorem scrOk (hL : L.Ok) : ScrOk L.env fScr L.scr := ⟨by simp [Lay.env], by simp [Lay.env], hL.nc⟩

/-- A region of the locals misses `scratch`. -/
theorem fr_st (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (ST L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (st_within L.scr).sub
theorem fr_ks (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (KS L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (ks_within L.scr).sub

theorem within_self (p : Addr) (n : Nat) : Within ⟨p, n⟩ ⟨p, n⟩ := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem in_readable (R : Region) (hR : R ∈ L.inputs) :
    Within R (FR L.E) ∨ ∃ R' ∈ L.env.ins ++ L.env.outs, Within R R' :=
  .inr ⟨R, by simp [Lay.env, hR], within_self R.base R.len⟩

/-- The hash. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) :
    WP isa (Impl.Ed448.AArch64.Verify.hash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 = Spec.Sha3.shake256 (hashIn L m₀) 114 := by
  have hV := env_ok hL
  have hs := scrOk hL
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  -- The header.
  have k0 := hc₁.2.1 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2.1 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
    (repr_nil hz₁)) fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := arg_src hL hc₂.1 ha (j := 1) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (arg_src hL hc₂.1 ha (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs])) (hL.cc.sub_right (st_within L.scr).sub)
    (hL.cc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, _, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  -- `R`.
  have a5 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aSig = L.sig := arg_src hL hc₃.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aSig) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a5 rfl hx₃ (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide))) hr₃)
    fun t₄ ⟨hc₄, _, hr₄, hx₄⟩ => ?_)
  have eS : Spec.Sha3.bytesAt t₃.mem L.sig 57 = Spec.Sha3.bytesAt m₀ L.sig 57 :=
    in_bytes hL hc₃.1 (R := L.SIG) (by simp [Lay.inputs]) (show 57 ≤ 114 by decide) (show 114 ≤ 2 ^ 64 by decide)
  rw [eS] at hr₄ hx₄
  -- The public key.
  have a0 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := arg_src hL hc₄.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₄ (by decide)
    (in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₅ ⟨hc₅, _, hr₅, hx₅⟩ => ?_)
  have eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₅ hx₅
  -- The message.
  have a3 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aMsg = L.msg := arg_src hL hc₅.1 ha (j := 3) (by decide) _
  have a4 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat :=
    (arg_src hL hc₅.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₅ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a3 a4
    hx₅ L.len.isLt (in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₅) fun t₆ ⟨hc₆, _, hr₆, hx₆⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₅.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    in_bytes hL hc₅.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₆ hx₆
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₆ (pos := .ret) trivial hx₆ (Nat.mod_lt _ (by decide)))
    fun t₇ ⟨hc₇, _, hp₇⟩ => ?_)
  have hst := hp₇ _ hr₆ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₇ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← shake256_eq]

end VG.Proof.Ed448.AArch64.Verify
