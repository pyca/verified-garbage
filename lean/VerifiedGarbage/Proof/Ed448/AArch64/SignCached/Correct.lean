module

public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
public import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Body
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ed448.AArch64.SignCached.Hash`, which this module and modules that import it used -/

section

/-!
# Ed448 signing with a cached public key on AArch64: the hashes

Each into the locals at `fH`: `SHAKE256(seed, 114)` (`seedHash_ok`),
`SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` with the prefix in the locals
(`nonceHash_ok`), and `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` with `R` in the
first half of `out` (`chalHash_ok`). The header of `dom4` is kept in the
locals; each absorption starts from the position the previous one returned.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  srcValue_loc Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed for `r` and for `k`: `dom4(0, C) ‖ X ‖ M`. -/
abbrev domIn (L : Lay) (m : Mem) (X : List Byte) : List Byte :=
  hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ X ++ Spec.Sha3.bytesAt m L.msg L.len.toNat

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

/-- Bytes apart from what a step writes are kept. -/
theorem keep_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) {n : Nat} (hn : n ≤ R.len) (hl : R.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' R.base n = Spec.Sha3.bytesAt m R.base n := by
  unfold Spec.Sha3.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hl (by have := List.mem_range.mp hi; omega_using [hn, this])

/-- A region apart from the sponge's writes. -/
theorem sponge_apart {R : Region} (hS : R.Disjoint (ST L.scr)) (hK : R.Disjoint (KS L.scr))
    (hC : (CK L.E).Disjoint R) : ∀ r ∈ [ST L.scr, KS L.scr, CK L.E], R.Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [hS, hK, hC.symm]

theorem len_src (hc : WCtx L.env g vec m₀ t) :
    srcValue L.env.E t.mem (t.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat := by
  rw [aLen, srcValue_loc hc.2.1 (show (fLen, L.len) ∈ L.env.ls by simp [Lay.env]) 0, BitVec.add_zero]
  exact (ofNat_toNat64 L.len).symm

/-- `SHAKE256(seed, 114)`. -/
theorem seedHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) :
    WP isa (seedHash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m₀ L.seed 57) 114 := by
  obtain hV := env_ok hL
  obtain hs := scrOk hL
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  obtain a1 : srcValue L.env.E t₁.mem (t₁.gpr .x0) aSeed = L.seed := arg_src hL hc₁.1 ha (j := 1) (by decide) _
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := aSeed) (len := .val (.const 57))
    (pos := .val (.const 0)) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) (show 0 < 65536 by decide)
    rfl rfl a1 rfl rfl (by decide) (in_readable L.SEED (by simp [Lay.inputs]))
    (hL.sc.sub_right (st_within L.scr).sub) (hL.sc.sub_right (ks_within L.scr).sub) hL.cs (repr_nil hz₁))
    fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  obtain eS : Spec.Sha3.bytesAt t₁.mem L.seed 57 = Spec.Sha3.bytesAt m₀ L.seed 57 :=
    in_bytes hL hc₁.1 (R := L.SEED) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eS, List.nil_append] at hr₂ hx₂
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₂ (pos := .ret) trivial hx₂ (Nat.mod_lt _ (by decide)))
    fun t₃ ⟨hc₃, _, hp₃⟩ => ?_)
  obtain hst := hp₃ _ hr₂ rfl
  refine WP.mono (ksqz_ok v hV hs hc₃ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← shake256_eq]

/-- What a hash into the locals writes: `scratch`, the 16 bytes below the
frame, and the hash. -/
abbrev HW (L : Lay) : List Region := [L.SCR, CK L.E, ⟨L.E + BitVec.ofNat 64 fH, 114⟩]

theorem hw_sub {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, r ∈ [ST L.scr, KS L.scr, CK L.E, ⟨L.E + BitVec.ofNat 64 fH, 114⟩]) :
    Frame (HW L) m m' := by
  refine hf.sub fun r hr => ?_
  obtain h' := h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (st_within L.scr).sub⟩
  · exact ⟨L.SCR, by simp, (ks_within L.scr).sub⟩
  · exact ⟨CK L.E, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The hash of `dom4(0, C) ‖ X ‖ M` into the locals, for `X` the 57 bytes
`xs` at `xp` (`x`), which the sponge's writes miss. -/
theorem domHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) {x : Src} (hvx : srcValid x) (hrx : noRet x = true) {xp : Addr}
    (hxp : ∀ {u : State}, WCtx L.env g vec m₀ u → srcValue L.env.E u.mem (u.gpr .x0) x = xp)
    (hin : Within ⟨xp, 57⟩ (FR L.E) ∨ ∃ R ∈ L.env.ins ++ L.env.outs, Within ⟨xp, 57⟩ R)
    (dS : Region.Disjoint ⟨xp, 57⟩ (ST L.scr)) (dK : Region.Disjoint ⟨xp, 57⟩ (KS L.scr))
    (kD : (CK L.E).Disjoint ⟨xp, 57⟩) :
    WP isa (.seq (VG.Impl.Ed448.AArch64.Whole.zeroSt fScr) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr (.val (.frame fHdr)) (.val (.const 10)) (.val (.const 0))) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aCtx aCtxLen .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr x (.val (.const 57)) .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aMsg aLen .ret) <|
      .seq (VG.Impl.Ed448.AArch64.Whole.kpad v.callee fScr .ret)
        (VG.Impl.Ed448.AArch64.Whole.ksqz v.callee fScr (.val (.frame fH)))) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame (HW L) t.mem u.mem ∧
        Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (domIn L m₀ (Spec.Sha3.bytesAt t.mem xp 57)) 114 := by
  obtain hV := env_ok hL
  obtain hs := scrOk hL
  obtain hx := sponge_apart dS dK kD
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, hf₁, hz₁⟩ => ?_)
  obtain eX₁ : Spec.Sha3.bytesAt t₁.mem xp 57 = Spec.Sha3.bytesAt t.mem xp 57 :=
    keep_bytes (R := ⟨xp, 57⟩) hf₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact dS)
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The header.
  obtain k0 := hc₁.2.1 (fHdr, sigWord) (by simp [Lay.env])
  obtain k8 := hc₁.2.1 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  obtain hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide))
    (ck_frame (by decide)) (repr_nil hz₁)) fun t₂ ⟨hc₂, hf₂, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  obtain eX₂ := keep_bytes (R := ⟨xp, 57⟩) hf₂ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The context.
  obtain a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := arg_src hL hc₂.1 ha (j := 3) (by decide) _
  obtain a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (arg_src hL hc₂.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs])) (hL.xc.sub_right (st_within L.scr).sub)
    (hL.xc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, hf₃, hr₃, hx₃⟩ => ?_)
  obtain eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  obtain eX₃ := keep_bytes (R := ⟨xp, 57⟩) hf₃ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- `X`.
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := x) (len := .val (.const 57)) (pos := .ret)
    hvx (show 57 < 65536 by decide) trivial hrx rfl (hxp hc₃) rfl hx₃ (by decide) hin dS dK kD hr₃)
    fun t₄ ⟨hc₄, hf₄, hr₄, hx₄⟩ => ?_)
  rw [eX₃, eX₂, eX₁] at hr₄ hx₄
  -- The message.
  obtain a3 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aMsg = L.msg := arg_src hL hc₄.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl a3 (len_src hc₄)
    hx₄ L.len.isLt (in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₄) fun t₅ ⟨hc₅, hf₅, hr₅, hx₅⟩ => ?_)
  obtain eM : Spec.Sha3.bytesAt t₄.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    in_bytes hL hc₄.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₅ hx₅
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₅ (pos := .ret) trivial hx₅ (Nat.mod_lt _ (by decide)))
    fun t₆ ⟨hc₆, hf₆, hp₆⟩ => ?_)
  obtain hst := hp₆ _ hr₅ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₆ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, hf₇, hb⟩ => ⟨hu, ?_, ?_⟩
  · have w₁ := hw_sub (L := L) hf₁ (by simp)
    obtain w₂ := hw_sub (L := L) hf₂ (by simp [Lay.env])
    obtain w₃ := hw_sub (L := L) hf₃ (by simp [Lay.env])
    obtain w₄ := hw_sub (L := L) hf₄ (by simp [Lay.env])
    obtain w₅ := hw_sub (L := L) hf₅ (by simp [Lay.env])
    obtain w₆ := hw_sub (L := L) hf₆ (by simp [Lay.env])
    obtain w₇ := hw_sub (L := L) hf₇ (by simp [Lay.env])
    exact (((((w₁.trans w₂).trans w₃).trans w₄).trans w₅).trans w₆).trans w₇
  · rw [hb, hst, ← shake256_eq]

/-- The hash of `dom4(0, C) ‖ R ‖ A ‖ M` into the locals, `R` in the first
half of `out`. -/
theorem chalHash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) :
    WP isa (chalHash v.callee) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame (HW L) t.mem u.mem ∧
        Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 =
        Spec.Sha3.shake256 (domIn L m₀ (Spec.Sha3.bytesAt t.mem L.out 57 ++
          Spec.Sha3.bytesAt m₀ L.pk 57)) 114 := by
  obtain hV := env_ok hL
  obtain hs := scrOk hL
  obtain dS : Region.Disjoint ⟨L.out, 57⟩ (ST L.scr) :=
    (hL.oc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide))
  obtain dK : Region.Disjoint ⟨L.out, 57⟩ (KS L.scr) :=
    (hL.oc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide))
  obtain kD : (CK L.E).Disjoint ⟨L.out, 57⟩ := hL.co.sub_right (Region.sub_prefix (by decide))
  obtain hx := sponge_apart dS dK kD
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, hf₁, hz₁⟩ => ?_)
  obtain eX₁ : Spec.Sha3.bytesAt t₁.mem L.out 57 = Spec.Sha3.bytesAt t.mem L.out 57 :=
    keep_bytes (R := ⟨L.out, 57⟩) hf₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact dS)
      (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The header.
  obtain k0 := hc₁.2.1 (fHdr, sigWord) (by simp [Lay.env])
  obtain k8 := hc₁.2.1 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  obtain hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide))
    (ck_frame (by decide)) (repr_nil hz₁)) fun t₂ ⟨hc₂, hf₂, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  obtain eX₂ := keep_bytes (R := ⟨L.out, 57⟩) hf₂ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- The context.
  obtain a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := arg_src hL hc₂.1 ha (j := 3) (by decide) _
  obtain a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (arg_src hL hc₂.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs])) (hL.xc.sub_right (st_within L.scr).sub)
    (hL.xc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, hf₃, hr₃, hx₃⟩ => ?_)
  obtain eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  obtain eX₃ := keep_bytes (R := ⟨L.out, 57⟩) hf₃ hx (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  -- `R`.
  obtain a0 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aOut = L.out := arg_src hL hc₃.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aOut) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₃ (by decide)
    (.inr ⟨L.OUT, by simp [Lay.env], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩) dS dK kD hr₃)
    fun t₄ ⟨hc₄, hf₄, hr₄, hx₄⟩ => ?_)
  rw [eX₃, eX₂, eX₁] at hr₄ hx₄
  -- The public key.
  obtain a2 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := arg_src hL hc₄.1 ha (j := 2) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a2 rfl hx₄ (by decide)
    (in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₄' ⟨hc₄', hf₄', hr₄', hx₄'⟩ => ?_)
  obtain eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₄' hx₄'
  -- The message.
  obtain a3 : srcValue L.env.E t₄'.mem (t₄'.gpr .x0) aMsg = L.msg := arg_src hL hc₄'.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄' (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl a3 (len_src hc₄')
    hx₄' L.len.isLt (in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₄') fun t₅ ⟨hc₅, hf₅, hr₅, hx₅⟩ => ?_)
  obtain eM : Spec.Sha3.bytesAt t₄'.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    in_bytes hL hc₄'.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₅ hx₅
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₅ (pos := .ret) trivial hx₅ (Nat.mod_lt _ (by decide)))
    fun t₆ ⟨hc₆, hf₆, hp₆⟩ => ?_)
  obtain hst := hp₆ _ hr₅ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₆ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fLen, fScr, fHdr, fH]) (by simp [fLen, fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, hf₇, hb⟩ => ⟨hu, ?_, ?_⟩
  · have w₁ := hw_sub (L := L) hf₁ (by simp)
    obtain w₂ := hw_sub (L := L) hf₂ (by simp [Lay.env])
    obtain w₃ := hw_sub (L := L) hf₃ (by simp [Lay.env])
    obtain w₄ := hw_sub (L := L) hf₄ (by simp [Lay.env])
    obtain w₄' := hw_sub (L := L) hf₄' (by simp [Lay.env])
    obtain w₅ := hw_sub (L := L) hf₅ (by simp [Lay.env])
    obtain w₆ := hw_sub (L := L) hf₆ (by simp [Lay.env])
    obtain w₇ := hw_sub (L := L) hf₇ (by simp [Lay.env])
    exact ((((((w₁.trans w₂).trans w₃).trans w₄).trans w₄').trans w₅).trans w₆).trans w₇
  · rw [hb, hst, ← shake256_eq, domIn, List.append_assoc _ (Spec.Sha3.bytesAt t.mem L.out 57)]

end VG.Proof.Ed448.AArch64.SignCached

end

end

/-!
# Ed448 signing with a cached public key on AArch64: the frame's body

Pruning (`prune_step`), the calls of the Ed448 primitives (`reduceR_step`,
`base_step`, `reduceK_step`, `mulAdd_step`), each with what it writes, the
locals cleared (`wipe_step`), and the body (`body_ok`): the signature in
`out`, for the inputs as on entry (`Proof.Ed448.sign_pipeline`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call base_call
  mulAdd_call Readable Writable Apart kept_frame prune_run sha3_bytesAt_length)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

attribute [local irreducible] VG.Impl.X448.AArch64.Base.combWords

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem ed448_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Ed448.bytesAt m p n = Spec.Sha3.bytesAt m p n := rfl

theorem scr_writable (L : Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], within_self _ _⟩

theorem outR_within (L : Lay) : Within ⟨L.out, 57⟩ L.OUT := ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩
theorem outS_within (L : Lay) : Within ⟨L.out + BitVec.ofNat 64 57, 57⟩ L.OUT :=
  ⟨57, rfl, by show 57 + 57 ≤ 114; decide⟩

theorem outR_writable (L : Lay) : Writable L.env ⟨L.out, 57⟩ := .inr ⟨L.OUT, by simp [Lay.env], outR_within L⟩
theorem outS_writable (L : Lay) : Writable L.env ⟨L.out + BitVec.ofNat 64 57, 57⟩ :=
  .inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem fr_out (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.OUT :=
  hL.ko.sub_left (Offset.sub_base _ h)

/-- A region of the locals apart from the kept words. -/
theorem fr_apart {d n : Nat} (h₁ : 16 ≤ d) (h₂ : d + n ≤ 200) : Apart L.env ⟨L.E + BitVec.ofNat 64 d, n⟩ :=
  ⟨⟨d, rfl, by show d + n ≤ 256; omega_using [h₂]⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fLen, fScr, fHdr]; omega_arith) (by simp [fLen, fScr, fHdr]) (by omega_using [h₂])⟩

theorem out_sep (hL : L.Ok) : Region.Disjoint ⟨L.out, 57⟩ ⟨L.out + BitVec.ofNat 64 57, 57⟩ := by
  have h := Offset.disjoint (L.out) (d := 0) (n := 57) (e := 57) (k := 57) (by omega_using []) (by omega_using [])
    (by have := hL.no; omega_using [])
  rwa [BitVec.add_zero] at h

/-- The word of `out` at 57. -/
theorem outS_src (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) (x0 : BitVec 64) :
    srcValue L.env.E t.mem x0 aR = L.out + BitVec.ofNat 64 57 := by
  show t.mem.read (L.E + BitVec.ofNat 64 (256 + 8 * 0)) 8 + BitVec.ofNat 64 57 = _
  rw [arg_word hL hc.1 ha (j := 0) (by decide)]
  rfl

/-- `s`: the hash pruned. -/
theorem prune_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) {hb : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114 = hb) :
    WP isa (.block prune) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 fS, 64⟩] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fS) 57) = Spec.Ed448.prune hb := by
  have hV := env_ok hL
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.1.sp, hc.1.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 fH) 114 = hb := by rw [hc.1.sp]; exact hh
  refine WP.mono_syms (prune_run (h := fH) (d := fS) hwrite (by decide) (by decide) (by decide) (by decide)
    (by decide) hh') fun u ⟨hu, hf, hp⟩ hsy => ?_
  rw [hc.1.sp] at hf hp
  refine ⟨hc.of_frame hV hu.rd hu.wr hu.sp (fun r hr _ => ?_) (fun r _ => by rw [hu.v]) hf ?_ hsy, hf, hp⟩
  · apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (fr_apart (by decide) (by decide))

/-- `r`, into the second half of `out`. -/
theorem reduceR_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧
      Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceRArgs) (by decide)
    (by simp [reduceRArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (List.mem_of_getElem? (i := 0) rfl)).trans (outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (outS_writable L) (scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `R = [r]B`, into the first half of `out`. -/
theorem base_step (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := baseArgs) (by decide)
    (by simp [baseArgs, aOut, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out :=
    (hv (.x0, aOut) (List.mem_of_getElem? (i := 0) rfl)).trans (arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (List.mem_of_getElem? (i := 1) rfl)).trans (outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (base_call hb hV ⟨rfl,rfl⟩ hu h0 h1 h2 (hL.oc.sub_left (outR_within L).sub)
    (hL.oc.sub_left (outS_within L).sub) hL.nc (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩)
    (outR_writable L) (scr_writable L) ha.2) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `k`, over the hash. -/
theorem reduceK_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.E + BitVec.ofNat 64 fH, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceKArgs) (by decide)
    (by simp [reduceKArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fH := hv (.x0, .val (.frame fH)) (List.mem_of_getElem? (i := 0) rfl)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (fr_apart (by decide) (by decide))) (scr_writable L)) fun w ⟨hw, hf, hk⟩ =>
      ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- `S = (r + k s) mod L`, into the second half of `out`. -/
theorem mulAdd_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t fun u =>
      WCtx L.env g vec m₀ u ∧ Frame [⟨L.out + BitVec.ofNat 64 57, 57⟩, L.SCR, CK L.E] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem (L.out + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 57)
          (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fS) 57) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := mulAddArgs) (by decide)
    (by simp [mulAddArgs, aR, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fH, fS, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x0, aR) (List.mem_of_getElem? (i := 0) rfl)).trans (outS_src hL hc ha _)
  have h1 : u.gpr .x1 = L.out + BitVec.ofNat 64 57 :=
    (hv (.x1, aR) (List.mem_of_getElem? (i := 1) rfl)).trans (outS_src hL hc ha _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fH := hv (.x2, .val (.frame fH)) (List.mem_of_getElem? (i := 2) rfl)
  have h3 : u.gpr .x3 = L.E + BitVec.ofNat 64 fS := hv (.x3, .val (.frame fS)) (List.mem_of_getElem? (i := 3) rfl)
  have h4 : u.gpr .x4 = L.scr := by
    rw [hv (.x4, .loc fScr 0) (List.mem_of_getElem? (i := 4) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (mulAdd_call hV hu h0 h1 h2 h3 h4 (hL.oc.sub_left (outS_within L).sub)
    (fr_scr hL (by decide)) (fr_scr hL (by decide)) (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩)
    (.inl ⟨fH, rfl, show fH + 57 ≤ 256 by decide⟩) (.inl ⟨fS, rfl, show fS + 57 ≤ 256 by decide⟩)
    (outS_writable L) (scr_writable L)) fun w ⟨hw, hf, hk⟩ => ⟨hw, by rw [← hm]; exact hf, by rw [hk, hm]⟩

/-- The hash, `k` and `s` cleared. -/
theorem wipe_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (.block wipe) t fun u => WCtx L.env g vec m₀ u ∧
      Frame [⟨L.E + BitVec.ofNat 64 16, 184⟩] t.mem u.mem := by
  have hV := env_ok hL
  refine WP.mono_syms (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc.1 (start := 2) (count := 23) (by decide))
    fun u ⟨hu, hf, _⟩ hsy => ⟨⟨hu, kept_frame hV hc.2.1 (hf.mono fun r hr => List.mem_append_left _ hr)
      fun r hr => ?_, by rw [hsy]; exact hc.2.2⟩, hf⟩
  rw [List.mem_singleton.mp hr]
  exact .inl (fr_apart (by decide) (by decide))

/-- The specification's hash input. -/
theorem dom_eq (L : Lay) (m : Mem) (X : List Byte) :
    domIn L m X = Spec.Ed448.dom4 0 (Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat) ++
      (X ++ Spec.Sha3.bytesAt m L.msg L.len.toNat) := by
  simp only [domIn, hdrBytes, Spec.Ed448.dom4, sha3_bytesAt_length, List.append_assoc, List.cons_append,
    List.nil_append]

theorem bytes_split (m : Mem) (p : Addr) :
    Spec.Sha3.bytesAt m p 114 = Spec.Sha3.bytesAt m p 57 ++ Spec.Sha3.bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

end VG.Proof.Ed448.AArch64.SignCached
