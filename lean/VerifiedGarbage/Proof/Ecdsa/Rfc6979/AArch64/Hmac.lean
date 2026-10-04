import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash

/-!
# Deterministic ECDSA on AArch64: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`: HMAC's
`init` with `K` (`init_step`), the streaming `update` on the inner state
(`upd_step`), and HMAC's `finalize` (`fin_step`), for any hash function `P`.
They change only HMAC's states and working space (the first 2256 bytes of
`scratch`), the 16 bytes below the frame, and `dst` (`hmac_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64.Calls (After)

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 16 ≤ o ∧ o + len ≤ 184) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

namespace DataOk

variable {da : Addr} {len : Nat}

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact hL.low_scr h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem within (hd : DataOk L da len) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

theorem Ctx.sp16 (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) : 16 ≤ u.sp.toNat := by
  rw [hc.sp, toNat_add_of (by have := hL.nB; omega)]; omega

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (D : Nat) (hD : D < 2 ^ 16) :
    WP isa (.block (Cfg.hmacArgs₁ D)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .x2 = L.B + BitVec.ofNat 64 16 ∧ t'.gpr .x3 = BitVec.ofNat 64 D ∧
      t'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (fr_ok hL h₂.ctx (d := .x2) (by decide) (o := 0) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (movz_ok hL h₃.ctx (d := .x3) (by decide) hD) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- What a call leaves keeps `Ctx`, if it writes only safe regions and the
16 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hc.below_eq]
      exact .inr (.inr (Region.sub_prefix (by omega)))

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 16) P.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

/-- The memory a call changes: within `ws`, each in `⟨scratch, 2256⟩` or in
the 16 bytes below the frame. -/
theorem after_frame {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Region.Sub r ⟨L.scr, 2256⟩) : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨⟨L.scr, 2256⟩, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 16⟩, by simp, by rw [hc.below_eq]; exact sub_refl _⟩

theorem initA (hL : L.Ok) {u : State} (hcu : Ctx L g m₀ u) (h0 : u.gpr .x0 = L.scr + BitVec.ofNat 64 0)
    (h1 : u.gpr .x1 = L.scr + BitVec.ofNat 64 192) (h2 : u.gpr .x2 = L.B + BitVec.ofNat 64 16)
    (h3 : u.gpr .x3 = BitVec.ofNat 64 P.H.D) (h4 : u.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := P.H) u (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (L.B + BitVec.ofNat 64 16) (L.scr + BitVec.ofNat 64 384) P.H.D := by
  have hsp : below u.sp 16 = ⟨L.B, 16⟩ := hcu.below_eq
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by anums)
      x4 := h4, klB := by anums
      cr := hcu.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
      cw := hcu.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_o := Offset.disjoint _ (by anums) (by anums) (by anums)
      i_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      k_i := hL.stk_scr (by anums) (by anums)
      k_o := hL.stk_scr (by anums) (by anums)
      k_s := hL.stk_scr (by anums) (by anums)
      sp16 := hcu.sp16 hL
      stk_i := by rw [hsp]; exact hL.low_scr (by anums)
      stk_o := by rw [hsp]; exact hL.low_scr (by anums)
      stk_k := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; anums }

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (Cfg.hmacArgs₁ P.H.D)) (.call P.H.hmacInitN P.H.hmacInit)) t (Inited P L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hL hc P.H.D (by anums)) fun u ⟨hcu, hmu, h0, h1, h2, h3, h4⟩ => ?_)
  have a := initA (P := P) hL hcu h0 h1 h2 h3 h4
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId a fun u' ha hi ho => ?_
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by anums)
  exact ⟨hcu.after hL ha fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega)))),
    hmu ▸ after_frame hcu ha hsafe, by rw [← hmu]; exact hi, by rw [← hmu]; exact ho⟩

/-! ## The streaming `update` -/

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.H.D) :
    (Spec.Hmac.blockKey P.ok.SH.H k).length = P.H.P.B := by
  have hB := P.ok.hB
  have hDB : P.H.D < P.H.P.B := by anums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.H.P.B < P.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem updArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) {B : Nat} (hB : B < 2 ^ 16)
    (hlen : len < 2 ^ 16) :
    WP isa (.block (Cfg.hmacArgs₂ B dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u'.gpr .x1 = BitVec.ofNat 64 B ∧
      u'.gpr .x2 = da ∧ u'.gpr .x3 = BitVec.ofNat 64 len ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₂, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (movz_ok hL h₁.ctx (d := .x1) (by decide) hB) fun u₂ h₂ => ?_
  refine WP.mono (hdA u₂ h₂.ctx) fun u₃ h₃ => ?_
  refine WP.mono (movz_ok hL h₃.ctx (d := .x3) (by decide) hlen) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩] t.mem u.mem
  inner : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : Addr} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 192) (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h2 : w.gpr .x2 = da)
    (h3 : w.gpr .x3 = BitVec.ofNat 64 len) (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs P.ok.stream w (L.scr + BitVec.ofNat 64 0) da
      (L.scr + BitVec.ofNat 64 384) len := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  exact
    { x0 := h0, x2 := h2, x3 := by rw [h3, BitVec.toNat_ofNat]; omega, x4 := h4
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_sc := Offset.disjoint _ (by anums) (by anums) (by anums)
      d_st := hd.work hL (by anums)
      d_sc := hd.work hL (by anums)
      sp16 := hcw.sp16 hL
      stk_st := by rw [hsp]; exact hL.low_scr (by anums)
      stk_d := by rw [hsp]; exact hd.low hL
      stk_sc := by rw [hsp]; exact hL.low_scr (by anums) }

theorem upd_step (hL : L.Ok) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr} {da : Addr} {len : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : DataOk L da len)
    (hlen : len ≤ 192) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ P.H.P.B dataA len)) (.call P.H.updN P.H.updC)) u
      (Updated P L g m₀ t da len) := by
  refine WP.seq (WP.mono (updArgs_ok hL hu.ctx hdA (B := P.H.P.B) (by anums) (by omega))
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have a := updA (P := P) hL hcw hd hlen h0 h2 h3 h4
  refine Proof.Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream a fun w' af hr => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by anums)
  have hdata : Spec.Sha256.bytesAt w.mem da len = Spec.Sha256.bytesAt t.mem da len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2256) (by omega)
    · exact (hd.low hL).symm
  refine ⟨hcw.after hL af fun r hr => .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega)))),
    hu.frame.trans (hmw ▸ after_frame hcw af hws), ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) (by rw [h1, xorPad_length, blockKey_length (keyOf_length _)])
  · refine P.ok.stream.repr w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.H.stream.S⟩) af.frame (fun r hr => ?_)
      (by show P.H.stream.S ≤ 2 ^ 64; anums) hi
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hcw.below_eq]
      exact (hL.low_scr (by anums)).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {B len dst : Nat} (hlen : B + len < 2 ^ 16)
    (hdst : dst < 4096) :
    WP isa (.block (Cfg.hmacArgs₃ B len dst)) u
      fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧ u'.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧
        u'.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧ u'.gpr .x2 = BitVec.ofNat 64 (B + len) ∧
        u'.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst) ∧ u'.gpr .x4 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₃, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := 0) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (scr_ok hL h₁.ctx (d := .x1) (by decide) (a := 192) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (movz_ok hL h₂.ctx (d := .x2) (by decide) hlen) fun u₃ h₃ => ?_
  refine WP.mono (fr_ok hL h₃.ctx (d := .x3) (by decide) hdst) fun u₄ h₄ => ?_
  refine WP.mono (scr_ok hL h₄.ctx (d := .x4) (by decide) (a := 384) (by decide)) fun u₅ h₅ => ?_
  refine ⟨h₅.ctx, by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val]
  · rw [h₅.keep _ (by decide), h₄.val]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 2256⟩, ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

/-- The arguments of HMAC's `finalize`. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {len dst : Nat} (hdst : dst + P.H.D ≤ 168)
    (h0 : w.gpr .x0 = L.scr + BitVec.ofNat 64 0) (h1 : w.gpr .x1 = L.scr + BitVec.ofNat 64 192)
    (h2 : w.gpr .x2 = BitVec.ofNat 64 (P.H.P.B + len)) (h3 : w.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst))
    (h4 : w.gpr .x4 = L.scr + BitVec.ofNat 64 384) :
    Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := P.H) w (L.scr + BitVec.ofNat 64 0)
      (L.scr + BitVec.ofNat 64 192) (BitVec.ofNat 64 (P.H.P.B + len)) (L.B + BitVec.ofNat 64 (16 + dst))
      (L.scr + BitVec.ofNat 64 384) := by
  have hsp : below w.sp 16 = ⟨L.B, 16⟩ := hcw.below_eq
  exact
    { x0 := h0, x1 := h1, x2 := h2, x3 := h3, x4 := h4
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
        · exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_u := Offset.disjoint _ (by anums) (by anums) (by anums)
      i_o := (hL.stk_scr (d := 16 + dst) (by anums) (by anums)).symm
      i_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      u_o := (hL.stk_scr (d := 16 + dst) (by anums) (by anums)).symm
      u_s := Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := hL.stk_scr (by anums) (by anums)
      sp16 := hcw.sp16 hL
      stk_i := by rw [hsp]; exact hL.low_scr (by anums)
      stk_u := by rw [hsp]; exact hL.low_scr (by anums)
      stk_o := by rw [hsp]; exact Offset.base_disjoint _ (by omega) (by anums)
      stk_s := by rw [hsp]; exact hL.low_scr (by anums)
      scnw := by rw [toNat_add_of (by have := hL.nc; omega)]; have := hL.nc; anums }

theorem fin_step (hL : L.Ok) {t u : State} {da : Addr} {len dst : Nat} (hu : Updated P L g m₀ t da len u)
    (hlen : len ≤ 192) (hdst : dst + P.H.D ≤ 168) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ P.H.P.B len dst)) (.call P.H.hmacFinN P.H.hmacFin)) u
      (Done P L g m₀ t da len dst) := by
  refine WP.seq (WP.mono (finArgs_ok hL hu.ctx (B := P.H.P.B) (len := len) (by anums) (by omega))
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h4⟩ => ?_)
  have a := finA (P := P) hL hcw (len := len) hdst h0 h1 h2 h3 h4
  refine Proof.Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd a fun w' ha hpost => ?_
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region),
      ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩] ++
      [below w.sp 16], ∃ r' ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩,
        ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hcw.below_eq]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩, by simp, sub_refl _⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by anums)⟩
    · exact ⟨⟨L.B, 16⟩, by simp, sub_refl _⟩
  have hl : (Spec.Sha256.bytesAt t.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcw.keep hL ha.rd ha.wr ha.sp ha.cs ha.frame fun r hr => ?_,
    hu.frame.sub (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩) |>.trans (hmw ▸ ha.frame.sub hws), ?_⟩
  · obtain ⟨r', hr', hs⟩ := hws r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs (Region.sub_prefix (by omega))))
    · exact .inr (.inr (sub_trans hs (Region.sub_prefix (by omega))))
    · exact .inr (.inr (sub_trans hs (Offset.sub_base _ (by anums))))
  · have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
    exact hpost _ _ hk (by rw [hk, hl]; anums)
      (hmw ▸ hu.inner) (by rw [hl]) (hmw ▸ hu.outer)

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .x2 da)) (hd : DataOk L da len)
    (hlen : len ≤ 192) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t da len dst) :=
  seq_seq (init_step hL hc) fun _ hu => seq_seq (upd_step hL hu hdA hd hlen) fun _ hw =>
    fin_step hL hw hlen hdst

end VG.Proof.Ecdsa.Rfc6979.AArch64
