import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs

/-!
# Deterministic ECDSA on 32-bit ARM: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) in the frame and `len` bytes of data in the frame or in `scratch`
above HMAC's working space (`DataOk`), written to the frame at `dst`: HMAC's
`init` with `K` (`init_step`), the streaming `update` on the inner state
(`upd_step`), and HMAC's `finalize` (`fin_step`), each called in its frame
as PBKDF2's code calls them (`VG.Proof.Pbkdf2.Whole.Arm`), for any hash
function `P`. They change only HMAC's states and working space (the first
2256 bytes of `scratch`), the 24 bytes below the frame, and `dst`
(`hmac_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (After HiArgs HfArgs UpdL hi_frame hf_frame upd_frame stk)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The stack below the frame -/

theorem Ctx.spA (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : State.addr t.sp = L.B + BitVec.ofNat 64 24 := by
  rw [hc.sp]; exact hL.fpA0

theorem Ctx.sp24 (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : 24 ≤ t.sp.toNat := by
  rw [← toNat_addr, hc.spA hL, Offset.toNat_add_ofNat]
  have := hL.B_fit; rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The 24 bytes below the frame, where the calls' frames go. -/
theorem Ctx.stk_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : stk t = ⟨L.B, 24⟩ := by
  simp only [stk, hc.spA hL]
  exact congrArg (fun b => (⟨b, 24⟩ : Region)) (BitVec.add_sub_cancel _ _)

/-- The 16 bytes below the stack pointer, which `update` may use. -/
theorem Ctx.below_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Pbkdf2.Stream.Arm.below t = ⟨L.B + BitVec.ofNat 64 8, 16⟩ := by
  simp only [Pbkdf2.Stream.Arm.below, hc.spA hL]
  exact congrArg (fun b => (⟨b, 16⟩ : Region)) (Offset.add_ofNat_sub L.B (show 16 ≤ 24 by decide))

theorem ptr_preserved : ∀ r ∈ ptrRegs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- What a call leaves keeps `Ctx`, if it writes only safe regions and the
24 bytes below the frame. -/
theorem Ctx.after (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2) ha.frame
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hc.stk_eq hL]
        exact .inr (.inr (.inl (Region.sub_prefix (by omega))))

/-- The same, for `update`, which may use the 16 bytes below the stack pointer. -/
theorem Ctx.afterU (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') (hs : ∀ r ∈ ws, Safe L r) : Ctx L g m₀ u' :=
  hc.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2) ha.frame
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        rw [hc.below_eq hL]
        exact safe_low L (by omega)

/-! ## Addresses -/

theorem scr_toNat (hL : L.Ok) {o : Nat} (ho : o < 8192) : (L.scr + BitVec.ofNat 32 o).toNat = L.scr.toNat + o := by
  have := hL.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

theorem fp_toNat (hL : L.Ok) {o : Nat} (ho : o ≤ 216 + 4 * L.e) :
    (L.fp + BitVec.ofNat 32 o).toNat = L.sp.toNat - (216 + 4 * L.e) + o := by
  have := hL.nB; have := L.sp.isLt; have := L.he
  have hfp : L.fp.toNat = L.sp.toNat - (216 + 4 * L.e) := VG.Arm.FrameStack.sub_toNat' (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32), hfp]
  exact Nat.mod_eq_of_lt (by omega)

/-- The stack below the frame and parts of it are apart from `scratch`. -/
theorem low_scr (hL : L.Ok) {n e k : Nat} (hn : n ≤ 240) (h : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, n⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ :=
  (hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ h)

/-- The part of `scratch` HMAC's functions use: its states and working space. -/
abbrev WK {dn : Nat} (L : Lay dn) : Region := ⟨State.addr L.scr, 2256⟩

theorem wk_safe {r : Region} (h : Region.Sub r (WK L)) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))

theorem scr_wk (hL : L.Ok) {o n : Nat} (ho : o < 8192) (h : o + n ≤ 2256) :
    Region.Sub ⟨State.addr (L.scr + BitVec.ofNat 32 o), n⟩ (WK L) := by
  rw [scrA hL ho]; exact Offset.sub_base _ h

/-- The memory a call changes: within `ws`, each in `WK`, or in the 24 bytes below the frame. -/
theorem after_frame (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region} (ha : After u ws u')
    (hs : ∀ r ∈ ws, Region.Sub r (WK L)) : Frame [WK L, ⟨L.B, 24⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨WK L, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.stk_eq hL]; exact sub_refl _⟩

theorem after_frameU (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {ws : List Region}
    (ha : Pbkdf2.Stream.Arm.After u ws u') (hs : ∀ r ∈ ws, Region.Sub r (WK L)) :
    Frame [WK L, ⟨L.B, 24⟩] u.mem u'.mem :=
  ha.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨WK L, by simp, hs r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 24⟩, by simp, by rw [hc.below_eq hL]; exact Offset.sub_base _ (by omega)⟩

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok {t : State} (hc : Ctx L g m₀ t) {D : Nat} (hD : D < 2 ^ 16) :
    WP isa (.block (Cfg.hmacArgs₁ D)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ t'.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
      t'.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ t'.gpr .r3 = BitVec.ofNat 32 D ∧
      t'.gpr .r12 = L.scr + BitVec.ofNat 32 384 ∧ t'.gpr .r9 = t.gpr .r9 := by
  simp only [Cfg.hmacArgs₁, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine fpAdd_ok c₂ (d := .r2) (by decide) (o := fK) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine movw_ok c₃ (d := .r3) (by decide) hD fun t₄ c₄ m₄ v₄ k₄ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₄ (d := .r12) (by decide) (o := sWork) (by decide) fun t₅ c₅ m₅ v₅ k₅ => ?_
  refine WP.block_nil ⟨c₅, by rw [m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, v₅, ?_⟩
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]
    exact v₁
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide)]
    exact v₂
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide)]
    exact v₃
  · rw [k₅ _ (by decide) (by decide)]
    exact v₄
  · rw [k₅ _ (by decide) (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide),
      k₁ _ (by decide) (by decide)]

/-- The key `K`: the first `D` bytes of the frame. -/
abbrev keyOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) P.F.H.D

/-- After HMAC's `init`: HMAC's states for the key `K` in the frame on entry `t`. -/
structure Inited (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 0))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 192))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of HMAC's `init`, as its frame needs them. -/
theorem initA (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (h0 : u.gpr .r0 = L.scr + BitVec.ofNat 32 0)
    (h1 : u.gpr .r1 = L.scr + BitVec.ofNat 32 192) (h2 : u.gpr .r2 = L.fp + BitVec.ofNat 32 0)
    (h3 : u.gpr .r3 = BitVec.ofNat 32 P.F.H.D) (h12 : u.gpr .r12 = L.scr + BitVec.ofNat 32 384) :
    HiArgs P.ok.hH.SH P.ok.Wi u (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.fp + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 384) P.F.H.D := by
  have e0 := scrA hL (o := 0) (by decide)
  have e1 := scrA hL (o := 192) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have ek := hL.fpA (o := 0) (by omega)
  have hst := hc.stk_eq hL
  have := hL.nc; have := hL.nB; have := L.sp.isLt
  obtain ⟨_, _, _, _, _, _, _, _, _, hS, _, hB⟩ := P.sizes
  exact
    { r0 := h0, r1 := h1, r2 := h2, r3 := h3, r12 := h12
      klB := by rw [hB]; anums
      kl32 := by anums
      sp := hc.sp24 hL
      cr := hc.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [ek]; exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
      cw := hc.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_o := by rw [e0, e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      i_k := by rw [e0, ek]; exact (hL.stk_scr (by anums) (by anums)).symm
      i_s := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      o_k := by rw [e1, ek]; exact (hL.stk_scr (by anums) (by anums)).symm
      o_s := by rw [e1, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      k_s := by rw [ek, e3]; exact hL.stk_scr (by anums) (by anums)
      b_i := by rw [hst, e0]; exact low_scr hL (by omega) (by anums)
      b_o := by rw [hst, e1]; exact low_scr hL (by omega) (by anums)
      b_k := by rw [hst, ek]; exact Offset.base_disjoint _ (by omega) (by anums)
      b_s := by rw [hst, e3]; exact low_scr hL (by omega) (by anums)
      ni := by rw [scr_toNat hL (by decide)]; anums
      no := by rw [scr_toNat hL (by decide)]; anums
      nk := by rw [fp_toNat hL (by omega)]; anums
      nsc := by rw [scr_toNat hL (by decide)]; anums }

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (Cfg.hmacArgs₁ P.F.H.D))
      (.frame (.push [.r12, .lr]) (.call P.F.hiN P.F.hiC) (.pop .r12 8))) t (Inited P L g m₀ t) := by
  refine WP.seq (WP.mono (initArgs_ok hc (D := P.F.H.D) (by anums)) fun u ⟨hcu, hmu, h0, h1, h2, h3, h12, h9⟩ => ?_)
  refine hi_frame P.ok.hi P.ok.hiSt (initA hL hcu h0 h1 h2 h3 h12) fun u' ha hi ho => ?_
  have ek : Spec.Sha256.bytesAt u.mem (State.addr (L.fp + BitVec.ofNat 32 0)) P.F.H.D = keyOf P L t.mem := by
    rw [hL.fpA (by omega), hmu]
  have hws : ∀ r ∈ HiArgs.wr P.ok.hH.SH P.ok.Wi (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.scr + BitVec.ofNat 32 384), Region.Sub r (WK L) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_wk hL (by decide) (by anums)
  exact ⟨hcu.after hL ha fun r hr => wk_safe (hws r hr), by rw [ha.cs .r9 (by decide) (by decide), h9],
    hmu ▸ after_frame hL hcu ha hws,
    by rw [← ek]; exact hi, by rw [← ek]; exact ho⟩

/-! ## The streaming `update` -/

/-- Where the data may be: in the frame below `h`'s end, or in `scratch`
above HMAC's working space. -/
def DataOk {dn : Nat} (L : Lay dn) (da : BitVec 32) (len : Nat) : Prop :=
  (∃ o, da = L.fp + BitVec.ofNat 32 o ∧ o + len ≤ 176) ∨
    (∃ o, da = L.scr + BitVec.ofNat 32 o ∧ 2256 ≤ o ∧ o + len < 8192)

/-- Code that sets `r1` to the data's address `da`, changing nothing else but `r12`. -/
def DataA {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (dataA : List Instr) (da : BitVec 32) : Prop :=
  ∀ (u : State) (is : List Instr) (Q : State → Prop), Ctx L g m₀ u →
    (∀ u', Ctx L g m₀ u' → u'.mem = u.mem → u'.gpr .r1 = da → (∀ r, r ≠ .r1 → r ≠ .r12 → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) → WP isa (.block (dataA ++ is)) u Q

namespace DataOk

variable {da : BitVec 32} {len : Nat}

theorem addr (hd : DataOk L da len) (hL : L.Ok) :
    (∃ o, State.addr da = L.B + BitVec.ofNat 64 o ∧ 24 ≤ o ∧ o + len ≤ 200) ∨
      (∃ o, State.addr da = State.addr L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192) := by
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact .inl ⟨24 + o, hL.fpA (by omega), by omega, by omega⟩
  · exact .inr ⟨o, scrA hL (by omega), h₁, by omega⟩

theorem nowrap (hd : DataOk L da len) (hL : L.Ok) : da.toNat + len ≤ 2 ^ 32 := by
  have := hL.nc; have := hL.nB; have := L.sp.isLt
  rcases hd with ⟨o, rfl, h⟩ | ⟨o, rfl, h₁, h₂⟩
  · rw [fp_toNat hL (by omega)]; omega
  · rw [scr_toNat hL (by omega)]; omega

theorem low (hd : DataOk L da len) (hL : L.Ok) : Region.Disjoint ⟨L.B, 24⟩ ⟨State.addr da, len⟩ := by
  rcases hd.addr hL with ⟨o, e, h₁, h₂⟩ | ⟨o, e, h₁, h₂⟩ <;> rw [e]
  · exact Offset.base_disjoint _ h₁ (by omega)
  · exact low_scr hL (by omega) h₂

/-- The data is apart from HMAC's states and working space. -/
theorem work (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨State.addr da, len⟩ ⟨State.addr L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd.addr hL with ⟨o, e', h₁, h₂⟩ | ⟨o, e', h₁, h₂⟩ <;> rw [e']
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem within (hd : DataOk L da len) (hL : L.Ok) :
    ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨State.addr da, len⟩ R := by
  rcases hd.addr hL with ⟨o, e, h₁, h₂⟩ | ⟨o, e, h₁, h₂⟩ <;> rw [e]
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

end DataOk

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.F.H.D) :
    (Spec.Hmac.blockKey P.ok.hH.SH.H k).length = P.F.H.B := by
  obtain ⟨_, _, _, _, _, _, _, hDB, _, _, _, hB⟩ := P.sizes
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.F.H.B < P.F.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.F.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

theorem append_zero {k : Nat} (hk : k < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 k = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega

theorem updArgs_ok {u : State} (hc : Ctx L g m₀ u) {dataA : List Instr} {da : BitVec 32}
    (hdA : DataA L g m₀ dataA da) {B : Nat} (hB : B < 2 ^ 16) {len : Nat} (hlen : len < 2 ^ 16) :
    WP isa (.block (Cfg.hmacArgs₂ B dataA len)) u fun u' => Ctx L g m₀ u' ∧
      u'.mem = u.mem ∧ u'.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u'.gpr .r1 = da ∧
      u'.gpr .r2 = BitVec.ofNat 32 B ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r7 = BitVec.ofNat 32 len ∧
      u'.gpr .r10 = L.scr + BitVec.ofNat 32 384 ∧ u'.gpr .r9 = u.gpr .r9 := by
  simp only [Cfg.hmacArgs₂, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine hdA t₁ _ _ c₁ fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine movw_ok c₂ (d := .r2) (by decide) hB fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine movw_ok c₄ (d := .r7) (by decide) hlen fun t₅ c₅ m₅ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₅ (d := .r10) (by decide) (o := sWork) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine WP.block_nil ⟨c₆, by rw [m₆, m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, ?_, v₆, ?_⟩
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide)]
    exact v₁
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), v₂]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), v₄]
  · rw [k₆ _ (by decide) (by decide), v₅]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide), k₁ _ (by decide) (by decide)]

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (da : BitVec 32) (len : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩] t.mem u.mem
  inner : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 0))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem (State.addr da) len)
  outer : P.ok.hH.SH.Repr u.mem (State.addr (L.scr + BitVec.ofNat 32 192))
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

/-- The arguments of the streaming `update`, as its frame needs them. -/
theorem updA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {da : BitVec 32} {len : Nat} (hd : DataOk L da len)
    (hlen : len ≤ 256)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 0) (h1 : w.gpr .r1 = da)
    (h7 : w.gpr .r7 = BitVec.ofNat 32 len) (h10 : w.gpr .r10 = L.scr + BitVec.ofNat 32 384) :
    UpdL P.ok.hH w (L.scr + BitVec.ofNat 32 0) da (L.scr + BitVec.ofNat 32 384) len := by
  have e0 := scrA hL (o := 0) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have hb := hcw.below_eq hL
  have hn := hd.nowrap hL
  have := hL.nc
  obtain ⟨_, _, _, _, _, _, _, _, _, hS, _, hB⟩ := P.sizes
  have bsub : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 16⟩ ⟨L.B, 24⟩ := Offset.sub_base _ (by omega)
  exact
    { r0 := h0, r1 := h1, r7 := h7, r10 := h10
      hlen := by omega
      sp16 := by have := hcw.sp24 hL; omega
      cd := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd.within hL
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      st_sc := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      d_st := by rw [e0]; exact hd.work hL (by anums)
      d_sc := by rw [e3]; exact hd.work hL (by anums)
      b_st := by rw [hb, e0]; exact (low_scr hL (by omega) (by anums)).sub_left bsub
      b_d := by rw [hb]; exact (hd.low hL).sub_left bsub
      b_sc := by rw [hb, e3]; exact (low_scr hL (by omega) (by anums)).sub_left bsub
      nst := by rw [scr_toNat hL (by decide)]; anums
      nd := hn
      nsc := by rw [scr_toNat hL (by decide)]; anums }

theorem upd_step (hL : L.Ok) {t u : State} (hu : Inited P L g m₀ t u) {dataA : List Instr} {da : BitVec 32}
    {len : Nat} (hdA : DataA L g m₀ dataA da) (hd : DataOk L da len) (hlen : len ≤ 256) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ P.F.H.B dataA len))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call P.F.H.updN P.F.H.updC) (.pop .r1 16))) u
      (Updated P L g m₀ t da len) := by
  refine WP.seq (WP.mono (updArgs_ok hu.ctx hdA (B := P.F.H.B) (by anums) (len := len) (by omega))
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h7, h10, h9⟩ => ?_)
  refine upd_frame P.ok.hH (updA hL hcw hd hlen h0 h1 h7 h10) fun w' af hr => ?_
  have hws : ∀ r ∈ [(⟨State.addr (L.scr + BitVec.ofNat 32 0), P.F.H.S⟩ : Region),
      ⟨State.addr (L.scr + BitVec.ofNat 32 384), P.ok.hH.Wb⟩], Region.Sub r (WK L) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_wk hL (by decide) (by anums)
  have hdata : Spec.Sha256.bytesAt w.mem (State.addr da) len = Spec.Sha256.bytesAt t.mem (State.addr da) len := by
    rw [hmw]
    refine bytesAt_frame hu.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa using hd.work hL (e := 0) (k := 2256) (by omega)
    · exact (hd.low hL).symm
  have hcount : Pbkdf2.Stream.Arm.count w = BitVec.ofNat 64
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad).length := by
    rw [Pbkdf2.Stream.Arm.count, h2, h3, xorPad_length, blockKey_length (keyOf_length _)]
    exact append_zero (by anums)
  refine ⟨hcw.afterU hL af fun r hr => wk_safe (hws r hr), by rw [af.cs .r9 (by decide) (by decide), h9, hu.r9],
    hu.frame.trans (hmw ▸ after_frameU hL hcw af hws),
    ?_, ?_⟩
  · rw [← hdata]
    exact hr _ (hmw ▸ hu.inner) hcount
  · refine P.ok.hH.repr w.mem w'.mem _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨State.addr (L.scr + BitVec.ofNat 32 192), P.F.H.S⟩) af.frame (fun r hr => ?_)
      (by show P.F.H.S ≤ 2 ^ 64; anums) hi
    rw [scrA hL (by decide)] at hr ⊢
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)
      · rw [scrA hL (by decide)]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hcw.below_eq hL]
      exact ((low_scr hL (n := 24) (by omega) (by anums)).sub_left (Offset.sub_base _ (by omega))).symm

/-! ## HMAC's `finalize` -/

theorem finArgs_ok {u : State} (hc : Ctx L g m₀ u) {B len dst : Nat} (hlen : B + len < 2 ^ 16)
    (he : encodable (BitVec.ofNat 32 dst) = true) :
    WP isa (.block (Cfg.hmacArgs₃ B len dst)) u fun u' => Ctx L g m₀ u' ∧ u'.mem = u.mem ∧
      u'.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u'.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
      u'.gpr .r2 = BitVec.ofNat 32 (B + len) ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r10 = L.fp + BitVec.ofNat 32 dst ∧
      u'.gpr .r12 = L.scr + BitVec.ofNat 32 384 ∧ u'.gpr .r9 = u.gpr .r9 := by
  simp only [Cfg.hmacArgs₃, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine movw_ok c₂ (d := .r2) (by decide) hlen fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine fpAdd_ok c₄ (d := .r10) (by decide) he fun t₅ c₅ m₅ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₅ (d := .r12) (by decide) (o := sWork) (by decide) fun t₆ c₆ m₆ v₆ k₆ => ?_
  refine WP.block_nil ⟨c₆, by rw [m₆, m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, ?_, v₆, ?_⟩
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide)]
    exact v₁
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]
    exact v₂
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), v₄]
  · rw [k₆ _ (by decide) (by decide), v₅]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
      k₂ _ (by decide) (by decide), k₁ _ (by decide) (by decide)]

/-- After HMAC's `finalize`: the MAC in the frame at `dst`. -/
structure Done (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (da : BitVec 32) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  r9 : u.gpr .r9 = t.gpr .r9
  frame : Frame [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.F.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem (State.addr da) len)

/-- The arguments of HMAC's `finalize`, as its frame needs them. -/
theorem finA (hL : L.Ok) {w : State} (hcw : Ctx L g m₀ w) {dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (h0 : w.gpr .r0 = L.scr + BitVec.ofNat 32 0) (h1 : w.gpr .r1 = L.scr + BitVec.ofNat 32 192)
    (h10 : w.gpr .r10 = L.fp + BitVec.ofNat 32 dst) (h12 : w.gpr .r12 = L.scr + BitVec.ofNat 32 384) :
    HfArgs P.ok.hH.SH P.ok.Wf w (L.scr + BitVec.ofNat 32 0) (L.scr + BitVec.ofNat 32 192)
      (L.fp + BitVec.ofNat 32 dst) (L.scr + BitVec.ofNat 32 384) := by
  have e0 := scrA hL (o := 0) (by decide)
  have e1 := scrA hL (o := 192) (by decide)
  have e3 := scrA hL (o := 384) (by decide)
  have eo := hL.fpA (o := dst) (by omega)
  have hst := hcw.stk_eq hL
  have := hL.nc; have := hL.nB; have := L.sp.isLt
  obtain ⟨_, _, _, _, _, _, _, _, _, hS, hD, hB⟩ := P.sizes
  exact
    { r0 := h0, r1 := h1, r10 := h10, r12 := h12
      sp := hcw.sp24 hL
      cr := hcw.covers fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      cw := hcw.coversW fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [e0]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
        · rw [eo]; exact ⟨L.FR, by simp, within_fr _ (by omega) (by anums)⟩
        · rw [e3]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
      i_u := by rw [e0, e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      i_o := by rw [e0, eo]; exact (hL.stk_scr (by anums) (by anums)).symm
      i_s := by rw [e0, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      u_o := by rw [e1, eo]; exact (hL.stk_scr (by anums) (by anums)).symm
      u_s := by rw [e1, e3]; exact Offset.disjoint _ (by anums) (by anums) (by anums)
      o_s := by rw [eo, e3]; exact hL.stk_scr (by anums) (by anums)
      b_i := by rw [hst, e0]; exact low_scr hL (by omega) (by anums)
      b_u := by rw [hst, e1]; exact low_scr hL (by omega) (by anums)
      b_o := by rw [hst, eo]; exact Offset.base_disjoint _ (by omega) (by anums)
      b_s := by rw [hst, e3]; exact low_scr hL (by omega) (by anums)
      ni := by rw [scr_toNat hL (by decide)]; anums
      nu := by rw [scr_toNat hL (by decide)]; anums
      no := by rw [fp_toNat hL (by omega)]; anums
      nsc := by rw [scr_toNat hL (by decide)]; anums }

theorem reprOK : Proof.Pbkdf2.Whole.Arm.ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

theorem fin_step (hL : L.Ok) {t u : State} {da : BitVec 32} {len dst : Nat} (hu : Updated P L g m₀ t da len u)
    (hlen : len ≤ 256) (hdst : dst + P.F.H.D ≤ 128) (he : encodable (BitVec.ofNat 32 dst) = true) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ P.F.H.B len dst))
      (.frame (.push [.r10, .r12]) (.call P.F.hfN P.F.hfC) (.pop .r12 8))) u (Done P L g m₀ t da len dst) := by
  refine WP.seq (WP.mono (finArgs_ok hu.ctx (B := P.F.H.B) (len := len) (by anums) he)
    fun w ⟨hcw, hmw, h0, h1, h2, h3, h10, h12, h9⟩ => ?_)
  refine hf_frame reprOK (by anums) P.ok.hf P.ok.hfSt (finA hL hcw hdst h0 h1 h10 h12) fun w' ha hpost => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, hS, hD, hB⟩ := P.sizes
  have eo := hL.fpA (o := dst) (by omega)
  have hk := blockKey_length (P := P) (keyOf_length (L := L) t.mem)
  have hl : (Spec.Sha256.bytesAt t.mem (State.addr da) len).length = len := by simp [Spec.Sha256.bytesAt]
  have hm := hpost _ (Spec.Sha256.bytesAt t.mem (State.addr da) len) (by rw [hk, hB])
    (by rw [hk, hl]; anums) (hmw ▸ hu.inner)
    (by rw [h3, h2, hB, hl]; exact append_zero (by anums)) (hmw ▸ hu.outer)
  rw [eo, hD] at hm
  have hws : ∀ r ∈ HfArgs.wr P.ok.hH.SH P.ok.Wf (L.scr + BitVec.ofNat 32 0) (L.fp + BitVec.ofNat 32 dst)
      (L.scr + BitVec.ofNat 32 384) ++ [stk w], ∃ r' ∈ [WK L, ⟨L.B, 24⟩,
        (⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩ : Region)], Region.Sub r r' := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hcw.stk_eq hL]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨WK L, by simp, scr_wk hL (by decide) (by anums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩, by simp, by rw [eo, hD]; exact sub_refl _⟩
    · exact ⟨WK L, by simp, scr_wk hL (by decide) (by anums)⟩
    · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
  refine ⟨hcw.keep hL ha.rd ha.wr ha.sp (fun r hr => ha.cs r (ptr_preserved r hr).1 (ptr_preserved r hr).2)
      ha.frame fun r hr => ?_, by rw [ha.cs .r9 (by decide) (by decide), h9, hu.r9],
    (hu.frame.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h],
      sub_refl _⟩).trans (hmw ▸ ha.frame.sub hws), hm⟩
  obtain ⟨r', hr', hs⟩ := hws r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact wk_safe hs
  · exact .inr (.inr (.inl (sub_trans hs (Region.sub_prefix (by omega)))))
  · exact .inr (.inr (.inl (sub_trans hs (Offset.sub_base _ (by anums)))))

/-! ## The whole HMAC -/

theorem seq_seq {a b c : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a b) s P)
    (hc : ∀ s', P s' → WP isa c s' Q) : WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  exact WP.mono h₁ hc

/-- `HMAC_K(data)`, for the key `K` in the frame, to the frame at `dst`. -/
theorem hmac_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : BitVec 32}
    {len dst : Nat} (hdA : DataA L g m₀ dataA da) (hd : DataOk L da len) (hlen : len ≤ 256)
    (hdst : dst + P.F.H.D ≤ 128) (he : encodable (BitVec.ofNat 32 dst) = true) :
    WP isa ((cfgOf P).hmac dataA len dst) t (Done P L g m₀ t da len dst) :=
  seq_seq (init_step hL hc) fun _ hu => seq_seq (upd_step hL hu hdA hd hlen) fun _ hw =>
    fin_step hL hw hlen hdst he

end VG.Proof.Ecdsa.Rfc6979.Arm
