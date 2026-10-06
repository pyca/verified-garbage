import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes

/-!
# Deterministic ECDSA on 32-bit ARM: signing with a candidate

`core(out, d, digest, k, scratch)`'s arguments (`coreArgs_ok`), then the
call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame, or, if `wide`,
the digest and `k` from the frame's top words, in a frame of `{r12, lr}`
whose first word is its stack argument, `scratch`, as for HMAC's `init`
(`core_ok`): it returns 1 and writes the signature, or returns 0 and writes
zeros, as `Spec.Ecdsa.signWith` gives for `d` and `Q` bytes of the digest
and of `k`, and changes only `out`, `scratch` and the 24 bytes below the
frame.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Arm.FrameStack
open VG.Proof.Pbkdf2.Whole.Arm (After stk frame2_ok p2_arg0 p2_bytes p2_sub)
open VG.Proof.Pbkdf2.Stream.Arm (ce0 ce1 ce2 ce3)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The digest and `k` `core` is passed, and their addresses. -/
abbrev dgArg {dn : Nat} (L : Lay dn) : BitVec 32 := if L.wide then L.fp + BitVec.ofNat 32 fX else L.dg
abbrev kArg {dn : Nat} (L : Lay dn) : BitVec 32 :=
  if L.wide then L.fp + BitVec.ofNat 32 fKb else L.fp + BitVec.ofNat 32 fV
abbrev dgAddr {dn : Nat} (L : Lay dn) : Addr := if L.wide then L.B + BitVec.ofNat 64 240 else State.addr L.dg
abbrev kAddr {dn : Nat} (L : Lay dn) : Addr :=
  if L.wide then L.B + BitVec.ofNat 64 312 else L.B + BitVec.ofNat 64 88

theorem dgArg_w (hL : L.Ok) : State.addr (dgArg L) = dgAddr L := by
  simp only [dgArg, dgAddr]
  cases hw : L.wide
  · rfl
  · have := L.ew; rw [hw] at this
    exact hL.fpA (by simp only [extra, ite_true] at this; simp only [fX]; omega)

theorem kArg_w (hL : L.Ok) : State.addr (kArg L) = kAddr L := by
  simp only [kArg, kAddr]
  cases hw : L.wide
  · exact hL.fpA (by simp only [fV]; omega)
  · have := L.ew; rw [hw] at this
    exact hL.fpA (by simp only [extra, ite_true] at this; simp only [fKb]; omega)

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m (State.addr L.d) (dgAddr L) (kAddr L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and its
argument on the stack, and writes `out` and `scratch`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨State.addr L.d, P.Q⟩, ⟨dgAddr L, P.Q⟩, ⟨kAddr L, P.Q⟩, ⟨L.B + BitVec.ofNat 64 16, 4⟩]
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨State.addr L.out, 2 * P.Q⟩, L.SCR]

/-- The arguments of `core`. -/
theorem coreArgs_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Cfg.coreArgs L.wide)) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = L.out ∧ t'.gpr .r1 = L.d ∧ t'.gpr .r2 = dgArg L ∧ t'.gpr .r3 = kArg L ∧
      t'.gpr .r12 = L.scr ∧ t'.gpr .r9 = t.gpr .r9 := by
  simp only [Cfg.coreArgs, List.cons_append, List.nil_append]
  refine movr_ok hc (d := .r0) (r := .r4) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine movr_ok c₁ (d := .r1) (r := .r5) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  have h0 : t₂.gpr .r0 = L.out := by rw [k₂ _ (by decide), v₁, hc.r4]
  have h1 : t₂.gpr .r1 = L.d := by rw [v₂, c₁.r5]
  have h9 : t₂.gpr .r9 = t.gpr .r9 := by rw [k₂ _ (by decide), k₁ _ (by decide)]
  have m : t₂.mem = t.mem := by rw [m₂, m₁]
  cases hw : L.wide
  · simp only [Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    refine movr_ok c₂ (d := .r2) (r := .r6) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
    refine fpAdd_ok c₃ (d := .r3) (by decide) (o := fV) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
    refine movr_ok c₄ (d := .r12) (r := .r11) (by decide) fun t₅ c₅ m₅ v₅ k₅ => WP.block_nil ?_
    refine ⟨c₅, by rw [m₅, m₄, m₃, m], ?_, ?_, ?_, ?_, by rw [v₅, c₄.r11], ?_⟩
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h0]
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h1]
    · rw [k₅ _ (by decide), k₄ _ (by decide), v₃, c₂.r6, dgArg, hw]; rfl
    · rw [k₅ _ (by decide), v₄, kArg, hw]; rfl
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h9]
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine fpAdd_ok c₂ (d := .r2) (by decide) (o := fX) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
    refine fpAdd_ok c₃ (d := .r3) (by decide) (o := fKb) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
    refine movr_ok c₄ (d := .r12) (r := .r11) (by decide) fun t₅ c₅ m₅ v₅ k₅ => WP.block_nil ?_
    refine ⟨c₅, by rw [m₅, m₄, m₃, m], ?_, ?_, ?_, ?_, by rw [v₅, c₄.r11], ?_⟩
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h0]
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h1]
    · rw [k₅ _ (by decide), k₄ _ (by decide), v₃, dgArg, hw]; rfl
    · rw [k₅ _ (by decide), v₄, kArg, hw]; rfl
    · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), h9]

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs {dn : Nat} (L : Lay dn) (t : State) : Prop where
  r0 : t.gpr .r0 = L.out
  r1 : t.gpr .r1 = L.d
  r2 : t.gpr .r2 = dgArg L
  r3 : t.gpr .r3 = kArg L
  r12 : t.gpr .r12 = L.scr

/-- What `core`'s digest and `k` need of the layout: unless two `V`s make a
candidate, the digest has `Q` bytes; if they do, the frame has its top
words. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ (L.wide = false → P.Q ≤ dn) ∧ L.wide = P.R.wide

/-- `core`'s digest and `k`: in the digest or the frame, apart from `out`,
`scratch` and the stack below the frame, and not wrapping. -/
theorem coreArg_ok (hL : L.Ok) (hk : CoreOk P L) {v : BitVec 32} {x : Addr}
    (hx : (v = dgArg L ∧ x = dgAddr L) ∨ (v = kArg L ∧ x = kAddr L)) :
    (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B, 24⟩ ∧ v.toNat + P.Q ≤ 2 ^ 32 := by
  have nB := hL.nB
  have := L.sp.isLt
  cases hw : L.wide
  · obtain ⟨hQ8, h6, -⟩ := P.sizesA (hk.2.2 ▸ hw)
    have hn := hk.2.1 hw
    have he : L.e = 0 := by rw [L.ew, hw]; rfl
    simp only [dgArg, kArg, dgAddr, kAddr, hw, Bool.false_eq_true, ite_false] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨L.DG, by simp, within_base _ hn⟩, hL.og.symm.sub_left (Region.sub_prefix hn),
        hL.gc.sub_left (Region.sub_prefix hn),
        ((hL.kg.sub_left (Region.sub_prefix (by omega))).symm).sub_left (Region.sub_prefix hn),
        by have := hL.ng; omega⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm,
        by rw [fp_toNat hL (by simp only [fV]; omega)]; simp only [fV]; omega⟩
  · obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW (hk.2.2 ▸ hw)
    have he : L.e = 36 := by rw [L.ew, hw]; rfl
    simp only [dgArg, kArg, dgAddr, kAddr, hw, ite_true] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm,
        by rw [fp_toNat hL (by simp only [fX]; omega)]; simp only [fX]; omega⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega),
        (Offset.base_disjoint _ (by omega) (by omega)).symm,
        by rw [fp_toNat hL (by simp only [fKb]; omega)]; simp only [fKb]; omega⟩

theorem core_sp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    State.addr (t.sp - BitVec.ofNat 32 8) = L.B + BitVec.ofNat 64 16 := by
  rw [addr_sub' (by have := hc.sp24 hL; omega), hc.spA hL, Offset.add_ofNat_sub _ (by decide)]

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    (coreK P.R.E).pre ((pushed [.r12, .lr] t).callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have h24 := hc.sp24 hL
  have hsp := core_sp hL hc
  have := hL.nB; have := L.sp.isLt
  have hq : L.q = P.R.E.C.len := hk.1
  have eD : (⟨State.addr L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  have eO : (⟨State.addr L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
  obtain ⟨-, gO, gS, -, gN⟩ := coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)
  obtain ⟨-, kO, kS, -, kN⟩ := coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)
  simp only [coreK, State.withRegions_gpr, ce0, ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1,
    hr.r2, hr.r3, p2_arg0 (s := t) (by omega), hr.r12, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, pushed_sp, dgArg_w hL, kArg_w hL]
  simp only [eD, eO]
  refine ⟨?_, trivial, hL.oc, hL.dc, gS, kS, ?_, ?_,
    by have := hL.no; rw [hq] at this; omega, by have := hL.nd; rw [hq] at this; omega, gN, kN, hL.nc, ?_⟩
  · rw [← eD, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_OUT (by omega)).symm
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_SCR (by omega)).symm
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, VG.Arm.FrameStack.sub_toNat' (by omega)]; omega

theorem core_cov (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) := by
  have hq : L.q = P.Q := hk.1
  have hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
      ∃ R ∈ [L.D, L.DG] ++ [⟨L.B + BitVec.ofNat 64 16, 8⟩, L.FR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R :=
    fun ⟨R, hR, hW⟩ => ⟨R, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl <;> simp, hW⟩
  refine covers_of fun q hq' => ?_
  rw [pushed_rd, pushed_wr, hc.rd, hc.wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, core_sp hL hc]
  simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq'
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨L.D, by simp, within_base _ (by omega)⟩
  · exact hw (coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)).1
  · exact hw (coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)).1
  · exact ⟨⟨L.B + BitVec.ofNat 64 16, 8⟩, by simp, within_base _ (by omega)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_covW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreWr P L) (pushed [.r12, .lr] t).wr :=
  covers_of fun q hq' => by
    rw [pushed_wr, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, k, scratch)`, in a frame of `{scratch, lr}`. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hr : CoreRegs L t) :
    WP isa (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 1 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 0 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have h24 := hc.sp24 hL
  have hst := hc.stk_eq hL
  have hq : L.q = P.Q := hk.1
  have eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine frame2_ok (ra := .r12) (rb := .lr) (t := .r12) rfl (by decide) P.R.coreX
    (by show armStack P.R.coreC ≤ 16; rw [P.R.coreStack]; omega) h24 (core_pre hL hk hc hr)
    (core_cov hL hk hc) (core_covW hq hc) fun s₂ ha hpost => ?_
  rw [eW] at ha
  have hf : Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem (popped .r12 8 s₂).mem := ha.frame.sub fun q hq' => by
    rw [hst] at hq'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
  refine ⟨hc.after hL ha fun q hq' => ?_, ha.cs .r9 (by decide) (by decide), hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
  · obtain ⟨-, -, -, gB, -⟩ := coreArg_ok hL hk (.inl ⟨rfl, rfl⟩)
    obtain ⟨-, -, -, kB, -⟩ := coreArg_ok hL hk (.inr ⟨rfl, rfl⟩)
    have hQe : P.Q = P.R.E.C.len := rfl
    have hQl : P.Q ≤ 72 := by have := P.R.len_words; have := P.R.n9; omega
    have hq : L.q = P.Q := hk.1
    have hs : coreSigOf P.R.E (pushed [.r12, .lr] t).mem (State.addr L.d) (dgAddr L) (kAddr L) =
        coreSig P L t.mem := by
      have d1 : (stk t).Disjoint ⟨State.addr L.d, P.R.E.C.len⟩ := by
        rw [hst]
        exact (hL.kd.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
      have d2 : (stk t).Disjoint ⟨dgAddr L, P.R.E.C.len⟩ := by rw [hst]; exact gB.symm
      have d3 : (stk t).Disjoint ⟨kAddr L, P.R.E.C.len⟩ := by rw [hst]; exact kB.symm
      simp only [coreSigOf, coreSig, Rfc6979.ecdsa_bytesAt]
      rw [p2_bytes h24 d1 (by omega), p2_bytes h24 d2 (by omega), p2_bytes h24 d3 (by omega)]
    simp only [coreK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0,
      ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1, hr.r2, hr.r3, dgArg_w hL, kArg_w hL, hs] at hpost
    rw [popped_gpr (by decide), popped_gpr (by decide), popped_mem]
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.Arm
