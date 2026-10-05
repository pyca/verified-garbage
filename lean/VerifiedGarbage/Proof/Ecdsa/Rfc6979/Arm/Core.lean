import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes

/-!
# Deterministic ECDSA on 32-bit ARM: signing with a candidate

`core(out, d, digest, V, scratch)`'s arguments (`coreArgs_ok`), then the call
of `vg_ecdsa_<curve>_sign` with `k = V` from the frame, in a frame of
`{r12, lr}` whose first word is its stack argument, `scratch`, as for HMAC's
`init` (`core_ok`): it returns 1 and writes the signature, or returns 0 and
writes zeros, as `Spec.Ecdsa.signWith` gives for `d`, the leftmost `8 w`
bytes of the digest and of `V`, and changes only `out`, `scratch` and the 24
bytes below the frame.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Arm.FrameStack
open VG.Proof.Pbkdf2.Whole.Arm (After stk frame2_ok p2_arg0 p2_bytes p2_sub)
open VG.Proof.Pbkdf2.Stream.Arm (ce0 ce1 ce2 ce3)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m (State.addr L.d) (State.addr L.dg) (L.B + BitVec.ofNat 64 88)

/-- `core` reads the private key, the leftmost `8 w` bytes of the digest and
of `V`, and its argument on the stack, and writes `out` and `scratch`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨State.addr L.d, 8 * P.w⟩, ⟨State.addr L.dg, 8 * P.w⟩, ⟨L.B + BitVec.ofNat 64 88, 8 * P.w⟩,
    ⟨L.B + BitVec.ofNat 64 16, 4⟩]
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨State.addr L.out, 16 * P.w⟩, L.SCR]

/-- The arguments of `core`. -/
theorem coreArgs_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r0 = L.out ∧ t'.gpr .r1 = L.d ∧ t'.gpr .r2 = L.dg ∧ t'.gpr .r3 = L.fp + BitVec.ofNat 32 64 ∧
      t'.gpr .r12 = L.scr ∧ t'.gpr .r9 = t.gpr .r9 := by
  simp only [Cfg.coreArgs]
  refine movr_ok hc (d := .r0) (r := .r4) (by decide) fun t₁ c₁ m₁ v₁ k₁ => ?_
  refine movr_ok c₁ (d := .r1) (r := .r5) (by decide) fun t₂ c₂ m₂ v₂ k₂ => ?_
  refine movr_ok c₂ (d := .r2) (r := .r6) (by decide) fun t₃ c₃ m₃ v₃ k₃ => ?_
  refine fpAdd_ok c₃ (d := .r3) (by decide) (o := fV) (by decide) fun t₄ c₄ m₄ v₄ k₄ => ?_
  refine movr_ok c₄ (d := .r12) (r := .r11) (by decide) fun t₅ c₅ m₅ v₅ k₅ => WP.block_nil ?_
  refine ⟨c₅, by rw [m₅, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, by rw [v₅, c₄.r11], ?_⟩
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), v₁, hc.r4]
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), v₂, c₁.r5]
  · rw [k₅ _ (by decide), k₄ _ (by decide), v₃, c₂.r6]
  · rw [k₅ _ (by decide), v₄]; rfl
  · rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]

/-- What a framed call of `core` needs of the registers. -/
structure CoreRegs {dn : Nat} (L : Lay dn) (t : State) : Prop where
  r0 : t.gpr .r0 = L.out
  r1 : t.gpr .r1 = L.d
  r2 : t.gpr .r2 = L.dg
  r3 : t.gpr .r3 = L.fp + BitVec.ofNat 32 64
  r12 : t.gpr .r12 = L.scr

theorem core_sp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    State.addr (t.sp - BitVec.ofNat 32 8) = L.B + BitVec.ofNat 64 16 := by
  rw [addr_sub' (by have := hc.sp24 hL; omega), hc.spA hL, Offset.add_ofNat_sub _ (by decide)]

theorem core_pre (hL : L.Ok) (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (hr : CoreRegs L t) :
    (coreK P.R.E).pre ((pushed [.r12, .lr] t).callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have h24 := hc.sp24 hL
  have hk : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega)
  have hsp := core_sp hL hc
  have := hL.nB; have := L.sp.isLt
  have h6 := P.R.n6
  have hw : P.w = P.R.E.n := rfl
  have hq' : L.q = 8 * P.R.E.n := hq
  have eD : (⟨State.addr L.d, 8 * P.R.E.n⟩ : Region) = L.D := by rw [Lay.D, hq']
  have eO : (⟨State.addr L.out, 16 * P.R.E.n⟩ : Region) = L.OUT := by rw [Lay.OUT, hq']; congr 1; omega
  simp only [coreK, State.withRegions_gpr, ce0, ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1,
    hr.r2, hr.r3, p2_arg0 (s := t) (by omega), hr.r12, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, pushed_sp, hk]
  simp only [eD, eO]
  refine ⟨?_, trivial, hL.oc, hL.dc, hL.gc.sub_left (Region.sub_prefix hn), hL.stk_SCR (by omega), ?_, ?_,
    by have := hL.no; omega, by have := hL.nd; omega, by have := hL.ng; omega, ?_, hL.nc, ?_⟩
  · rw [← eD, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_OUT (by omega)).symm
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, hsp]; exact (hL.stk_SCR (by omega)).symm
  · rw [fp_toNat hL (by omega)]; omega
  · rw [show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, VG.Arm.FrameStack.sub_toNat' (by omega)]; omega

theorem core_cov (hL : L.Ok) (hn : 8 * P.w ≤ dn) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) ((pushed [.r12, .lr] t).rd ++ (pushed [.r12, .lr] t).wr) :=
  covers_of fun q hq' => by
    have h6 := P.R.n6
    have hw : P.w = P.R.E.n := rfl
    rw [pushed_rd, pushed_wr, hc.rd, hc.wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, core_sp hL hc]
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ hn⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 16, 8⟩, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_covW (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreWr P L) (pushed [.r12, .lr] t).wr :=
  covers_of fun q hq' => by
    rw [pushed_wr, hc.wr]
    simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, V, scratch)`, in a frame of `{scratch, lr}`. -/
theorem core_ok (hL : L.Ok) (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (hr : CoreRegs L t) :
    WP isa (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame [L.OUT, L.SCR, ⟨L.B, 24⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 1 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (16 * P.w) = Spec.Ecdsa.encode P.R.E.C rs
      | none => BitVec.setWidth 32 (t'.gpr .r1 ++ t'.gpr .r0) = 0 ∧
          Spec.Sha256.bytesAt t'.mem (State.addr L.out) (16 * P.w) = List.replicate (16 * P.w) 0 := by
  have h24 := hc.sp24 hL
  have hst := hc.stk_eq hL
  have h6 := P.R.n6
  have hw : P.w = P.R.E.n := rfl
  have eW : coreWr P L = [L.OUT, L.SCR] := by
    simp only [coreWr, Lay.OUT, hq, List.cons.injEq, and_true]; congr 1; omega
  refine frame2_ok (ra := .r12) (rb := .lr) (t := .r12) rfl (by decide) P.R.coreX
    (by show armStack P.R.coreC ≤ 16; rw [P.R.coreStack]; omega) h24 (core_pre hL hq hn hc hr)
    (core_cov hL hn hq hc) (core_covW hq hc) fun s₂ ha hpost => ?_
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
  · have hk : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega)
    have hs : coreSigOf P.R.E (pushed [.r12, .lr] t).mem (State.addr L.d) (State.addr L.dg)
        (L.B + BitVec.ofNat 64 88) = coreSig P L t.mem := by
      have d1 : (stk t).Disjoint ⟨State.addr L.d, 8 * P.R.E.n⟩ := by
        rw [hst]; exact (hL.kd.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
      have d2 : (stk t).Disjoint ⟨State.addr L.dg, 8 * P.R.E.n⟩ := by
        rw [hst]; exact (hL.kg.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix hn)
      have d3 : (stk t).Disjoint ⟨L.B + BitVec.ofNat 64 88, 8 * P.R.E.n⟩ := by
        rw [hst]; exact Offset.base_disjoint _ (by omega) (by omega)
      simp only [coreSigOf, coreSig, Rfc6979.ecdsa_bytesAt]
      rw [p2_bytes h24 d1 (by omega), p2_bytes h24 d2 (by omega), p2_bytes h24 d3 (by omega)]
    simp only [coreK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0,
      ce1, ce2, ce3, pushed_gpr, hr.r0, hr.r1, hr.r2, hr.r3, hk, hs] at hpost
    rw [popped_gpr (by decide), popped_gpr (by decide), popped_mem]
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.Arm
