module
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# Deterministic ECDSA on AArch64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign_k` with the digest `X` (or, if `big`,
the one at `fXc`) and the candidate `T`, above the frame's pointers
(`core_ok`): it returns 1 and writes the signature, or returns 0 and writes
zeros, as `Spec.Ecdsa.signWith` gives for `d` and `Q` bytes of the digest
and of `k`, and changes only `out` and `scratch` (it pushes no frame: its
return address is in `x30`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {L : Lay dn P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d (dgArg P L) (kArg P L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and
the comb's tables. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region :=
  [⟨L.d, P.Q⟩, ⟨dgArg P L, P.Q⟩, ⟨kArg P L, P.Q⟩] ++ L.tables
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region := [⟨L.out, 2 * P.Q⟩, L.SCR]

/-- What `core`'s arguments need of the layout: the scalars' bytes. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : Prop := L.q = P.Q

/-- `core`'s digest and `k`: in the frame above its pointers, apart from
`out` and `scratch`. -/
theorem coreArg_ok (hL : L.Ok) (_hk : CoreOk P L) {x : Addr} (hx : x = dgArg P L ∨ x = kArg P L) :
    (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR := by
  have hQ : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he := L.he
  have key : ∀ o, 16 ≤ o → o + 66 ≤ 600 → (∃ R ∈ [L.D, L.DG, L.FR],
      Within ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ R) ∧ Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.SCR := fun o h₁ h₂ =>
    ⟨⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩, hL.stk_OUT (by omega), hL.stk_SCR (by omega)⟩
  simp only [dgArg, kArg] at hx
  rcases hx with h | rfl
  · split at h <;> subst h
    · exact key (16 + fXc) (by decide) (by decide)
    · exact key (16 + fX) (by decide) (by decide)
  · exact key (16 + fT) (by decide) (by decide)

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The comb's tables, as on entry. -/
theorem tbl_held (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : ∀ i < P.R.E.combWords.length,
    t.mem.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = P.R.E.combWords.getD i 0 := fun i hi => by
  have hT := hL.nT
  rw [hc.frame.readW (r := L.TBL) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.tOut
    · exact hL.tScr
    · exact hL.tStk) (by decide)]
  exact hc.held i hi

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out) (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = dgArg P L) (h3 : t.gpr .x3 = kArg P L)
    (h4 : t.gpr .x4 = L.scr) :
    (coreK P.R.E).pre (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have hq' : L.q = P.R.E.C.len := hk
  have eD : (⟨L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq']
  have eO : (⟨L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq']
  have no : L.out.toNat + 2 * P.R.E.C.len ≤ 2 ^ 64 := by have := hL.no; rw [hq'] at this; omega
  obtain ⟨-, gO, gS⟩ := coreArg_ok hL hk (.inl rfl)
  obtain ⟨-, kO, kS⟩ := coreArg_ok hL hk (.inr rfl)
  have sy : ∀ rd wr, tableAddr P.R.E (t.callEntry.withRegions rd wr).syms = L.T := fun _ _ => hc.sy
  simp only [coreK, TblOk, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3,
    h4, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, sy]
  exact ⟨by atriv, by atriv, hL.oc, hL.od, gO.symm, kO.symm, hL.dc, gS, kS, no, hL.nc, tbl_held hL hc,
    hL.nT, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.tOut.sub_right (Region.sub_prefix (by omega))
      · exact hL.tScr⟩

theorem core_covers (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) := by
  have hq : L.q = P.Q := hk
  have hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
      ∃ R ∈ ([L.D, L.DG, L.TAB] ++ L.tables) ++ [L.FR, L.LR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R :=
    fun ⟨R, hR, hW⟩ => ⟨R, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl <;> simp, hW⟩
  refine covers_of fun r hr => ?_
  rw [hc.rd, hc.wr]
  change r ∈ [⟨L.d, P.Q⟩, ⟨dgArg P L, P.Q⟩, ⟨kArg P L, P.Q⟩] ++ L.tables ++
    [⟨L.out, 2 * P.Q⟩, L.SCR] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.D, by simp, within_base _ (by omega)⟩
      · exact hw (coreArg_ok hL hk (.inl rfl)).1
      · exact hw (coreArg_ok hL hk (.inr rfl)).1
    · exact ⟨r, by simp [hr], within_base _ (Nat.le_refl _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_coversW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr P L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, k, scratch)`. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out) (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = dgArg P L) (h3 : t.gpr .x3 = kArg P L)
    (h4 : t.gpr .x4 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => (t'.gpr .x0).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => (t'.gpr .x0).setWidth 32 = 0 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have hq : L.q = P.Q := hk
  have eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine WP.of_syms (WP.call (k := coreK P.R.E) P.R.coreX (core_pre hL hk hc h0 h1 h2 h3 h4)
    (core_covers hL hk hc) (core_coversW hq hc) (fun t' hrd hwr hsp hf hcs _ hpost hsy => ?_) P.R.coreNoFrames)
  rw [eW] at hf
  refine ⟨hc.keep hL hrd hwr hsp hcs hf (hsy := hsy) fun r hr => ?_, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
  · simp only [coreK, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3, State.withRegions_mem, State.callEntry_mem,
      State.withRegions_gpr, Rfc6979.ecdsa_bytesAt] at hpost
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.AArch64
