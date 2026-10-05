import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes

/-!
# Deterministic ECDSA on AArch64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame (`core_ok`):
it returns 1 and writes the signature, or returns 0 and writes zeros, as
`Spec.Ecdsa.signWith` gives for `d`, the digest and `V`, and changes only
`out` and `scratch` (it pushes no frame: its return address is in `x30`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {L : Lay dn P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d L.dg (L.B + BitVec.ofNat 64 80)

/-- `core` reads the private key, the leftmost `8 w` bytes of the digest and
of `V`, and the comb's tables. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region :=
  [⟨L.d, 8 * P.w⟩, ⟨L.dg, 8 * P.w⟩, ⟨L.B + BitVec.ofNat 64 80, 8 * P.w⟩, L.TBL]
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region := [⟨L.out, 16 * P.w⟩, L.SCR]

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

theorem core_pre (hL : L.Ok) (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out)
    (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = L.dg) (h3 : t.gpr .x3 = L.B + BitVec.ofNat 64 80)
    (h4 : t.gpr .x4 = L.scr) :
    (coreK P.R.E).pre (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have h6 : P.R.E.n ≤ 6 := P.R.n6
  have hq' : L.q = 8 * P.R.E.n := hq
  have hn' : 8 * P.R.E.n ≤ dn := hn
  have eD : (⟨L.d, 8 * P.R.E.n⟩ : Region) = L.D := by rw [Lay.D, hq']
  have eO : (⟨L.out, 16 * P.R.E.n⟩ : Region) = L.OUT := by rw [Lay.OUT, hq']; congr 1; omega
  have no : L.out.toNat + 16 * P.R.E.n ≤ 2 ^ 64 := by have := hL.no; rw [hq'] at this; omega
  have sy : ∀ rd wr, (t.callEntry.withRegions rd wr).syms P.R.E.tsym = L.T := fun _ _ => hc.sy
  simp only [coreK, TblOk, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3,
    h4, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, sy]
  exact ⟨by atriv, by atriv, hL.oc, hL.od, hL.og.sub_right (Region.sub_prefix hn'), (hL.stk_OUT (by omega)).symm,
    hL.dc, hL.gc.sub_left (Region.sub_prefix hn'), hL.stk_SCR (by omega), no, hL.nc, tbl_held hL hc,
    hL.nT, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.tOut.sub_right (Region.sub_prefix (by omega))
      · exact hL.tScr⟩

theorem core_covers (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    have h6 : P.w ≤ 6 := P.R.n6
    rw [hc.rd, hc.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ hn⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨L.TBL, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_coversW (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr P L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, V, scratch)`. -/
theorem core_ok (hL : L.Ok) (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out)
    (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = L.dg) (h3 : t.gpr .x3 = L.B + BitVec.ofNat 64 80)
    (h4 : t.gpr .x4 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => (t'.gpr .x0).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out (16 * P.w) = Spec.Ecdsa.encode P.R.E.C rs
      | none => (t'.gpr .x0).setWidth 32 = 0 ∧
          Spec.Sha256.bytesAt t'.mem L.out (16 * P.w) = List.replicate (16 * P.w) 0 := by
  have eW : coreWr P L = [L.OUT, L.SCR] := by
    simp only [coreWr, Lay.OUT, hq, List.cons.injEq, and_true]; congr 1; omega
  refine WP.of_syms (WP.call (k := coreK P.R.E) P.R.coreX (core_pre hL hq hn hc h0 h1 h2 h3 h4)
    (core_covers hq hn hc) (core_coversW hq hc) (fun t' hrd hwr hsp hf hcs _ hpost hsy => ?_) P.R.coreNoFrames)
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
