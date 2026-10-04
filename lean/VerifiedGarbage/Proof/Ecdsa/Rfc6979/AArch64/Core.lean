import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Blocks
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes

/-!
# Deterministic ECDSA on AArch64: signing with a candidate

The call of `vg_ecdsa_p256_sign` with `k = V` from the frame (`core_ok`):
it returns 1 and writes the signature, or returns 0 and writes zeros, as
`Spec.Ecdsa.signWith` gives for `d`, the digest and `V`, and changes only
`out` and `scratch` (it pushes no frame: its return address is in `x30`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem core_noFrames : Impl.Ecdsa.AArch64.signP256.noFrames = true := by lit_decide

/-- The signature `core` computes, or none. -/
abbrev coreSig {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  Proof.Ecdsa.AArch64.sig m L.d L.dg (L.B + BitVec.ofNat 64 80)

/-- `core` reads the private key, and the leftmost 32 bytes of the digest and of `V`. -/
abbrev coreRd {dn : Nat} (L : Lay dn) : List Region := [L.D, ⟨L.dg, 32⟩, ⟨L.B + BitVec.ofNat 64 80, 32⟩]
abbrev coreWr {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR]

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem core_pre (hL : L.Ok) (hn : 32 ≤ dn) {t : State} (h0 : t.gpr .x0 = L.out)
    (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = L.dg) (h3 : t.gpr .x3 = L.B + BitVec.ofNat 64 80)
    (h4 : t.gpr .x4 = L.scr) :
    Proof.Ecdsa.AArch64.signAArch64.pre (t.callEntry.withRegions (coreRd L) (coreWr L)) := by
  simp only [Proof.Ecdsa.AArch64.signAArch64, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3,
    h4, State.withRegions_rd, State.withRegions_wr]
  exact ⟨by atriv, by atriv, hL.oc, hL.od, hL.og.sub_right (Region.sub_prefix hn), (hL.stk_OUT (by omega)).symm,
    hL.dc, hL.gc.sub_left (Region.sub_prefix hn), hL.stk_SCR (by omega), hL.no, hL.nc⟩

theorem core_covers (hn : 32 ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd L ++ coreWr L) (t.rd ++ t.wr) :=
  hc.covers fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ hn⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_coversW {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, V, scratch)`. -/
theorem core_ok (hL : L.Ok) (hn : 32 ≤ dn) {t : State} (hc : Ctx L g m₀ t) (h0 : t.gpr .x0 = L.out)
    (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = L.dg) (h3 : t.gpr .x3 = L.B + BitVec.ofNat 64 80)
    (h4 : t.gpr .x4 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR] t.mem t'.mem ∧
      match coreSig L t.mem with
      | some rs => (t'.gpr .x0).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out 64 = Spec.Ecdsa.encode Spec.P256.curve rs
      | none => (t'.gpr .x0).setWidth 32 = 0 ∧ Spec.Sha256.bytesAt t'.mem L.out 64 = List.replicate 64 0 := by
  refine WP.call (k := Proof.Ecdsa.AArch64.signAArch64) P.coreX (core_pre hL hn h0 h1 h2 h3 h4)
    (core_covers hn hc) (core_coversW hc) (fun t' hrd hwr hsp hf hcs _ hpost => ?_) core_noFrames
  refine ⟨hc.keep hL hrd hwr hsp hcs hf fun r hr => ?_, hf, ?_⟩
  · simp only [coreWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
  · simp only [Proof.Ecdsa.AArch64.signAArch64, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3, State.withRegions_mem, State.callEntry_mem,
      State.withRegions_gpr, Rfc6979.ecdsa_bytesAt] at hpost
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.AArch64
