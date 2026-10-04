import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes

/-!
# Deterministic ECDSA on x86-64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame (`core_ok`):
it returns 1 and writes the signature, or returns 0 and writes zeros, as
`Spec.Ecdsa.signWith` gives for `d`, the digest and `V`, and changes only
`out`, `scratch` and its return address.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem core_nosp (P : RfcHash) : NoSp P.R.coreC := Proof.Pbkdf2.Md.X86_64.nosp_of P.R.coreNs

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d L.dg (L.B + BitVec.ofNat 64 88)

/-- `core` reads the private key, and the leftmost `8 w` bytes of the digest and of `V`. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.d, 8 * P.w⟩, ⟨L.dg, 8 * P.w⟩, ⟨L.B + BitVec.ofNat 64 88, 8 * P.w⟩]
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨L.out, 16 * P.w⟩, L.SCR]

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The return address of a call from the frame. -/
theorem Ctx.ret {t : State} (hc : Ctx L g m₀ t) :
    (⟨t.callEntry.gpr .rsp, 8⟩ : Region) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ := by
  rw [State.callEntry_rsp, hc.rsp]
  congr 1
  bv_omega

/-- Bytes the return address misses, on entry to a call. -/
theorem ce_bytesAt {t : State} (hc : Ctx L g m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.B + BitVec.ofNat 64 16, 8⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt t.callEntry.mem p n = Spec.Sha256.bytesAt t.mem p n := by
  refine bytesAt_frame (ws := [below (t.gpr .rsp) 8]) ?_ (fun r hr => ?_) hn
  · exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.rsp]
    refine hd.sub_right fun a ha => ?_
    have e : L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8 = L.B + BitVec.ofNat 64 16 := by bv_omega
    simpa [below, e] using ha

theorem core_pre (hL : L.Ok) (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.out)
    (hsi : t.gpr .rsi = L.d) (hdx : t.gpr .rdx = L.dg) (hcx : t.gpr .rcx = L.B + BitVec.ofNat 64 88)
    (h8 : t.gpr .r8 = L.scr) :
    (coreK P.R.E).pre (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have hret := hc.ret
  have h6 : P.R.E.n ≤ 6 := P.R.n6
  have hq' : L.q = 8 * P.R.E.n := hq
  have hn' : 8 * P.R.E.n ≤ dn := hn
  have eD : (⟨L.d, 8 * P.R.E.n⟩ : Region) = L.D := by rw [Lay.D, hq']
  have eO : (⟨L.out, 16 * P.R.E.n⟩ : Region) = L.OUT := by rw [Lay.OUT, hq']; congr 1; omega
  have no : L.out.toNat + 16 * P.R.E.n ≤ 2 ^ 64 := by have := hL.no; rw [hq'] at this; omega
  simp only [coreK, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx, h8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
  rw [hret]
  exact ⟨by triv, by triv, hL.oc, hL.od, hL.og.sub_right (Region.sub_prefix hn'), (hL.stk_OUT (by omega)).symm,
    hL.dc, hL.gc.sub_left (Region.sub_prefix hn'), hL.stk_SCR (by omega), hL.stk_OUT (by omega),
    hL.stk_SCR (by omega), no, hL.nc⟩

theorem core_covers (hq : L.q = 8 * P.w) (hn : 8 * P.w ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) :=
  hc.covers fun r hr => by
    have h6 : P.w ≤ 6 := P.R.n6
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ hn⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
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
    (hdi : t.gpr .rdi = L.out)
    (hsi : t.gpr .rsi = L.d) (hdx : t.gpr .rdx = L.dg) (hcx : t.gpr .rcx = L.B + BitVec.ofNat 64 88)
    (h8 : t.gpr .r8 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => (t'.gpr .rax).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out (16 * P.w) = Spec.Ecdsa.encode P.R.E.C rs
      | none => (t'.gpr .rax).setWidth 32 = 0 ∧
          Spec.Sha256.bytesAt t'.mem L.out (16 * P.w) = List.replicate (16 * P.w) 0 := by
  have h6 : P.w ≤ 6 := P.R.n6
  have h6' : P.R.E.n ≤ 6 := P.R.n6
  have hsp : below (t.gpr .rsp) (8 * (P.R.coreC.depth + 1)) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ := by
    rw [P.R.coreD, hc.rsp]
    show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8, 8⟩ : Region) = _
    congr 1; bv_omega
  have eW : coreWr P L = [L.OUT, L.SCR] := by
    simp only [coreWr, Lay.OUT, hq, List.cons.injEq, and_true]; congr 1; omega
  refine WP.call (k := coreK P.R.E) P.R.coreX (core_nosp P)
    (by rw [P.R.coreD]; decide) (core_pre hL hq hn hc hdi hsi hdx hcx h8)
    (core_covers hq hn hc) (core_coversW hq hc) fun t' hrd hwr hcs hf _ ⟨s₂, hm, hg₂, hpost⟩ => ?_
  rw [hsp, eW] at hf
  refine ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf fun r hr => ?_, hf, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact safe_low L (by omega)
  · have hk : coreSigOf P.R.E t.callEntry.mem L.d L.dg (L.B + BitVec.ofNat 64 88) = coreSig P L t.mem := by
      simp only [coreSigOf, coreSig, ecdsa_bytesAt]
      rw [ce_bytesAt hc ((hL.stk_D (d := 16) (n := 8) (by omega)).symm.sub_left
          (Region.sub_prefix (by rw [hq]))) (by omega),
        ce_bytesAt hc ((hL.stk_DG (d := 16) (n := 8) (by omega)).symm.sub_left (Region.sub_prefix hn)) (by omega),
        ce_bytesAt hc (Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have hp := hpost
    simp only [coreK, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), hdi, hsi, hdx, hcx, State.withRegions_mem, hk, hm,
      hg₂ .rax (by decide)] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86_64
