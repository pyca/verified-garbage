import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes

/-!
# Deterministic ECDSA on x86-64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame, or, if two
`V`s make a candidate, the digest and the candidate above the frame's
pointers (`core_ok`): it returns 1 and writes the signature, or returns 0
and writes zeros, as `Spec.Ecdsa.signWith` gives for `d`, the digest and
`k`, and changes only `out`, `scratch` and its return address.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem core_nosp (P : RfcHash) : NoSp P.R.coreC := Proof.Pbkdf2.Md.X86_64.nosp_of P.R.coreNs

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d (dgArg P L) (kArg P L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and the comb's tables. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region :=
  [⟨L.d, P.Q⟩, ⟨dgArg P L, P.Q⟩, ⟨kArg P L, P.Q⟩] ++ L.TBLs
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn) : List Region := [⟨L.out, 2 * P.Q⟩, L.SCR]

/-- What `core`'s digest and `k` need of the layout: unless two `V`s make a
candidate, the digest has `Q` bytes; if they do, the frame has the words
above its pointers; and the tables are the comb's. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ (P.R.wide = false → P.Q ≤ dn) ∧ L.e = P.e ∧ L.cs = P.R.E.combConsts

/-- `core`'s digest and `k`: in the digest or the frame, apart from `out`,
`scratch` and the return address of a call from the frame. -/
theorem coreArg_ok (hL : L.Ok) (hk : CoreOk P L) {x : Addr} (hx : x = dgArg P L ∨ x = kArg P L) :
    (∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B + BitVec.ofNat 64 8, 16⟩ := by
  have hQ := P.sizes
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hn := hk.2.1 hw
    simp only [dgArg, kArg, hw, Bool.false_eq_true, ite_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨L.DG, by simp, within_base _ hn⟩, hL.og.symm.sub_left (Region.sub_prefix hn),
        hL.gc.sub_left (Region.sub_prefix hn), ((hL.stk_DG (d := 8) (n := 16) (by omega)).symm.sub_left
          (Region.sub_prefix hn))⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, (hL.stk_OUT (by omega)),
        hL.stk_SCR (by omega), Offset.disjoint _ (by omega) (by omega) (by omega)⟩
  · obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hw
    have he : L.e = 18 := by rw [hk.2.2.1]; simp only [RfcHash.e, hw, ite_true]
    simp only [dgArg, kArg, hw, ite_true] at hx
    rcases hx with rfl | rfl
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, (hL.stk_OUT (by omega)),
        hL.stk_SCR (by omega), Offset.disjoint _ (by omega) (by omega) (by omega)⟩
    · exact ⟨⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩, (hL.stk_OUT (by omega)),
        hL.stk_SCR (by omega), Offset.disjoint _ (by omega) (by omega) (by omega)⟩

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

/-- The comb's tables, at the addresses the state gives their statics. -/
theorem Ctx.tbls (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Abi.constRegions (fun n => t.syms n) P.R.E.combConsts = L.TBLs := by
  rw [Lay.TBLs, ← hk.2.2.2]; exact constRegions_congr hc.sy

/-- The comb's tables, as on entry, on entry to a call from the frame. -/
theorem tbl_held (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Abi.constsHeld t.callEntry.mem (fun n => t.syms n) P.R.E.combConsts := fun c hc' i hi => by
  have hcs : c ∈ L.cs := by rw [hk.2.2.2]; exact hc'
  show t.callEntry.mem.readW (t.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
  rw [hc.sy c hcs]
  obtain ⟨hn, tO, tS, tK⟩ := hL.tbl ⟨L.sy c.1, 8 * c.2.length⟩
    (List.mem_map_of_mem (f := fun c => (⟨L.sy c.1, 8 * c.2.length⟩ : Region)) hcs)
  simp only at hn
  have hce : Frame [below (t.gpr .rsp) 8] t.mem t.callEntry.mem :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  have hf : Frame [L.OUT, L.SCR, L.STK] m₀ t.callEntry.mem := hc.frame.trans (hce.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, (hc.below_sub (n := 8) (by omega)).trans (Region.sub_prefix (by omega))⟩)
  rw [hf.readW (r := ⟨L.sy c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact tO
    · exact tS
    · exact tK) (by decide)]
  exact hc.held c hcs i hi

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.out) (hsi : t.gpr .rsi = L.d) (hdx : t.gpr .rdx = dgArg P L) (hcx : t.gpr .rcx = kArg P L)
    (h8 : t.gpr .r8 = L.scr) :
    (coreK P.R.E).pre (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have hret := hc.ret
  have hq : L.q = P.R.E.C.len := hk.1
  have eD : (⟨L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq]
  have eO : (⟨L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq]
  have no : L.out.toNat + 2 * P.R.E.C.len ≤ 2 ^ 64 := by have := hL.no; rw [hq] at this; omega
  obtain ⟨-, gO, gS, gR⟩ := coreArg_ok hL hk (.inl rfl)
  obtain ⟨-, kO, kS, -⟩ := coreArg_ok hL hk (.inr rfl)
  have ht := hc.tbls hk
  have hT : ∀ T ∈ Abi.constRegions (fun n => t.syms n) P.R.E.combConsts, T.base.toNat + T.len ≤ 2 ^ 64 ∧
      ∀ r ∈ [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 16, 8⟩], T.Disjoint r := fun T hT => by
    rw [ht] at hT
    obtain ⟨hn, tO, tS, tK⟩ := hL.tbl T hT
    refine ⟨hn, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact tO
    · exact tS
    · exact tK.sub_right (Offset.sub_base _ (by omega))
  simp only [coreK, TblsOk, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx, h8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
  rw [hret]
  exact ⟨(congrArg (fun x => [L.D, (⟨dgArg P L, P.Q⟩ : Region), ⟨kArg P L, P.Q⟩] ++ x) ht).symm, by triv, hL.oc,
    hL.od, gO.symm, kO.symm, hL.dc, gS, kS, (hL.stk_OUT (by omega)).symm.symm, hL.stk_SCR (by omega), no, hL.nc,
    tbl_held hL hk hc, hT⟩

/-- Nothing `core` reads or writes is in the 8 bytes below its `rsp`,
where its own calls store their return addresses. -/
theorem core_clear (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Clear (hole ((t.callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .rsp))
      (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have hq : L.q = P.Q := hk.1
  have hh : hole ((t.callEntry.withRegions (coreRd P L) (coreWr P L)).gpr .rsp) =
      ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hc.rsp]
    show (⟨L.B + BitVec.ofNat 64 24 - 8 - 8, 8⟩ : Region) = _
    congr 1; bv_omega
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.B + BitVec.ofNat 64 8, 16⟩ := Region.sub_prefix (by omega)
  rw [hh]
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, coreRd, coreWr, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | hr | rfl | rfl
  · rw [← hq]; exact (hL.stk_d (by omega)).symm
  · exact (coreArg_ok hL hk (.inl rfl)).2.2.2.sub_right hs
  · exact (coreArg_ok hL hk (.inr rfl)).2.2.2.sub_right hs
  · exact (hL.tbl r hr).2.2.2.sub_right (Offset.sub_base _ (by omega))
  · rw [show (⟨L.out, 2 * P.Q⟩ : Region) = L.OUT by simp only [Lay.OUT, hq]]; exact (hL.stk_OUT (by omega)).symm
  · exact (hL.stk_SCR (by omega)).symm

theorem core_covers (hk : CoreOk P L) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    have hq : L.q = P.Q := hk.1
    have m : ∀ {R}, R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR] → R ∈ t.rd ++ t.wr := fun h => by
      rw [hc.rd, hc.wr]; exact Ctx.mem_regions h
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr | rfl | rfl
    · exact ⟨L.D, m (by simp), within_base _ (by omega)⟩
    · obtain ⟨R, hR, hw⟩ := (coreArg_ok hL hk (.inl rfl)).1; exact ⟨R, m hR, hw⟩
    · obtain ⟨R, hR, hw⟩ := (coreArg_ok hL hk (.inr rfl)).1; exact ⟨R, m hR, hw⟩
    · exact ⟨r, by rw [hc.rd]; simp [hr], 0, (BitVec.add_zero _).symm, by omega⟩
    · exact ⟨L.OUT, m (by simp), within_base _ (by omega)⟩
    · exact ⟨L.SCR, m (by simp), within_base _ (by omega)⟩

theorem core_coversW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr P L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, k, scratch)`. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.out) (hsi : t.gpr .rsi = L.d) (hdx : t.gpr .rdx = dgArg P L) (hcx : t.gpr .rcx = kArg P L)
    (h8 : t.gpr .r8 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 8, 16⟩] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => (t'.gpr .rax).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => (t'.gpr .rax).setWidth 32 = 0 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have hq : L.q = P.Q := hk.1
  have hD := P.R.coreD
  have hsp : Region.Sub (below (t.gpr .rsp) (8 * (P.R.coreC.depth + 1))) ⟨L.B + BitVec.ofNat 64 8, 16⟩ := by
    rw [hc.rsp]
    rcases (show P.R.coreC.depth = 0 ∨ P.R.coreC.depth = 1 by omega) with h | h <;> rw [h]
    · rw [show below (L.B + BitVec.ofNat 64 24) (8 * (0 + 1)) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ by
        show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8, 8⟩ : Region) = _
        congr 1; bv_omega]
      exact Offset.sub _ (by omega) (by omega)
    · rw [show below (L.B + BitVec.ofNat 64 24) (8 * (1 + 1)) = ⟨L.B + BitVec.ofNat 64 8, 16⟩ by
        show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 16, 16⟩ : Region) = _
        congr 1; bv_omega]
      exact sub_refl _
  have eW : coreWr P L = [L.OUT, L.SCR] := by
    simp only [coreWr, Lay.OUT, hq]
  refine WP.of_syms (WP.call (k := (coreK P.R.E).clear) (fun s h => P.R.coreX s h.1 h.2) (core_nosp P)
    (by omega) ⟨core_pre hL hk hc hdi hsi hdx hcx h8, core_clear hL hk hc⟩
    (core_covers hk hL hc) (core_coversW hq hc) fun t' hrd hwr hcs hf _ ⟨s₂, hm, hg₂, hpost⟩ hsy => ?_)
  rw [eW] at hf
  replace hf : Frame [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 8, 16⟩] t.mem t'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, sub_refl _⟩
    · exact ⟨_, by simp, hsp⟩
  refine ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_, hf,
    ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact safe_low L (by omega)
  · obtain ⟨-, -, -, gR⟩ := coreArg_ok hL hk (.inl rfl)
    obtain ⟨-, -, -, kR⟩ := coreArg_ok hL hk (.inr rfl)
    have hQl : P.R.E.C.len ≤ 72 := by have := P.R.len_words; have := P.R.n9; omega
    have hQl' : P.Q ≤ 72 := hQl
    have hk' : coreSigOf P.R.E t.callEntry.mem L.d (dgArg P L) (kArg P L) = coreSig P L t.mem := by
      simp only [coreSigOf, coreSig, ecdsa_bytesAt]
      rw [ce_bytesAt hc ((hL.stk_D (d := 16) (n := 8) (by omega)).symm.sub_left
          (Region.sub_prefix (by rw [hq]))) (by omega),
        ce_bytesAt hc (gR.sub_right (Offset.sub _ (by omega) (by omega))) (by omega),
        ce_bytesAt hc (kR.sub_right (Offset.sub _ (by omega) (by omega))) (by omega)]
    have hp : (coreK P.R.E).post (t.callEntry.withRegions (coreRd P L) (coreWr P L)) s₂ := hpost
    simp only [coreK, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), hdi, hsi, hdx, hcx, State.withRegions_mem, hk', hm,
      hg₂ .rax (by decide)] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86_64
