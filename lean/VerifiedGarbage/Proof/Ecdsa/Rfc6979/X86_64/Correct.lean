module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Cand
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Prep
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ecdsa.Rfc6979.X86_64.Loop`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.X86_64.Core`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign` with `k = V` from the frame, or, if two
`V`s make a candidate, the digest and the candidate above the frame's
pointers (`core_ok`): it returns 1 and writes the signature, or returns 0
and writes zeros, as `Spec.Ecdsa.signWith` gives for `d`, the digest and
`k`, and changes only `out`, `scratch` and its return address.
-/

@[expose] public section

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

/-- What `core`'s arguments need of the layout: the scalars' bytes, the
comb's tables, and the table of `P`. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop :=
  L.q = P.Q ∧ L.cs = P.R.E.combConsts ∧ L.H = P.H ∧ L.f = P.f

/-- `core`'s digest and `k`: in the frame above its pointers, apart from
`out`, `scratch` and the return address of a call from the frame. -/
theorem coreArg_ok (hL : L.Ok) {x : Addr} (hx : x = dgArg P L ∨ x = kArg P L) :
    (∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR ∧ Region.Disjoint ⟨x, P.Q⟩ ⟨L.B + BitVec.ofNat 64 8, 16⟩ := by
  have hQ : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he := L.he
  have key : ∀ o, 240 ≤ o → o + 66 ≤ 624 → (∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR],
      Within ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ R) ∧ Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.SCR ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ ⟨L.B + BitVec.ofNat 64 8, 16⟩ := fun o h₁ h₂ =>
    ⟨⟨L.FR, by simp, within_fr _ (by omega_using [h₁]) (by omega_using [hQ, he, h₂])⟩,
      (hL.stk_OUT (by omega_using [hQ, he, h₂])), hL.stk_SCR (by omega_using [hQ, he, h₂]),
      Offset.disjoint _ (by omega_using [h₁]) (by omega_using [hQ, h₂]) (by omega_using [])⟩
  simp only [dgArg, kArg] at hx
  rcases hx with h | rfl
  · split at h <;> subst h
    · exact key (24 + fXc) (by decide) (by decide)
    · exact key (24 + fX) (by decide) (by decide)
  · exact key (24 + fT) (by decide) (by decide)

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
  · exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_using []) (by omega_using []))
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.rsp]
    refine hd.sub_right fun a ha => ?_
    have e : L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8 = L.B + BitVec.ofNat 64 16 := by bv_omega
    simpa [below, e] using ha

/-- The comb's tables, at the addresses the state gives their statics. -/
theorem Ctx.tbls (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Abi.constRegions (fun n => t.syms n) P.R.E.combConsts = L.TBLs := by
  rw [Lay.TBLs, ← hk.2.1]; exact constRegions_congr hc.sy

/-- The comb's tables, as on entry, on entry to a call from the frame. -/
theorem tbl_held (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Abi.constsHeld t.callEntry.mem (fun n => t.syms n) P.R.E.combConsts := fun c hc' i hi => by
  have hcs : c ∈ L.cs := by rw [hk.2.1]; exact hc'
  show t.callEntry.mem.readW (t.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
  rw [hc.sy c hcs]
  obtain ⟨hn, tO, tS, tK⟩ := hL.tbl ⟨L.sy c.1, 8 * c.2.length⟩
    (List.mem_map_of_mem (f := fun c => (⟨L.sy c.1, 8 * c.2.length⟩ : Region)) hcs)
  simp only at hn
  have hce : Frame [below (t.gpr .rsp) 8] t.mem t.callEntry.mem :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_using []) (by omega_using []))
  have hf : Frame [L.OUT, L.SCR, L.STK] m₀ t.callEntry.mem := hc.frame.trans (hce.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, (hc.below_sub (n := 8) (by omega_using [])).trans (Region.sub_prefix (by omega_using []))⟩)
  rw [hf.readW (r := ⟨L.sy c.1, 8 * c.2.length⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hn])) (fun r hr => by
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
  have no : L.out.toNat + 2 * P.R.E.C.len ≤ 2 ^ 64 := by have := hL.no; rw [hq] at this; omega_using [this]
  obtain ⟨-, gO, gS, gR⟩ := coreArg_ok (P := P) hL (.inl rfl)
  obtain ⟨-, kO, kS, -⟩ := coreArg_ok (P := P) hL (.inr rfl)
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
    · exact tK.sub_right (Offset.sub_base _ (by omega_using []))
  simp only [coreK, TblsOk, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx, h8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
  rw [hret]
  exact ⟨(congrArg (fun x => [L.D, (⟨dgArg P L, P.Q⟩ : Region), ⟨kArg P L, P.Q⟩] ++ x) ht).symm, by triv, hL.oc,
    hL.od, gO.symm, kO.symm, hL.dc, gS, kS, (hL.stk_OUT (by omega_using [])).symm.symm, hL.stk_SCR (by omega_using []), no, hL.nc,
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
  have hs : Region.Sub ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.B + BitVec.ofNat 64 8, 16⟩ := Region.sub_prefix (by omega_using [])
  rw [hh]
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, coreRd, coreWr, List.cons_append, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | hr | rfl | rfl
  · rw [← hq]; exact (hL.stk_d (by omega_using [])).symm
  · exact (coreArg_ok (P := P) hL (.inl rfl)).2.2.2.sub_right hs
  · exact (coreArg_ok (P := P) hL (.inr rfl)).2.2.2.sub_right hs
  · exact (hL.tbl r hr).2.2.2.sub_right (Offset.sub_base _ (by omega_using []))
  · rw [show (⟨L.out, 2 * P.Q⟩ : Region) = L.OUT by simp only [Lay.OUT, hq]]; exact (hL.stk_OUT (by omega_using [])).symm
  · exact (hL.stk_SCR (by omega_using [])).symm

theorem core_covers (hk : CoreOk P L) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) :=
  covers_of fun r hr => by
    have hq : L.q = P.Q := hk.1
    have m : ∀ {R}, R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR] → R ∈ t.rd ++ t.wr := fun h => by
      rw [hc.rd, hc.wr]; exact Ctx.mem_regions h
    simp only [coreRd, coreWr, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | hr | rfl | rfl
    · exact ⟨L.D, m (by simp), within_base _ (by omega_using [hq])⟩
    · obtain ⟨R, hR, hw⟩ := (coreArg_ok (P := P) hL (.inl rfl)).1; exact ⟨R, m hR, hw⟩
    · obtain ⟨R, hR, hw⟩ := (coreArg_ok (P := P) hL (.inr rfl)).1; exact ⟨R, m hR, hw⟩
    · exact ⟨r, by rw [hc.rd]; simp [hr], 0, (BitVec.add_zero _).symm, by omega_using []⟩
    · exact ⟨L.OUT, m (by simp), within_base _ (by omega_using [hq])⟩
    · exact ⟨L.SCR, m (by simp), within_base _ (by omega_using [])⟩

theorem core_coversW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr P L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega_using [hq])⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_using [])⟩

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
    rcases (show P.R.coreC.depth = 0 ∨ P.R.coreC.depth = 1 by omega_using [hD]) with h | h <;> rw [h]
    · rw [show below (L.B + BitVec.ofNat 64 24) (8 * (0 + 1)) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ by
        show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8, 8⟩ : Region) = _
        congr 1; bv_omega]
      exact Offset.sub _ (by omega_using []) (by omega_using [])
    · rw [show below (L.B + BitVec.ofNat 64 24) (8 * (1 + 1)) = ⟨L.B + BitVec.ofNat 64 8, 16⟩ by
        show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 16, 16⟩ : Region) = _
        congr 1; bv_omega]
      exact sub_refl _
  have eW : coreWr P L = [L.OUT, L.SCR] := by
    simp only [coreWr, Lay.OUT, hq]
  refine WP.of_syms (WP.call (k := (coreK P.R.E).clear) (fun s h => P.R.coreX s h.1 h.2) (core_nosp P)
    (by omega_using [hD]) ⟨core_pre hL hk hc hdi hsi hdx hcx h8, core_clear hL hk hc⟩
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
    · exact safe_low L (by omega_using [])
  · obtain ⟨-, -, -, gR⟩ := coreArg_ok (P := P) hL (.inl rfl)
    obtain ⟨-, -, -, kR⟩ := coreArg_ok (P := P) hL (.inr rfl)
    have hQl : P.R.E.C.len ≤ 72 := by have := P.R.len_words; have := P.R.n9; omega_arith
    have hQl' : P.Q ≤ 72 := hQl
    have hk' : coreSigOf P.R.E t.callEntry.mem L.d (dgArg P L) (kArg P L) = coreSig P L t.mem := by
      simp only [coreSigOf, coreSig, ecdsa_bytesAt]
      rw [ce_bytesAt hc ((hL.stk_D (d := 16) (n := 8) (by omega_using [])).symm.sub_left
          (Region.sub_prefix (by rw [hq]))) (by omega_using [hQl]),
        ce_bytesAt hc (gR.sub_right (Offset.sub _ (by omega_using []) (by omega_using []))) (by omega_using [hQl']),
        ce_bytesAt hc (kR.sub_right (Offset.sub _ (by omega_using []) (by omega_using []))) (by omega_using [hQl'])]
    have hp : (coreK P.R.E).post (t.callEntry.withRegions (coreRd P L) (coreWr P L)) s₂ := hpost
    simp only [coreK, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), hdi, hsi, hdx, hcx, State.withRegions_mem, hk', hm,
      hg₂ .rax (by decide)] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end


/-!
# Deterministic ECDSA on x86-64: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the candidate's `k` for `core` (`cand_ok`); the loop's invariant
before candidate `i` (`LoopInv`): `K` and `V` are those before it, the count
is `tries - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1`,
branching back, or leaves the loop with the signature of candidate `i`,
which is suitable or the last (`tryOne_ok`, `loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgArg P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .rax).setWidth 32 = 1 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => (t.gpr .rax).setWidth 32 = 0 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem
  saved : SavedK P L t.mem (kOf P L t.mem)

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem hok_of (hk : CoreOk P L) : HOk P L := ⟨hk.1, hk.2.2.1, hk.2.2.2⟩

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 200, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 200, 8⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by nums)
  · exact Offset.disjoint_base _ (by nums) (by nums)

theorem cw_cnt (hL : L.Ok) : ∀ r ∈ CW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 200, 8⟩ r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]
  have := L.he
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_SCR (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_arith)) (by omega_arith) (by simp only [fT]; omega_arith)

/-- What `core` changes: `out`, `scratch` and the return addresses of it and its calls. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 8, 16⟩]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 248 + 8 * L.e) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  have := L.he
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint _ (by nums) (by nums) (by nums)

/-- The regions the loop writes, which are apart from `core`'s digest. -/
def DgApart {dn : Nat} (L : Lay dn) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 152⟩ ∨ r = ⟨L.B, 160⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 16, 8⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 200, 8⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 (24 + fT), 136⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 8, 16⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 24, 128⟩

theorem dg_apart (hL : L.Ok) {r : Region} (h : DgApart L r) : Region.Disjoint ⟨dgArg P L, P.Q⟩ r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have he := L.he
  have key : ∀ o, 256 ≤ o → o + P.Q ≤ 24 + fT → Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ r := by
    intro o h₁ h₂
    simp only [fT] at h₂
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact hL.stk_OUT (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_arith)) (by omega_arith) (by simp only [fT]; omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [dgArg]
  split
  · exact key _ (by simp only [fXc]; omega_arith) (by simp only [fXc, fT]; omega_arith)
  · exact key _ (by simp only [fX]; omega_arith) (by simp only [fX, fT]; omega_arith)

theorem DgOk.frame {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨dgArg P L, P.Q⟩ r) : DgOk P L m₀ m' := by
  have hQ : P.Q ≤ 72 := by nums
  unfold DgOk; rw [bytesAt_frame hf hd (by omega_arith)]; exact h

theorem DgOk.frameOf (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, DgApart L r) : DgOk P L m₀ m' :=
  h.frame hf fun r hr => dg_apart hL (hd r hr)

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 64 (T - i) - 1 = BitVec.ofNat 64 (T - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega_arith

theorem cnt_ne {T i : Nat} (hT : T < 2 ^ 32) : BitVec.ofNat 64 (T - (i + 1)) ≠ 0 ↔ i + 1 < T := by
  rw [Ne, ← BitVec.toNat_inj]
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h0]
  omega_arith

/-- `core`'s signature is the candidate's: it reads the private key, its
digest, and `k`, whose number is `bits2int` of the candidate. -/
theorem coreSig_eq (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg P L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  have e₄ : Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := hc.dBytes hL (by rw [hk.1])
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, xOf]
  rw [show Spec.Sha256.bytesAt t.mem (dgArg P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (dgArg P L) P.Q from rfl,
    hdg, show Spec.Sha256.bytesAt t.mem L.d P.R.E.C.len = Spec.Sha256.bytesAt t.mem L.d P.Q from rfl, e₄,
    show Spec.Sha256.bytesAt t.mem (kArg P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (kArg P L) P.Q from rfl, hkv]

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    (t.gpr .rax).setWidth 32 = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `rax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .rax = t.gpr .rax)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)

/-- `core`'s arguments. -/
structure Args (P : RfcHash) {dn : Nat} (L : Lay dn) (u : State) : Prop where
  rdi : u.gpr .rdi = L.out
  rsi : u.gpr .rsi = L.d
  rdx : u.gpr .rdx = dgArg P L
  rcx : u.gpr .rcx = kArg P L
  r8 : u.gpr .r8 = L.scr

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval .ne u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem kvw_apart : ∀ r ∈ KVW L, DgApart L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem cw_apart : ∀ r ∈ CW L, DgApart L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem corew_apart : ∀ r ∈ CoreW L, DgApart L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem try₁_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL (hok_of hk).2 hc hi.saved) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, _⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_frame hf₁ (cw_cnt hL)).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₁ cw_apart, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ Args P L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, hdi, hsi, hdx, hcx, h8⟩

theorem try₃_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : Args P L t) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok (P := P) hL hk hc ha.rdi ha.rsi ha.rdx ha.rcx ha.r8) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hk hc hi.dg hi.kk] at hr₃
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by nums) (by nums)) (by nums)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by nums) (by nums)) (by nums)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by nums) (by nums))).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₃ corew_apart, hr₃⟩

theorem try₄_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails,
    hi.dg.frameOf hL hf₄ (by simp [DgApart]), ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by nums)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))
  · show u₄.zf.map (!·) = _
    rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [Option.map_some, Bool.not_not, hi.res.eax_zero, cnt_ne P.tries_lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite .ne (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL (hok_of hk) hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅, hS₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨by show u₆.zf.map _ = _; rw [hz₆]; rfl, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_, by rw [hm₆]; exact hS₅⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [hm₆]; exact hi.dg.frameOf hL hf₅ kvw_apart
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨by show u₅.zf.map _ = _; rw [hz₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega_arith)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hk hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hk h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hk h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hk h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end


/-!
# Deterministic ECDSA on x86-64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_using [this]) (by show 8 * P.R.E.C.len < _; omega_using [this])

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D x hB =
      let K₁ := P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega_using [h]), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega_using [h]) hn).1]

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fX)) P.Q =
    List.replicate (P.Q - min P.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hT : TabL P L := (hok_of hk).2
  have hD : P.H.D = P.I.hashLen := P.len.symm
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.H.D P.Q) =
      (hBOf P L m₀).take (min P.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega_using []), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hT (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hk : CoreOk P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hT : TabL P L := (hok_of hk).2
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlB : (hBOf P L m₀).length = P.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xa L) P.Q) = eOf P L m₀ := by
      rw [show xa L = L.B + BitVec.ofNat 64 (24 + fX) from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 24 + fH = hB from rfl, hh₂, hX, hSpec, Spec.Ecdsa.Rfc6979.bits2octets,
        Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgArg, hb, Bool.false_eq_true, ite_false]
      obtain ⟨-, -, hQ64⟩ := P.sizesA hb
      obtain ⟨-, hb₂, -, -, -, -, hb₇⟩ := hb_facts (L := L) hb
      simp only [fX] at hb₇
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [])) (by simp only [fX]; omega_using [hQ66]) (by omega_using [])
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [hb₂, hb₇])) (by simp only [fX]; omega_using [hQ66])
              (by omega_using [hb₂, hb₇])) (by omega_using [hQ66]),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', hQD⟩ := P.sizesW hb
    have hN : 8 * P.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.H.D < P.R.E.C.len := hQD
      omega_using [hl, this]
    have hm : min P.H.D P.Q = P.H.D := Nat.min_eq_left (by omega_using [hD64, hQ66'])
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hT hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by have := L.he; simp only [fX]; omega_using [hQ66, this]) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega_using [hQ66])) (by simp only [fX]; omega_using [hQ66])
              (by simp only [fXc]; omega_using [])) (by omega_using [hQ66]),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
          (by show 8 * P.R.E.C.len < _; omega_using [hl]) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_using []) (by simp only [RfcHash.Q]; omega_using [hl, hN])
      have hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgArg, hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl]) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = ⟨L.B, 152⟩ ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 24 + fH) :
    hOf P L m' = hOf P L m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have he := L.he
  have hho : 24 + fH ≤ 24 + (cfgOf P).fHo ∧ 24 + (cfgOf P).fHo + P.Q ≤ 24 + fXc := by
    simp only [Cfg.fHo]; split <;> simp only [fH, fX, fXc] <;> omega_using [hQ66]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hQ66])
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by simp only [fXc] at hho; omega_using [he, hho])
  · exact Offset.disjoint_base _ (by simp only [fH] at hho; omega_using [hho]) (by simp only [fXc] at hho; omega_using [hho])
  · exact Offset.disjoint _ (.inr (by omega_using [hho, hon])) (by simp only [fXc] at hho; omega_using [hho]) (by simp only [fH] at hon; omega_using [hon])

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨24, 128, rfl, by simp only [fH]; omega_using []⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frameOf hL hf₂ (by simp [DgApart])⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0 fun h => absurd rfl h) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 1 fun _ => hq.saved) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart]),
    by
      have hk' : kOf P L u'.mem = kOf P L u.mem := bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
      rw [hk']
      exact hq.saved.frame hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (by nums) (by nums)).symm⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_using [])).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (d := 256) (n := 8 * L.e - 16) (by omega_using [this])).symm.sub_left
          (Region.sub_prefix (by rw [hk.1]))) (by nums))⟩

theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).body t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  rw [Cfg.body]
  exact WP.seq (WP.mono (stageX_ok hL hk hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hk h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hk h₆ q₆) fun _ ⟨h₇, q₇⟩ => ⟨h₇, i, q₇⟩)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_using [hi]) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_using [hi]]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_using [h7]]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_using [h7]]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_using []) (by omega_using [])
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_using []

/-! ## The whole function -/

theorem pop_rsp (B : Addr) (e : Nat) :
    B + BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * (28 + e)) = B + BitVec.ofNat 64 (248 + 8 * e) := by
  rw [Offset.add_add, show 24 + 8 * (28 + e) = 248 + 8 * e by omega_using []]

theorem sign_eq (P : RfcHash) :
    (cfgOf P).sign = .frame (.push (pushRs 48)) (cfgOf P).body (.pop .rcx (pushRs 48).length) := by
  rw [pushRs_length (by decide)]; rfl

/-- The contract the code for `P`'s hash function is proven against, after
the entry, with `P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcX86_64 P.R.E.combConsts P.I (248 + 8 * 48) (tabFacts P.H P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len 48 rfl P.R.E.combConsts P.H P.f s

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layOf P s) := ⟨P.curveLen, rfl, rfl, rfl⟩

/-- `sign` for `P`'s hash function meets `rfcP P` and keeps the callee-saved
registers and its return address. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => gprPreserved s s' ∧ (rfcP P ns).post s s' := by
  have hL := lay_ok rfl h
  have hc := push_ctx rfl h
  rw [sign_eq]
  refine WP.frame (rs := pushRs 48) (by simp [pushRs]) (by simp [pushRs]) (by decide)
    (by rw [pushRs_length (by decide)]; have := h.1; omega_using [this])
    (WP.mono (body_ok hL (coreOk_lay P s) hc) fun u ⟨hu, i, hx⟩ =>
      ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, fun m uu fm => ?_⟩)
  rw [pushRs_length (by decide)] at fm
  generalize hX : ({ popped .rcx (pushRs 48).length u with mem := m, unknowns := uu } : State) = X
  have hXg : X.gpr = (popped .rcx (pushRs 48).length u).gpr := by rw [← hX]
  have hXm : X.mem = m := by rw [← hX]
  have hsub : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * (28 + 48)), 8 * (28 + 48)⟩
      ⟨s.gpr .rsp - BitVec.ofNat 64 (248 + 8 * 48), 248 + 8 * 48⟩ :=
    Offset.sub_below _ (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · have hrsp : X.gpr .rsp = s.gpr .rsp := by
      rw [hXg, popped_rsp, hu.rsp, pushRs_length (by decide), pop_rsp]
      exact lay_ret _ _ _ rfl _ _ _ _
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [hXg, popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [hXm]
      refine (fm.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · simp only [List.mem_singleton]
        rintro r rfl
        exact Offset.base_disjoint_below _ (by decide)
      refine hu.frame.readW (r := (layOf P s).RET) ?_ ?_ (by decide)
      · show (⟨_ + BitVec.ofNat 64 (248 + 8 * 48), 8⟩ : Region).Contains (s.gpr .rsp) 8
        rw [lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · have h₁ : (lay P.I.hashLen P.I.ecdsa.curve.len 48 rfl P.R.E.combConsts P.H P.f s).e = 48 := rfl
          have h₂ : (layOf P s).e = 48 := rfl
          exact Offset.disjoint_base _ (by omega_using [h₁, h₂]) (by omega_using [h₂])
  · have hko : (⟨(layOf P s).out, 2 * P.I.ecdsa.curve.len⟩ : Region).Disjoint
        ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * (28 + 48)), 8 * (28 + 48)⟩ :=
      fun x h₁ h₂ => hL.ko x (hsub x h₂) h₁
    rw [P.curveLen] at hko
    show match (result P.I s.mem (layOf P s).d (layOf P s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    refine hx.res.keep (by rw [hXg]; exact popped_gpr _ _ _ (by decide) (by decide)) ?_
    rw [hXm]
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => lost_byte fm hko (List.mem_range.mp hi)

end VG.Proof.Ecdsa.Rfc6979.X86_64
