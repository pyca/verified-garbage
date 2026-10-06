import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTPH

/-!
# RSA with the CRT on AArch64: constant time, `p`'s phase

`pPhase` is constant time (`pPhase_ct`) given its pieces' claims: before
each piece, a predicate (`PO0` … `PO4`, then `hSteps`' `H0`) carries the
piece's hypotheses and what correctness gives after it; `o0_of` proves the
first from `PPre`, as `pPhase_ok` runs the pieces.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The modulus' workspace. -/
abbrev PPhasePub.nw (p : PPhasePub) : Ws := ⟨p.ph.B, p.ph.Z, p.ph.w⟩

/-- The public data of the phase's first part. -/
abbrev PPhasePub.u (p : PPhasePub) : UPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.minv, p.ph.N, p.ph.o, p.ph.wx⟩

/-- The public data of `m_q G mod n`. -/
abbrev PPhasePub.mq (p : PPhasePub) : MqPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.oq, p.wq⟩

/-- The public data of the exponentiation. -/
abbrev PPhasePub.pw (p : PPhasePub) : BPub := ⟨⟨p.ph.B, p.ph.Z, p.ph.o, p.ph.w, p.ph.wx⟩, p.ph.ep, p.ph.len⟩

/-- The public data of `h`. -/
abbrev PPhasePub.h (p : PPhasePub) : HPub := ⟨p.ph.B, p.ph.Z, p.ph.w, p.ph.o, p.ph.wx, p.qp, p.ph.len⟩

/-- Before the way back to the modulus' workspace. -/
def PO4 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  s.gpr .x0 = off p.ph.B p.ph.o ∧ WP isa (.block [leave]) s (H0 M p.h)

/-- Before the exponentiation. -/
def PO3 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  PwPre sWsP sDp sPlen p.pw s ∧ WP isa (seqs (powSteps M.mm sWsP sDp sPlen)) s (PO4 M p)

/-- Before `c G mod N`. -/
def PO2 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (PO3 M p)

/-- Before `m_q G mod N`. -/
def PO1 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (PO2 M p)

/-- Before `pPhase`. -/
def PO0 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s (PO1 M p)

/-- From before the exponentiation: `PO3`, as `pPhase_ok` runs the rest. -/
theorem o3_of (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hcg : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hpl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hpy : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    PO3 M ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  -- `c^dP R_p mod p`.
  refine ⟨⟨minv, mx, N, X, C, eb, hg, hw28, hlo, hhi, hwx2, hwx, by decide, hslv, hws, hX, hX1, hXodd, hcg, hpl,
      hpy, by decide, by decide, hep, hel, rfl, hL1, hL2, he⟩,
    WP.mono (powPhase_ok M hg hw28 hlo hhi hwx2 hwx (sl := sWsP) (by decide) hslv hws hX hX1 hXodd hcg hpl hpy
      (sd := sDp) (slen := sPlen) (by decide) (by decide) hep hel hL1 hL2 he)
      fun s₄ ⟨hc₄, hX₄, hlt₄, _, hM₄, fx₄, k₄⟩ => ?_⟩
  -- Back to the modulus'.
  refine ⟨hc₄.x0, WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₄.mem)
    (by brun [leave, hc₄.x0, hdr_enc (show sLink < 32 by decide), hc₄.ld' (show sLink < 32 by decide), hc₄.link'])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_⟩
  have fx₅ : Frm B [xRange o wx] s.mem s₅.mem := by rw [hm₅]; exact fx₄
  have k05 := k₄.trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s.mem B d := fun d hd => fx₅.x_below hd ho64
  have hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.wr, hdi₅, ⟨(hb₅ _ (by unfold sW; omega)).trans hg.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega)).trans hg.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hg.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm fx₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  -- `h`.
  have a1 : word s₅.mem B (8 * sWsP) = off B o := by rw [hb₅ _ (by unfold sWsP sFn; omega)]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by rw [hm₅, hM₄]; exact hmask
  have a6 : word s₅.mem B (8 * sQinv) = qp := by rw [hb₅ _ (by unfold sQinv sFn; omega)]; exact hqp
  have a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₅ _ (by unfold sPlen sFn; omega), hql]; exact hel
  have := h_chain M hg₅ hw28 hlo hhi hwx2 hwx a1 a2 hX₅ hX1 a3 a5 a6 a7 (hqs.congrK i05 k05) (by omega)
    (by omega) hqw hqi
  rw [hql] at this
  exact this

/-- `pPhase_ok`'s hypotheses give `PO0`. -/
theorem o0_of (M : Mont) {p : PPhasePub} {s : State} (h : PPre p s) : PO0 M p s := by
  obtain ⟨⟨B, Z, w, minv, N, o, wx, ep, len⟩, oq, wq, qp⟩ := p
  dsimp only [PPre] at h
  obtain ⟨mx, mq, X, C, eb, qib, c, hg, hw, hw28, hlo, hhi, hqhi, hwx2, hwx, hwq, hwq', hslv, hws, hslq, hwsq, hN,
    hodd, hN1, hXm, hX, hX1, hXodd, hmask, hc, hep, hel, rfl, hL1, hL2, he, hqp, hql, hqs, hqw, hqi⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hhi' : o + slot wx 8 + tabBytes wx ≤ Z := by omega
  have hsub : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r ∈ pRanges w ++ [xRange o wx]) → ∀ {m m' : Mem},
      Frm B rs m m' → Frm B (pRanges w ++ [xRange o wx]) m m' := fun h _ _ f => f.mono h
  have sgx : ∀ r ∈ gRanges w ++ [xRange o wx], r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    (List.mem_append.mp hr).elim (fun h => List.mem_append_left _ (List.mem_append_left _ h))
      (fun h => List.mem_append_right _ h)
  have sp : ∀ r ∈ pRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr => List.mem_append_left _ hr
  have sg : ∀ r ∈ gRanges w, r ∈ pRanges w ++ [xRange o wx] := fun r hr =>
    List.mem_append_left _ (List.mem_append_left _ hr)
  have hqh : ∀ {m m' : Mem}, Frm B (pRanges w ++ [xRange o wx]) m m' → ∀ i < 32,
      word m' (off B oq) (8 * i) = word m (off B oq) (8 * i) := fun f i hi => by
    rw [word_off, word_off]; exact f.px_above hlo (by omega) (by omega)
  -- `R_p mod p`.
  refine ⟨⟨mx, X, hg, hw, hw28, hlo, hhi', hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
      hX, hX1, hXodd⟩,
    WP.mono (unitPhase_ok M hg hw hw28 hlo hhi' hwx2 hwx (sl := sWsP) (by decide) (by decide) (by decide) hslv
      hws hN hodd hN1 hX hX1 hXodd) fun s₁ ⟨hg₁, hws₁, hX₁, hlt₁, hG₁, hpl₁, hpy₁, hM₁, f₁, k₁⟩ => ?_⟩
  have f₁' := hsub sgx f₁
  have hN₁ := hN.of_frm f₁ hlo hz (by omega)
  have hslq₁ : word s₁.mem B (8 * sWsQ) = off B oq := by
    rw [f₁'.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslq
  have hwsq₁ : WsAt s₁.mem B oq wq mq := hwsq.of_words fun i hi => hqh f₁' i (by omega)
  -- `m_q G mod N`.
  refine ⟨mq_chain M hg₁ hw hw28 hN₁ hslq₁ hwsq₁ (show slot w 8 ≤ oq by omega) hqhi hwq hwq',
    WP.mono (mqPart_ok M hg₁ hw hw28 hN₁ hodd hlt₁ hG₁ hslq₁ hwsq₁ (show slot w 8 ≤ oq by omega) hqhi hwq hwq')
    fun s₂ ⟨hg₂, _, hmq₂, hY₂, f₂, k₂⟩ => ?_⟩
  have f₂' := hsub sp f₂
  have f₀₂ := f₁'.trans f₂'
  have hN₂ : NVals s₂ B w minv N := by
    exact ⟨by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.n,
      by rw [f₂'.word_eq (fun r hr => by
        have := pxR_bound hlo r hr
        have := slot_le (w := w) (show Public.aN < 8 by decide)
        simp only [pRanges, gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        have s1 := slot_sep (w := w) (show Public.aN ≠ Public.aAcc by decide)
        have s2 := slot_sep (w := w) (show Public.aN ≠ Public.aTmp by decide)
        have s3 := slot_sep (w := w) (show Public.aN ≠ Public.aY by decide)
        have s4 := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
        have := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega)
        (by have := slot_le (w := w) (show Public.aN < 8 by decide); omega)]; exact hN₁.inv,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.r2lt,
      by rw [f₂'.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hN₁.one⟩
  -- `c G mod N`.
  refine ⟨⟨minv, hg₂, show slot w 8 ≤ Z by omega⟩,
    WP.mono (mmY_ok M hg₂ (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
      (by decide) hN₂ (by rw [hY₂]; exact hlt₁)) fun s₃ ⟨hg₃, _, hm₃, f₃, k₃⟩ => ?_⟩
  have f₃' := hsub sg f₃
  have f₀₃ := f₀₂.trans f₃'
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    f₀₂.px_wv hlo hz (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcg : wv s₃.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, Nat.mul_mod, hXm₂, hXm, hY₂, hG₁, ← Nat.mul_mod]
    congr 1; ac_rfl
  have hpo : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d,
      o ≤ d → d + 8 ≤ 2 ^ 64 → word m' B d = word m B d := fun f hrs d hd hd' =>
    f.word_eq (fun r hr => Or.inr (by have := pRanges_le w r (hrs r hr); omega)) hd'
  have hpw : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ i < 32,
      word m' (off B o) (8 * i) = word m (off B o) (8 * i) := fun f hrs i hi => by
    rw [word_off, word_off]; exact hpo f hrs _ (by omega) (by omega)
  have sg' : ∀ r ∈ gRanges w, r ∈ pRanges w := fun r hr => List.mem_append_left _ hr
  have hpv : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ pRanges w) → ∀ d k,
      d + 8 * k ≤ slot wx 8 → wv m' (off B o) d k = wv m (off B o) d k := fun f hrs d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpo f hrs _ (by omega) (by omega)
  have hY8 := slot_le (w := wx) (show Public.aY < 8 by decide)
  have hpY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₁.mem (off B o) (slot wx Public.aY) wx := by
    rw [hpv f₃ sg' _ _ (by omega), hpv f₂ (fun r h => h) _ _ (by omega)]
  have hws₃ : WsAt s₃.mem B o wx mx := hws₁.of_words fun i hi => by
    rw [hpw f₃ sg' i (by omega), hpw f₂ (fun r h => h) i (by omega)]
  have hX₃ : XVals s₃ B o wx mx X :=
    (hX₁.of_below f₂ (fun r hr => (pRanges_le w r hr).trans hlo) (by omega)).of_below f₃
      (fun r hr => (pRanges_le w r (sg' r hr)).trans hlo) (by omega)
  have i03 : InScr B Z s.mem s₃.mem := InScr.of_frm f₀₃ fun r hr => by have := pxR_bound hlo r hr; omega
  have k03 := (k₁.trans k₂).trans k₃
  have hM₃ : word s₃.mem (off B o) (8 * sMaskX) = mask c := by
    rw [hpw f₃ sg' _ (by decide), hpw f₂ (fun r h => h) _ (by decide), hM₁]; exact hmask
  exact o3_of M hg₃ hw28 hlo hhi' hwx2 hwx (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hslv)
    hws₃ hX₃ hX1 hXodd hcg (by rw [hpY₃]; exact hpl₁) (fun hd => by rw [hpY₃]; exact hpy₁ hd)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hep)
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hel) hL1 hL2 (he.congrK i03 k03) hM₃
    (by rw [f₀₃.px_hdr hlo (by decide) (by decide) (by decide)]; exact hqp) hql (hqs.congrK i03 k03) hqw hqi

/-- `p`'s phase is constant time, given its pieces' claims. -/
theorem pPhase_ct (M : Mont) (hU : UnitCT M sWsP) (hP : PowCT M sWsP sDp sPlen) (hRX : RedcCT M Public.aX)
    (hL : LoadCT aChunk sQinv sPlen) : PPhaseCT M := by
  unfold PPhaseCT
  refine two_map id (fun _ _ h => o0_of M h) ?_
  rw [pPhase_eq]
  refine ct_steps (by simp [unitSteps]) (by simp [mqSteps]) PPhasePub.u (fun _ _ h => h.1) (fun _ _ h => h.2)
    hU ?_
  refine ct_steps (by simp [mqSteps]) (by simp) PPhasePub.mq (fun _ _ h => h.1) (fun _ _ h => h.2) (mq_ct M) ?_
  refine ct_steps (by simp) (by simp [powSteps]) PPhasePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [powSteps]) (by simp) PPhasePub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) hP ?_
  refine RelCT.seqs_append (by simp) (by simp [hSteps]) (ct_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact two_map PPhasePub.h (fun _ _ h => h) (h_ct M hRX hL)

end VG.Proof.Bignum.AArch64
