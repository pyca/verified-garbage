import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPMq

/-!
# RSA with the CRT on x86-64: constant time, `h = (m_p - m_q) qInv mod p`

`hSteps` (`hPart_ok`) is constant time (`h_ct`) for a predicate (`H0`) that
carries, before each piece, its claim's hypotheses and what correctness
gives after it; `h_chain` proves it from `hPart_ok`'s hypotheses, as
`hPart_ok` runs the pieces.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `hSteps`: the modulus' workspace, `p`'s, and `qInv`'s
pointer and length. -/
structure HPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat
  qp : Addr
  len : Nat

/-- `p`'s workspace. -/
abbrev HPub.pw (p : HPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- `p`'s workspace, as `redc`'s and `loadArr`'s claims take it. -/
abbrev HPub.x (p : HPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

/-- `qInv`, as `loadArr`'s claim takes it. -/
abbrev HPub.q (p : HPub) : BPub := ⟨p.x, p.qp, p.len⟩

/-- Before the way back to the modulus' workspace. -/
def H6 (p : HPub) (s : State) : Prop := s.gpr .rdi = off p.B p.o

/-- Before `h := T qInv R⁻¹`. -/
def H5 (M : Mont) (p : HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm Public.aY aT aChunk) s (H6 p)

/-- Before `qInv`'s mask. -/
def H4 (M : Mont) (p : HPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (maskArr aChunk)) s (H5 M p)

/-- Before `qInv`'s load. -/
def H3 (M : Mont) (p : HPub) (s : State) : Prop :=
  LPre aChunk sQinv sPlen p.q s ∧ WP isa (seqs (loadArr aChunk sQinv sPlen)) s (H4 M p)

/-- Before `T := m_p - m_q`. -/
def H2 (M : Mont) (p : HPub) (s : State) : Prop :=
  SmPre p.pw s ∧ WP isa (seqs (subModArr aT Public.aY aXc)) s (H3 M p)

/-- Before `m_q R_p` into `p`'s `X_c`. -/
def H1 (M : Mont) (p : HPub) (s : State) : Prop :=
  RPre Public.aX p.x s ∧ WP isa (seqs (redc M.mm Public.aX)) s (H2 M p)

/-- Before `hSteps`. -/
def H0 (M : Mont) (p : HPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sWsP))]) s (H1 M p)

/-- `hSteps` after its `redc` is constant time. -/
theorem h2_ct (M : Mont) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (H2 M)) (seqs (subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
      [M.mm Public.aY aT aChunk, .block [leave]])))) fun _ _ => True := by
  refine ct_steps (by simp [subModArr]) (by simp [loadArr]) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    subModArr_ct ?_
  refine ct_steps (by simp [loadArr]) (by simp [maskArr]) HPub.q (fun _ _ h => h.1) (fun _ _ h => h.2) hL ?_
  refine ct_steps (by simp [maskArr]) (by simp) HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (maskArr_ct (by decide) (by taint_decide)) ?_
  exact ct_step HPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .rdi = _ from h₁, h₂]) (by taint_decide))

/-- `hSteps` is constant time. -/
theorem h_ct (M : Mont) (hR : RedcCT M Public.aX) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two (H0 M)) (seqs (hSteps M.mm)) fun _ _ => True := by
  simp only [hSteps, List.append_assoc]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact ct_steps (by simp [redc]) (by simp [subModArr]) HPub.x (fun _ _ h => h.1) (fun _ _ h => h.2) hR
    (h2_ct M hL)

/-- `hTail_ok`'s hypotheses give `H2`. -/
theorem h2_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hc : SubCtx s B Z o w wx mx) (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hw28 : w < 2 ^ 28) (hwx2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hlt : wv s.mem (off B o) (slot wx aXc) wx < X) (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : H2 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  -- `T = (m_p - m_q) R_p mod p`.
  refine ⟨⟨⟨mx, hc.good, Nat.le_refl _⟩, hwx2, show wx < 2 ^ 31 by omega⟩,
    WP.mono (subModArr_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hwx2 (by omega)
    (o := aT) (a := Public.aY) (b := aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX.n]; exact hyl) (by rw [hX.n]; exact hlt))
    fun s₃ ⟨_, ha₃, k₃⟩ => ?_⟩
  obtain ⟨hc₃, hX₃, fx₃⟩ := hc.of_arrays hX ha₃ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> decide) k₃.2.2 (k₃.gpr (by decide)) (by omega)
  have hb₃ : ∀ d, d + 8 ≤ o → word s₃.mem B d = word s.mem B d := fun d hd => fx₃.x_below hd ho64
  have i03 : InScr B Z s.mem s₃.mem :=
    InScr.of_frm fx₃ fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hM₃ : word s₃.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ha₃.hslot (by decide)]; exact hmask
  -- `qInv`, masked.
  have a1 : word s₃.mem B (8 * sQinv) = qp := by rw [hb₃ _ (by unfold sQinv sFn; omega)]; exact hqp
  have a2 : word s₃.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₃ _ (by unfold sPlen sFn; omega)]; exact hql
  have a3 : Src s₃ B Z qp qib := hqs.congrK i03 k₃
  refine ⟨⟨mx, qib, hc₃, hwx2, hwx, show w < 2 ^ 30 by omega, by decide, by decide, by decide, a1, a2, rfl, a3,
      hq1, hq2, hqw⟩,
    WP.mono (primeLoad_ok hc₃ hwx2 hwx (by omega) (j := aChunk) (by decide) (sp := sQinv) (sl := sPlen)
      (by decide) (by decide) a1 a2 a3 hq1 hq2 hqw) fun s₄ ⟨hc₄, hq₄, ho₄, k₄⟩ => ?_⟩
  have hz₄ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega
  have hX₄ := hX₃.of_outside ho₄ (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have hM₄ : word s₄.mem (off B o) (8 * sMaskX) = mask c := by
    rw [ho₄.word (Or.inl (by have := hdr_lt_slot wx aChunk (show sMaskX < 32 by decide); omega))
      (by unfold sMaskX sFn; omega)]; exact hM₃
  refine ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, WP.mono (maskArr_ok hc₄.good (Nat.le_refl _) (by omega) (by omega)
    (j := aChunk) (by decide) hM₄) fun s₅ ⟨_, hq₅, ho₅, k₅⟩ => ?_⟩
  have ho₅' : Outside (off B o) (slot wx aChunk) (8 * (wx + 2)) s₄.mem s₅.mem :=
    ho₅.mono (Nat.le_refl _) (by omega)
  have hc₅ := hc₄.of_frm (rs := [(slot wx aChunk, 8 * (wx + 2))]) (Frm.of_outside ho₅' (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) (show aChunk < 8 by decide)
    have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
    simp only; omega) k₅.2.2 (k₅.gpr (by decide))
  have hX₅ := hX₄.of_outside ho₅' (by decide) (by decide) (by decide) (Nat.le_refl _) hz₄
  have hch : wv s₅.mem (off B o) (slot wx aChunk) wx < X := by
    rw [hq₅, hq₄]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [↓reduceIte]; exact hqi rfl
  -- `h = T qInv R_p⁻¹`.
  exact ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := aT) (b := aChunk) hc₅.good
    (Nat.le_refl _) hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hX₅.inv (by rw [hX₅.n]; exact hch)) fun _ h₆ => h₆.1.rdi⟩


/-- `hPart_ok`'s hypotheses give `H0`. -/
theorem h_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X o wx : Nat}
    {qp : Addr} {qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X)
    (hyl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : word s.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length)
    (hqs : Src s B Z qp qib) (hq1 : 1 ≤ qib.length) (hq2 : qib.length < 2 ^ 31) (hqw : (qib.length + 7) / 8 ≤ wx)
    (hqi : c = true → Spec.Rsa.os2ip qib < X) : H0 M ⟨B, Z, w, o, wx, qp, qib.length⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  have hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega
  refine ⟨hg.rdi, WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hslv]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_⟩
  have hc₁ : SubCtx s₁ B Z o w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo hhi
  have hX₁ : XVals s₁ B o wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  -- `m_q R_p` into `p`'s `X_c`.
  refine ⟨⟨mx, X, hc₁, hX₁, hwx2, hwx, show w < 2 ^ 30 by omega, hX1, by decide⟩,
    WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aX) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_⟩
  have fx₂ : Frm B [xRange o wx] s₁.mem s₂.mem := f₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hY₂ : wv s₂.mem (off B o) (slot wx Public.aY) wx = wv s.mem (off B o) (slot wx Public.aY) wx := by
    have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := wx) (show Public.aY < 8 by decide)
    have := hc₁.good.scr.nowrap
    rw [f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hM₂ : word s₂.mem (off B o) (8 * sMaskX) = mask c := by
    rw [f₂.word_eq (fun r hr => by
      simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have := hdr_lt_slot wx Public.aAcc (show 31 < 32 by decide)
      have := hdr_lt_slot wx Public.aTmp (show 31 < 32 by decide)
      have := hdr_lt_slot wx aXc (show 31 < 32 by decide)
      have := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
      have := hdr_lt_slot wx aT (show 31 < 32 by decide)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn] <;> omega)
      (by unfold sMaskX sFn; omega), hm₁]
    exact hmask
  have hb₂ : ∀ d, d + 8 ≤ o → word s₂.mem B d = word s.mem B d := fun d hd => by
    rw [fx₂.x_below hd ho64, hm₁]
  have i02 : InScr B Z s.mem s₂.mem := by
    have f := fx₂
    rw [hm₁] at f
    exact InScr.of_frm f fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  exact h2_chain M hc₂ hX₂ hX1 hw28 hwx2 hwx (by rw [hY₂]; exact hyl) hlt₂ hM₂
    (by rw [hb₂ _ (by unfold sQinv sFn; omega)]; exact hqp) (by rw [hb₂ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK i02 (k₁.trans k₂)) hq1 hq2 hqw hqi

end VG.Proof.Bignum.X86_64
