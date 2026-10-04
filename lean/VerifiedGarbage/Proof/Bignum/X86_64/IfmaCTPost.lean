import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPH
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTPre

/-!
# RSA with AVX512_IFMA on x86-64: constant time, after the exponentiations

`post` is, in `p`'s workspace, a `redc`, the loads of `q`'s result's
address (split at each load whose address the previous one gave), its
copy, a Montgomery multiplication and a copy, then `hSteps` after its
`redc` (`h2_ct`): each is constant time, so `post` is (`post_ct`), for
`post_ok`'s hypotheses (`PostPre`), from which `post_chain` proves what
each piece needs, as `post_ok` runs them.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

/-- The public data of `post`: `n`'s workspace, `p`'s and `q`'s (of `wx`
words each), and `qInv`'s pointer and length. -/
structure PostPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  wx : Nat
  oq : Nat
  qp : Addr
  len : Nat

abbrev PostPub.x (p : PostPub) : XPub := ⟨p.B, p.Z, p.op, p.w, p.wx⟩
abbrev PostPub.pw (p : PostPub) : Ws := ⟨off p.B p.op, slot p.wx 8, p.wx⟩
abbrev PostPub.h (p : PostPub) : HPub := ⟨p.B, p.Z, p.w, p.op, p.wx, p.qp, p.len⟩

/-- `post`'s loads of `q`'s result's address: `n`'s base, `q`'s, and from them. -/
def postBlk1 : List Instr := [.mov .rax (.mem (hdr sLink))]
def postBlk2 : List Instr := [.mov .rax (.mem (ws .rax sWsQ))]
def postBlk3 : List Instr :=
  [.mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))]

theorem post_eqCT (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.post mul = ([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++ (redc mul Public.aR2 ++
      (.block (postBlk1 ++ (postBlk2 ++ postBlk3)) :: copyWords :: mul aChunk aChunk aXc ::
        (copyArr aXc aChunk ++ (subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
          [mul Public.aY aT aChunk, .block [leave]])))))) := by
  simp only [CrtIfma.post, enterP, postBlk1, postBlk2, postBlk3, List.append_assoc, List.cons_append,
    List.nil_append]

/-- Before `aXc := aChunk`. -/
def Q7 (M : Mont) (p : PostPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr aXc aChunk)) s (H2 M p.h)

/-- Before `aChunk := aChunk aXc`. -/
def Q6 (M : Mont) (p : PostPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm aChunk aChunk aXc) s (Q7 M p)

/-- Before the copy of `m_q`. -/
def Q5 (M : Mont) (p : PostPub) (s : State) : Prop :=
  s.gpr .rsi = off (off p.B p.oq) (slot p.wx Public.aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rbx = off (off p.B p.op) (slot p.wx aChunk) ∧ WP isa copyWords s (Q6 M p)

/-- Before the loads from `q`'s workspace. -/
def Q4 (M : Mont) (p : PostPub) (s : State) : Prop :=
  s.gpr .rax = off p.B p.oq ∧ s.gpr .rdi = off p.B p.op ∧ WP isa (.block postBlk3) s (Q5 M p)

/-- Before the load of `q`'s base. -/
def Q3 (M : Mont) (p : PostPub) (s : State) : Prop :=
  s.gpr .rax = p.B ∧ s.gpr .rdi = off p.B p.op ∧ WP isa (.block postBlk2) s (Q4 M p)

/-- Before the load of `n`'s base. -/
def Q2 (M : Mont) (p : PostPub) (s : State) : Prop :=
  s.gpr .rdi = off p.B p.op ∧ WP isa (.block postBlk1) s (Q3 M p)

/-- Before the `redc`. -/
def Q1 (M : Mont) (p : PostPub) (s : State) : Prop :=
  RPre Public.aR2 p.x s ∧ WP isa (seqs (redc M.mm Public.aR2)) s (Q2 M p)

/-- Before `post`. -/
def Q0 (M : Mont) (p : PostPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sWsP))]) s (Q1 M p)

/-- `post_ok`'s hypotheses, with what `post` reads of them public. -/
def PostPre (p : PostPub) (s : State) : Prop :=
  ∃ (minv mx mq : BitVec 64) (X : Nat) (qib : List Byte) (c : Bool),
    Good s p.B p.Z p.w minv ∧ p.w < 2 ^ 28 ∧ p.w = 2 * p.wx ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsAt s.mem p.B p.oq p.wx mq ∧
    p.oq + slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wx 8 + tabBytes p.wx ≤ p.oq ∧ 2 ≤ p.wx ∧
    word s.mem p.B (8 * sWsP) = off p.B p.op ∧ WsAt s.mem p.B p.op p.wx mx ∧ XVals s p.B p.op p.wx mx X ∧
    1 < X ∧ wv s.mem (off p.B p.op) (slot p.wx Public.aY) p.wx < X ∧
    word s.mem (off p.B p.op) (8 * sMaskX) = mask c ∧ word s.mem p.B (8 * sQinv) = p.qp ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 qib.length ∧ Src s p.B p.Z p.qp qib ∧ 1 ≤ qib.length ∧
    qib.length < 2 ^ 31 ∧ (qib.length + 7) / 8 ≤ p.wx ∧ (c = true → Spec.Rsa.os2ip qib < X) ∧ qib.length = p.len

/-- `post_ok`'s hypotheses give `Q0`, as `post_ok` runs the pieces. -/
theorem post_chain (M : Mont) {p : PostPub} {s : State} (h : PostPre p s) : Q0 M p s := by
  obtain ⟨B, Z, w, op, wx, oq, qp, len⟩ := p
  dsimp only [PostPre] at h
  obtain ⟨minv, mx, mq, X, qib, c, hg, hw28, hw2, hq, hwsq, hhiq, hlo, hhi, hwx2, hsp, hws, hX, hX1, hyl, hmask,
    hqp, hql, hqs, hq1, hq2, hqw, hqi, rfl⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : op < 2 ^ 64 := by omega
  have hoL : op + slot wx 8 ≤ 2 ^ 64 := by omega
  have hwx : wx ≤ w := by omega
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have lC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have lX := slot_le (w := wx) (show aXc < 8 by decide)
  have hX0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, slot, hdrBytes] <;>
      omega
  have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  -- Into `p`'s workspace.
  refine ⟨hg.rdi, WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B op ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hsp]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_⟩
  have hc₁ : SubCtx s₁ B Z op w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (by omega)
  have hX₁ : XVals s₁ B op wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  refine ⟨⟨mx, X, hc₁, hX₁, hwx2, hwx, show w < 2 ^ 30 by omega, hX1, by decide⟩, ?_⟩
  -- `redc` of `R_n²`.
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aR2) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, _, r₂, k₂⟩ => ?_
  have fx₂ : Frm B [xRange op wx] s.mem s₂.mem := by
    rw [← hm₁]; exact r₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hb₂ : ∀ d, d + 8 ≤ op → word s₂.mem B d = word s.mem B d := fun d hd => fx₂.x_below hd ho64
  have hab₂ : ∀ d, op + slot wx 8 + tabBytes wx ≤ d → d + 8 ≤ 2 ^ 64 → word s₂.mem B d = word s.mem B d :=
    fun d hd hd' => fx₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) hd'
  have hs₂ := hc₂.scr
  have hsP := hc₂.good.scr
  have hdi₂ := hc₂.rdi
  refine ⟨hdi₂, ?_⟩
  -- `rax := B`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = B ∧ t.mem = s₂.mem)
    (by xrun [postBlk1, State.ea, hdr, hdi₂, hdrOff, hsP.ld (d := 8 * sLink) (by unfold sLink sFn; omega),
      hc₂.link]) rfl) fun s₃ ⟨⟨hax₃, hm₃⟩, k₃⟩ => ⟨hax₃, (k₃.gpr (by decide)).trans hdi₂, ?_⟩
  have hs₃ := hs₂.congr k₃.2.2
  -- `rax := q`'s base.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = off B oq ∧ t.mem = s₃.mem)
    (by xrun [postBlk2, State.ea, ws, hax₃, hdrOff, hs₃.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hm₃,
      hb₂ (8 * sWsQ) (by unfold sWsQ sFn; omega), hq]) rfl)
    fun s₄ ⟨⟨hax₄, hm₄⟩, k₄⟩ => ⟨hax₄, (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂), ?_⟩
  have hs₄ := hs₃.congr k₄.2.2
  have hsP₄ := (hsP.congr k₃.2.2).congr k₄.2.2
  have hldq := (hs₄.sub (o := oq) (n := slot wx 8) (by omega) (by omega)).ld (d := 8 * sArr Public.aY)
    (by unfold sArr Public.aY; omega)
  have hqa : word s₄.mem (off B oq) (8 * sArr Public.aY) = off (off B oq) (slot wx Public.aY) := by
    rw [hm₄, hm₃, word_off, hab₂ (oq + 8 * sArr Public.aY) (by omega) (by unfold sArr Public.aY; omega), ← word_off]
    exact hwsq.hdr.harr Public.aY (by decide)
  have hdi₄ : s₄.gpr .rdi = off B op := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  have hpw : ∀ i < 32, word s₄.mem (off B op) (8 * i) = word s₂.mem (off B op) (8 * i) := fun i _ => by
    rw [hm₄, hm₃]
  -- `rsi`, `r12`, `rbx`.
  refine WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = off (off B oq) (slot wx Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rbx = off (off B op) (slot wx aChunk) ∧ t.mem = s₄.mem)
    (by xrun [postBlk3, State.ea, hdr, ws, hax₄, hdi₄, hdrOff, hldq, hqa,
      hsP₄.ld (d := 8 * sW) (by unfold sW; omega), hpw sW (by decide), hc₂.hdr.hw,
      hsP₄.ld (d := 8 * sArr aChunk) (by unfold sArr aChunk; omega), hpw (sArr aChunk) (by decide),
      hc₂.hdr.harr aChunk (by decide)]) rfl)
    fun s₅ ⟨⟨hsi₅, h12₅, hbx₅, hm₅⟩, k₅⟩ => ⟨hsi₅, h12₅, hbx₅, ?_⟩
  have k25 := (k₃.trans k₄).trans k₅
  have hs₅ := hs₂.congr k25.2.2
  have hsP₅ := hsP.congr k25.2.2
  have hsi₅' : s₅.gpr .rsi = off B (oq + slot wx Public.aY) := by rw [hsi₅, off_off]
  -- `aChunk := m_q`.
  refine WP.mono (copyWords_ok (S := B) (eS := oq + slot wx Public.aY) (D := off B op) (eD := slot wx aChunk)
    (w := wx) hsi₅' hbx₅ h12₅ (by omega) (by omega) (by omega) (fun j hj => hs₅.ld (by omega))
    (fun j hj => hsP₅.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [show off B (oq + slot wx Public.aY + 8 * j) = off (off B op) (oq + slot wx Public.aY + 8 * j - op) by
        rw [off_off]; congr 1; omega, ofs_off (off B op) (by omega)]; omega))) fun s₆ ⟨_, _, ho₆, k₆⟩ => ?_
  have hm25 : s₅.mem = s₂.mem := by rw [hm₅, hm₄, hm₃]
  rw [hm25] at ho₆
  have hz₂ : (off B op).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₂.good.scr.nowrap; omega
  have hX₆ : XVals s₆ B op wx mx X := hX₂.of_outside ho₆ (by decide) (by decide) (by decide) (by omega) hz₂
  have hc₆ : SubCtx s₆ B Z op w wx mx := hc₂.of_frm (rs := [(slot wx aChunk, 8 * wx)]) (Frm.of_outside ho₆ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) (k25.trans k₆).2.2 ((k25.trans k₆).gpr (by decide))
  have hxc₆ : wv s₆.mem (off B op) (slot wx aXc) wx = wv s₂.mem (off B op) (slot wx aXc) wx := by
    have := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    exact ho₆.wv (by omega) (by omega)
  refine ⟨⟨mx, hc₆.good, Nat.le_refl _⟩, ?_⟩
  -- `aChunk := aChunk aXc`.
  refine WP.mono (M.mm_ok (o := aChunk) (a := aChunk) (b := aXc) hc₆.good (Nat.le_refl _) hwx2
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₆.inv
    (by rw [hX₆.n, hxc₆]; exact hlt₂)) fun s₇ ⟨_, hlt₇, _, ha₇, k₇⟩ => ?_
  rw [hX₆.n] at hlt₇
  obtain ⟨hc₇, hX₇, fx₇⟩ := hc₆.of_arrays hX₆ ha₇ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₇.2.2 (k₇.gpr (by decide)) (by omega)
  refine ⟨⟨mx, hc₇.good, Nat.le_refl _⟩, ?_⟩
  -- `aXc := aChunk`.
  refine WP.mono (copyArr_ok hc₇.good (Nat.le_refl _) (by omega) (by omega) (o := aXc) (a := aChunk)
    (by decide) (by decide) (by decide)) fun s₈ ⟨hv₈, ho₈, k₈⟩ => ?_
  have hc₈ := hc₇.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₈ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₈.2.2 (k₈.gpr (by decide))
  have hX₈ : XVals s₈ B op wx mx X := hX₇.of_outside ho₈ (by decide) (by decide) (by decide) (by omega) hz₂
  have fx₈ : Frm B [xRange op wx] s₇.mem s₈.mem :=
    (ho₈.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have fx₆ : Frm B [xRange op wx] s₂.mem s₆.mem :=
    (ho₆.mono (o' := slot wx aChunk) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have f08 : Frm B [xRange op wx] s.mem s₈.mem := ((fx₂.trans fx₆).trans fx₇).trans fx₈
  have hb₈ : ∀ d, d + 8 ≤ op → word s₈.mem B d = word s.mem B d := fun d hd => f08.x_below hd ho64
  have i08 : InScr B Z s.mem s₈.mem :=
    InScr.of_frm f08 fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hY₈ : wv s₈.mem (off B op) (slot wx Public.aY) wx = wv s.mem (off B op) (slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    have := slot_sep (w := wx) (show Public.aY ≠ aChunk by decide)
    rw [ho₈.wv (by omega) (by omega), ha₇.wv_of_not_mem (by decide) (by decide) hz₂, ho₆.wv (by omega) (by omega),
      r₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hM₈ : word s₈.mem (off B op) (8 * sMaskX) = mask c := by
    have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega
    rw [ho₈.word (.inl (by omega)) (by omega), ha₇.hslot (by decide), ho₆.word (.inl (by omega)) (by omega),
      r₂.word_eq hrm (by omega), hm₁]; exact hmask
  exact h2_chain M hc₈ hX₈ hX1 hw28 hwx2 hwx (by rw [hY₈]; exact hyl) (by rw [hv₈]; exact hlt₇) hM₈
    (by rw [hb₈ _ (by unfold sQinv sFn; omega)]; exact hqp) (by rw [hb₈ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK i08 (((((k₁.trans k₂).trans k25).trans k₆).trans k₇).trans k₈)) hq1 hq2 hqw hqi

/-- `post` is constant time. -/
theorem post_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two PostPre) (seqs (CrtIfma.post M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => post_chain M h) ?_
  rw [post_eqCT]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [redc]) (by simp) PostPub.x (fun _ _ h => h.1) (fun _ _ h => h.2) hR2 ?_
  have b1 : RelCT isa (Two (Q2 M)) (.block postBlk1) (Two (Q3 M)) :=
    two_piece [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) fun _ _ h => h.2
  have b2 : RelCT isa (Two (Q3 M)) (.block postBlk2) (Two (Q4 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  have b3 : RelCT isa (Two (Q4 M)) (.block postBlk3) (Two (Q5 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq b1 (RelCT.block_append (RelCT.seq b2 b3)))) ?_
  refine ct_taint [.rsi, .r12, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  refine RelCT.seq (two_post (Ψ := Q7 M) (two_map PostPub.pw (fun _ _ h => h.1) (M.ct (by unfold MmUse; decide)))
    fun _ _ h => h.2) ?_
  exact ct_steps (by simp [copyArr]) (by simp [subModArr]) PostPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) (two_map PostPub.h (fun _ _ h => h) (h2_ct M hL))

end VG.Proof.Bignum.X86_64
