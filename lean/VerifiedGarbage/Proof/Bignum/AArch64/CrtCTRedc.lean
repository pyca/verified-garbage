import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow

/-!
# RSA with the CRT on AArch64: `redc` is constant time

`redc j` reduces `n`'s array `j` in chunks of `w_X` words: the number of
chunks `K = ⌈w / w_X⌉`, the words left (`sRem`) and the chunk's length (a
`csel` of them and `w_X`, pinned by correctness before the copy) depend only
on `w`, `w_X` and the iteration, which both runs share (`RInv`), and its
multiplications are constant time for any modulus (`M.ct`). Its loads from
the header are pinned by correctness.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem SubCtx.of_keep {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List Reg}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem) (k : Keep rs s t) (hr : Reg.x0 ∉ rs) :
    SubCtx t B Z o w wx minv :=
  h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.wr (k.gpr .x0 hr)

/-! ## `addMod` -/

/-- After `addMod`'s loads: its bases and counters. -/
def AmHd (o a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .x9 = off L.B (slot L.w a) ∧ t.gpr .x17 = off L.B (slot L.w b) ∧
    t.gpr .x10 = off L.B (slot L.w Public.aN) ∧ t.gpr .x8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .x6 = off L.B (slot L.w Public.aTmp) ∧ t.gpr .x5 = off L.B (slot L.w o) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x16 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .x14 = BitVec.ofNat 64 L.w

theorem pins_amHd (o a b : Nat) : Pins (AmHd o a b) [.x9, .x17, .x10, .x8, .x6, .x5, .x12, .x16, .x14] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁, j₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂, j₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]
  · rw [i₁, i₂]
  · rw [j₁, j₂]

/-- `addMod o a b` is constant time for any modulus, given that the taint
analysis checks its loads from `x0` (`by taint_decide` for given arrays). -/
theorem addMod_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x9 (sArr a), ldh .x17 (sArr b), ldh .x10 (sArr Public.aN),
      ldh .x8 (sArr Public.aAcc), ldh .x6 (sArr Public.aTmp), ldh .x5 (sArr o), ldh .x12 sW, movi .x7 0,
      mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7]) hc).isSome = true) :
    RelCT isa (Two GoodW) (addMod o a b) fun _ _ => True := by
  unfold addMod
  refine RelCT.seq (two_piece (Ψ := AmHd o a b) [.x0] pins_goodW hT fun L s h => ?_)
    (two_taint _ (pins_amHd o a b) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.x3, .x5, .x6, .x7, .x8, .x9, .x10, .x12, .x14, .x16, .x17] (Q := AmHd o a b L)
    (by brun [AmHd, hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt hb), hdr_enc (sArr_lt ho),
      hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hdr_enc (sArr_lt (show Public.aAcc < 8 by decide)),
      hdr_enc (sArr_lt (show Public.aTmp < 8 by decide)), hdr_enc (show sW < 32 by decide),
      hl (sArr a) (sArr_lt ha), hl (sArr b) (sArr_lt hb), hl (sArr o) (sArr_lt ho),
      hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide), hl (sArr Public.aTmp) (by decide),
      hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr b hb, hg.hdr.harr o ho,
      hg.hdr.harr Public.aN (by decide), hg.hdr.harr Public.aAcc (by decide),
      hg.hdr.harr Public.aTmp (by decide), hg.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-! ## The loop's body -/

/-- The sizes. -/
def XF (p : XPub) : Prop := 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30

/-- After `k` chunks. -/
def RLoop (j : Nat) (p : XPub) (k : Nat) (t : State) : Prop :=
  ∃ (s : State) (minv : BitVec 64) (X : Nat), RInv s p.B p.Z p.o p.w p.wx j minv X k t ∧ XF p ∧ 1 < X ∧ j < 8

/-- Before chunk `k`. -/
def RBody (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  q.2 < (q.1.w + q.1.wx - 1) / q.1.wx ∧ RLoop j q.1 q.2 t

/-- After the chunk's array is cleared. -/
def RB1 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    word t.mem (off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    word t.mem (off q.1.B q.1.o) (8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧ XF q.1

/-- Before the chunk's copy. -/
def RB4 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  t.gpr .x16 = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .x17 = off q.1.B (q.1.o + slot q.1.wx aChunk) ∧
    t.gpr .x12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)

/-- After the chunk's copy (`redcLoad_ok`). -/
def RB5 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    XVals t q.1.B q.1.o q.1.wx minv X ∧ 1 < X ∧
    t.gpr .x12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
    t.gpr .x16 = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx) + 8 * min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
    word t.mem (off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧ XF q.1

/-- The prime, before a multiplication. -/
def RA0 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧ XF p

/-- After `A' := A R⁻¹`. -/
def RA1 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧
    wv t.mem (off p.B p.o) (slot p.wx aXc) p.wx < X ∧ XF p

/-- After `T := c R⁻¹`. -/
def RA2 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧
    wv t.mem (off p.B p.o) (slot p.wx aXc) p.wx < X ∧ wv t.mem (off p.B p.o) (slot p.wx aT) p.wx < X ∧ XF p

theorem rb1_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RBody j q t) :
    WP isa (zeroArr aChunk) t (RB1 j q) := by
  obtain ⟨hk, s, minv, X, hI, hf, -, -⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hc := hI.ctx
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hC := slot_le (w := q.1.wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot q.1.wx aChunk (show 31 < 32 by decide)
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (show aChunk < 8 by decide))
    fun t₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.wr
      (k₁.gpr .x0 (by decide)), ?_, ?_, hf⟩
  · rw [ho₁.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega), hI.rem, hlw]
  · rw [ho₁.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega), hI.src, hlw]

/-- The chunk's length and pointers. -/
def rbBlock : List Instr :=
  [ldh .x3 sRem, ldh .x12 sW, .subs .x .x4 .x3 .x12, .csel .x .x12 .x12 .x3, ldh .x16 sSrc,
    ldh .x17 (sArr aChunk)]

theorem rb4_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB1 j q t) : WP isa (.block rbBlock) t (RB4 j q) := by
  obtain ⟨minv, hc, hrem, hsrc, hw2, hwx, hw30⟩ := h
  have hrem' : word t.mem q.1.B (q.1.o + 8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) := by
    rw [← word_off]; exact hrem
  have hsrc' : word t.mem q.1.B (q.1.o + 8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) := by
    rw [← word_off]; exact hsrc
  exact WP.mono (WP.keep [.x3, .x4, .x12, .x16, .x17] (Q := RB4 j q)
    (by brun [rbBlock, RB4, hc.x0, hdr_enc (show sRem < 32 by decide), hdr_enc (show sW < 32 by decide),
      hdr_enc (show sSrc < 32 by decide), hdr_enc (sArr_lt (show aChunk < 8 by decide)),
      hc.ld' (show sRem < 32 by decide), hc.ld' (show sW < 32 by decide), hc.ld' (show sSrc < 32 by decide),
      hc.ld' (sArr_lt (show aChunk < 8 by decide)), hrem', hc.hw', hsrc', hc.harr' (show aChunk < 8 by decide),
      csel_min (show q.1.w - q.2 * q.1.wx < 2 ^ 64 by omega) (show q.1.wx < 2 ^ 64 by omega)])
    (by decide) (by decide) (by decide +kernel)) fun _ h => h.1

theorem pins_subCtx {α : Type} {Φ : α → State → Prop} (f : α → XPub)
    (h : ∀ a s, Φ a s → ∃ minv, SubCtx s (f a).B (f a).Z (f a).o (f a).w (f a).wx minv) : Pins Φ [.x0] :=
  pins_x0B (fun a => off (f a).B (f a).o) fun a s hs => let ⟨_, hc⟩ := h a s hs; hc.x0

/-- A chunk into its array. -/
theorem redcLoad_ct (j : Nat) : RelCT isa (Two (RBody j)) (seqs redcLoad) fun _ _ => True := by
  simp only [redcLoad, seqs]
  refine RelCT.seq (two_post (Ψ := RB1 j) (two_map (fun q => q.1.ws)
    (fun q t ⟨_, _, minv, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩) (zeroArr_ct (by decide) (by taint_decide)))
    fun _ _ h => rb1_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := RB4 j) [.x0] (pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩)
    (by taint_decide) fun _ _ h => rb4_ok h) ?_
  refine two_taint [.x16, .x17, .x12] (pins_of (fun q r => if r = .x16 then
      off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx))
    else if r = .x17 then off q.1.B (q.1.o + slot q.1.wx aChunk)
    else BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)) fun q s h r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- `redcAcc`'s first block. -/
def raBlock : List Instr := [sth .x16 sSrc, ldh .x3 sRem, .sub .x .x3 .x3 .x12, sth .x3 sRem]

theorem ra0_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB5 j q t) : WP isa (.block raBlock) t (RA0 q.1) := by
  obtain ⟨minv, X, hc, hv, hX1, h12, h16, hrem, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hcr : min (q.1.w - q.2 * q.1.wx) q.1.wx ≤ q.1.w - q.2 * q.1.wx := Nat.min_le_left _ _
  have hr : q.1.w - q.2 * q.1.wx < 2 ^ 31 := by omega
  generalize q.1.w - q.2 * q.1.wx = r at hrem h12 h16 hcr hr
  generalize min r q.1.wx = c at h12 h16 hcr
  have hn := hc.good.scr.nowrap
  have rok := redcRanges_ok q.1.wx
  have hX : ∀ v : BitVec 64, (t.mem.writeW (off q.1.B (q.1.o + 8 * sSrc)) v).readW
      (off q.1.B (q.1.o + 8 * sRem)) 64 = BitVec.ofNat 64 r := fun v => by
    rw [store_off, ← off_off]
    exact (hdrStore_hdr t.mem (off q.1.B q.1.o) v (by decide) (by decide) (by decide)).trans hrem
  refine WP.mono (WP.keep [.x3] (Q := fun t₁ => ∃ v₁ v₂ : BitVec 64, t₁.mem = (t.mem.writeW
      (off (off q.1.B q.1.o) (8 * sSrc)) v₁).writeW (off (off q.1.B q.1.o) (8 * sRem)) v₂)
    (by brun [raBlock, hc.x0, h16, h12, hdr_enc (show sSrc < 32 by decide), hdr_enc (show sRem < 32 by decide),
      hc.st' (show sSrc < 32 by decide), hc.ld' (show sRem < 32 by decide), hc.st' (show sRem < 32 by decide), hX,
      off_off]; exact ⟨_, _, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨v₁, v₂, hm₁⟩, k₁⟩ => ?_
  have o1 := writeW_outside t.mem (off q.1.B q.1.o) (d := 8 * sSrc) v₁ (by decide)
  have o2 := writeW_outside (t.mem.writeW (off (off q.1.B q.1.o) (8 * sSrc)) v₁) (off q.1.B q.1.o) (d := 8 * sRem)
    v₂ (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm (off q.1.B q.1.o) (redcRanges q.1.wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [redcRanges])).trans (Frm.of_outside o2 (by simp [redcRanges]))
  exact ⟨minv, X, hc.of_frm f₁ rok k₁.wr (k₁.gpr .x0 (by decide)), hv.of_frm (by omega) (by omega) f₁, hX1, hf⟩

theorem ra1_ok (M : Mont) {p : XPub} {t : State} (h : RA0 p t) :
    WP isa (M.mm aXc aXc Public.aOne) t (RA1 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aXc) (a := aXc) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt, _⟩ => ⟨minv, X, hc', hv', hX1, hlt, hf⟩

theorem ra2_ok (M : Mont) {p : XPub} {t : State} (h : RA1 p t) :
    WP isa (M.mm aT aChunk Public.aOne) t (RA2 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hlt, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hn : (off p.B p.o).toNat + slot p.wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aT) (a := aChunk) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt', _, ha, _⟩ =>
      ⟨minv, X, hc', hv', by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hlt, hlt', hf⟩

theorem ra3_ok {p : XPub} {t : State} (h : RA2 p t) :
    WP isa (addMod aXc aXc aT) t fun t' => t'.gpr .x0 = off p.B p.o := by
  obtain ⟨minv, X, hc, hv, hlt, hlt', hw2, hwx, hw30⟩ := h
  exact WP.mono (addMod_ok hc.good.scr hc.x0 hc.hdr (Nat.le_refl _) hw2 (by omega) (o := aXc) (a := aXc) (b := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hv.n]; exact hlt) (by rw [hv.n]; exact hlt')) fun t' ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hc.x0

/-- The words left and the source advanced, and `A := A R⁻¹ + c R⁻¹`. -/
theorem redcAcc_ct (M : Mont) (j : Nat) : RelCT isa (Two (RB5 j)) (seqs (redcAcc M.mm)) fun _ _ => True := by
  simp only [redcAcc, seqs]
  refine RelCT.seq (two_piece (Ψ := fun q t => RA0 q.1 t) [.x0]
    (pins_subCtx (·.1) fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide) fun _ _ h => ra0_ok h)
    (two_map (fun q => q.1) (fun _ _ h => h) ?_)
  refine RelCT.seq (two_post (Ψ := RA1) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => ra1_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := RA2) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => ra2_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .x0 = off p.B p.o) (two_map XPub.ws
    (fun p _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))) fun _ _ h => ra3_ok h) ?_
  exact two_taint [.x0] (pins_x0B (fun p => off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- One chunk. -/
theorem redcBody_ct (M : Mont) (j : Nat) :
    RelCT isa (Two (RBody j)) (seqs (redcLoad ++ redcAcc M.mm)) fun _ _ => True := by
  refine RelCT.seqs_append (by simp [redcLoad]) (by simp [redcAcc])
    (RelCT.seq (two_post (Ψ := RB5 j) (redcLoad_ct j) fun q t h => ?_) (redcAcc_ct M j))
  obtain ⟨hk, s, minv, X, hI, hf, hX1, hj⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hsl := slot_le (w := q.1.w) hj
  have hrem0 := hI.rem
  have hsrc0 := hI.src
  rw [hlw] at hrem0 hsrc0
  exact WP.mono (redcLoad_ok hI.ctx hw2 hwx hw30 hj (r := q.1.w - q.2 * q.1.wx)
    (e := slot q.1.w j + 8 * (q.2 * q.1.wx)) (by omega) (by omega) (by omega) hrem0 hsrc0)
    fun t₁ ⟨hc₁, h12₁, h16₁, _, hrem₁, _, _, f₁, _⟩ =>
      ⟨minv, X, hc₁, hI.xv.of_frm (by have := hc₁.good.scr.nowrap; omega) (by omega) f₁, hX1, h12₁, h16₁, hrem₁, hf⟩

/-! ## `redc` -/

/-- After `A := 0`. -/
def RZ (p : XPub) (t : State) : Prop := ∃ minv, SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XF p

/-- After the load of `n`'s base. -/
def RL (p : XPub) (t : State) : Prop := t.gpr .x0 = off p.B p.o ∧ t.gpr .x5 = p.B

theorem rz_ok {j : Nat} {p : XPub} {s : State} (h : RPre j p s) : WP isa (zeroArr aXc) s (RZ p) := by
  obtain ⟨minv, X, hc, _, hw2, hwx, hw30, _⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  exact WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (show aXc < 8 by decide))
    fun s₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.wr
      (k₁.gpr .x0 (by decide)), hw2, hwx, hw30⟩

theorem rl_ok {p : XPub} {t : State} (h : RZ p t) : WP isa (.block [ldh .x5 sLink]) t (RL p) := by
  obtain ⟨_, hc, _⟩ := h
  exact WP.mono (WP.keep [.x5] (Q := fun t' => t'.gpr .x5 = p.B)
    (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨h1, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, h1⟩

/-- `redc`'s start, given that the taint analysis checks its loads through
`n`'s base (`by taint_decide` for a given `j`). -/
theorem redcHead_ct {j : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x3 .x5 (sArr j), sth .x3 sSrc, ldw .x3 .x5 sW,
      sth .x3 sRem]) hc).isSome = true) :
    RelCT isa (Two (RPre j)) (.seq (zeroArr aXc) (.block [ldh .x5 sLink, ldw .x3 .x5 (sArr j), sth .x3 sSrc,
      ldw .x3 .x5 sW, sth .x3 sRem])) fun _ _ => True :=
  RelCT.seq (two_post (Ψ := RZ) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (zeroArr_ct (by decide) (by taint_decide))) fun _ _ h => rz_ok h)
    (RelCT.block_append (l₁ := ([ldh .x5 sLink] : List Instr))
      (RelCT.seq (two_piece (Ψ := RL) [.x0] (pins_subCtx id fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide)
        fun _ _ h => rl_ok h)
      (two_taint [.x0, .x5] (pins_of (fun p r => if r = .x0 then off p.B p.o else p.B) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT)))

/-- `redc j`, given that the taint analysis checks its loads through `n`'s
base. -/
theorem redc_ct_of (M : Mont) {j : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x3 .x5 (sArr j), sth .x3 sSrc, ldw .x3 .x5 sW,
      sth .x3 sRem]) hc).isSome = true) :
    RedcCT M j := by
  unfold RedcCT
  rw [redc_eq]
  simp only [seqs]
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun p t => 0 < (p.w + p.wx - 1) / p.wx ∧ RLoop j p 0 t)
    (redcHead_ct hT) fun p s h => ?_) ((two_loop (Φ := RLoop j) (Ψ := fun _ _ => True)
      (fun p => (p.w + p.wx - 1) / p.wx) (redcBody_ct M j) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, X, hc, hv, hw2, hwx, hw30, hX1, hj⟩ := h
    have hn := hc.good.scr.nowrap
    have hK : 0 < (p.w + p.wx - 1) / p.wx := (lt_chunks (k := 0) (by omega)).mpr (by omega)
    have hl0 : lowW p.w p.wx 0 = 0 := by simp [lowW]
    exact WP.mono (redcHead_ok hc hw2 hwx hw30 hj) fun t₁ ⟨hc₁, hz₁, hsrc₁, hrem₁, f₁, k₁⟩ =>
      ⟨hK, s, minv, X, ⟨hc₁, hv.of_frm hn (by omega) f₁, by rw [hl0, Nat.sub_zero]; exact hrem₁,
        by rw [hl0, Nat.mul_zero, Nat.add_zero]; exact hsrc₁, by rw [hz₁]; omega, by rw [hz₁, hl0]; rfl, f₁, k₁⟩,
        ⟨hw2, hwx, hw30⟩, hX1, hj⟩
  · rintro p k t hk ⟨s, minv, X, hI, hf, hX1, hj⟩
    obtain ⟨hw2, hwx, hw30⟩ := id hf
    exact WP.mono (redcStep_ok M hw2 hwx hw30 hX1 hj hk hI) fun t' ⟨hI', hz⟩ =>
      ⟨eval_nz_count hk hz, fun _ => ⟨s, minv, X, hI', hf, hX1, hj⟩, fun _ => trivial⟩

theorem redc_ct_Y (M : Mont) : RedcCT M Public.aY := redc_ct_of M (by taint_decide)

theorem redc_ct_X (M : Mont) : RedcCT M Public.aX := redc_ct_of M (by taint_decide)

end VG.Proof.Bignum.AArch64
