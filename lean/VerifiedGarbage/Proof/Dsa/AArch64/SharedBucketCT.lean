module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedStoreCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedStoreCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The buckets' updates leak neither digit of the secret exponent

The secret digit's bucket is read by the scan of every entry and written by
the masked store of every entry; the public digit's bucket is read and
written at its address, which the public data fix. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower

/-! ## The secret digit's bucket -/

/-- `secretBucket_ok`'s hypotheses. -/
def SBPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc V : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 64 ∧ Xc < X

/-- With the digit in `sNib`: through the scan and the multiplication. -/
def SBMid (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ v < 8 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v ∧ Xc < X

theorem SBMid.sel {p : XPub} {s : State} (h : SBMid p s) : WindowVector.SelPn 16 p s :=
  let ⟨mi, X, Xc, v, hc, hw, hw', _, hv, ht, hn, _⟩ := h
  ⟨mi, X, Xc, v, hc, by omega_using [hw], hw', by omega_using [hv], ht, hn⟩

theorem SBMid.goodW {p : XPub} {s : State} (h : SBMid p s) : GoodW p.ws s :=
  let ⟨mi, _, _, _, hc, _⟩ := h; ⟨mi, hc.good, Nat.le_refl _⟩

theorem sbDigit_post {p : XPub} {s : State} (h : SBPre p s) : WP isa (.block secretDigit) s (SBMid p) := by
  obtain ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hA⟩ := h
  refine WP.mono (secretDigit_ok hc hV hV') fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V % 8)) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem s₁.mem := Frm.of_outside o₁ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, V % 8, hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hw, hw', hd, Nat.mod_lt _ (by decide),
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact ht,
    by rw [hm₁, word_writeW_self], hA⟩

theorem sbSelect_post {p : XPub} {s : State} (h : SBMid p s) :
    WP isa VG.Impl.Rsa.AArch64.Crt.select s (SBMid p) := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, hA⟩ := h
  have hv16 : v < 16 := by omega_using [hv]
  refine WP.mono (WindowVector.select_ok (Or.inl rfl)
    (fun hu tab nib => tabSel_ok hu (by omega_using [hw]) hw' hv16 tab nib) hc hw' hv16 ht hn)
    fun t ⟨hc₂, _, f₂, _⟩ => ?_
  exact ⟨mi, X, Xc, v, hc₂, hw, hw', hd, hv, (sel_hdr f₂ (by decide) (by decide) (by decide)).trans ht,
    (sel_hdr f₂ (by decide) (by decide) (by decide)).trans hn, hA⟩

theorem sbMul_post (M : Mont) {p : XPub} {s : State} (h : SBMid p s) :
    WP isa (M.mm Crt.aT Crt.aT Crt.aXc) s (SBMid p) := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, hA⟩ := h
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _)
    (by omega_using [hw]) (by omega_using [hw']) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨_, _, _, ha₃, k₃⟩ => ?_
  have f₃ : Frm (off p.B p.o) (crtWinRanges p.wx) s.mem t.mem := Frm.of_arrays ha₃ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, v, hc.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide)), hw, hw', hd, hv,
    (ha₃.hslot (by decide)).trans ht, (ha₃.hslot (by decide)).trans hn, hA⟩

/-- The secret digit's bucket is updated with the same addresses and
branches whatever the digit. -/
theorem secretBucket_ct (M : Mont) : RelCT isa (Two SBPre)
    (seqs [.block secretDigit, VG.Impl.Rsa.AArch64.Crt.select, M.mm Crt.aT Crt.aT Crt.aXc, store])
    (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_x0B (fun p : XPub => off p.B p.o)
    fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.x0) (by unfold secretDigit; taint_decide) fun _ _ h => sbDigit_post h) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.sel) (WindowVector.select_ct (Or.inl rfl) tabSel_ct))
    fun _ _ h => sbSelect_post h) ?_
  refine RelCT.seq (two_post (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW)
    (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide))) fun _ _ h => sbMul_post M h) ?_
  exact two_map id (fun _ _ ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn, _⟩ =>
    ⟨mi, X, Xc, v, hc, hw, hw', hd, hv, ht, hn⟩) store_ct

/-! ## The public digit's bucket -/

/-- After `put`'s exchange: the source and the destination of the copy. -/
def PutRegs (p : XPub × Nat) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 p.1.wx ∧
  s.gpr .x16 = off (off p.1.B p.1.o) (slot p.1.wx Crt.aT) ∧
  s.gpr .x17 = off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2))

/-- The store of `[aT]` to the entry the public data name. -/
theorem put_ct : RelCT isa (Two PublicPower.SelectPre) put (fun _ _ => True) := by
  unfold put
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := PublicPower.SelectRegs) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0))
    (by unfold VG.Impl.Dsa.AArch64.PublicPower.selectHead; taint_decide) (fun p s ⟨_, _, _, hc, _, hw', hv, ht, hn⟩ =>
      WP.mono (PublicPower.selectHead_ok hc hw' hv ht hn) (fun _ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩)))
    (two_piece (Ψ := PutRegs) [] (fun _ _ _ _ _ _ hr => nomatch hr) (by taint_decide) fun p s ⟨h12, h16, h17⟩ => ?_))) ?_
  · refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun a => a.gpr .x16 = s.gpr .x17 ∧
      a.gpr .x17 = s.gpr .x16) (by brun []) rfl rfl rfl) fun a ⟨⟨a16, a17⟩, ka⟩ => ?_
    exact ⟨(ka.gpr .x12 (by decide)).trans h12, a16.trans h17, a17.trans h16⟩
  exact two_taint [.x12, .x16, .x17] (pins_of
    (fun p r => if r = .x12 then BitVec.ofNat 64 p.1.wx else
      if r = .x16 then off (off p.1.B p.1.o) (slot p.1.wx Crt.aT) else
        off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2))) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)) (by taint_decide)

/-- `publicBucket_ok`'s hypotheses, the digit public. -/
def PBPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.2 < 8 ∧ word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    s.gpr .x3 = BitVec.ofNat 64 p.2 ∧ Xc < X

/-- With the entry's index in `sNib`. -/
def PBMid (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.2 < 16 ∧ word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 p.2 ∧ Xc < X

theorem PBMid.sel {p : XPub × Nat} {s : State} (h : PBMid p s) : PublicPower.SelectPre p s :=
  let ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, _⟩ := h; ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn⟩

theorem pbIndex_ok {s : State} {P : Addr} {wx : Nat} {mi : BitVec 64} {X Xc d : Nat}
    (hc : CExpCtx s P wx mi X Xc) (h3 : s.gpr .x3 = BitVec.ofNat 64 d) :
    WP isa (.block [.addImm .x .x3 .x3 8, sth .x3 Crt.sNib]) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (8 + d)) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  brun [hc.good.x0, hdr_enc (show Crt.sNib < 32 by decide), hc.st (i := Crt.sNib) (by decide), h3,
    ofNat_add_ofNat]
  rw [Nat.add_comm]

theorem pbIndex_post {p : XPub × Nat} {s : State} (h : PBPre p s) :
    WP isa (.block [.addImm .x .x3 .x3 8, sth .x3 Crt.sNib]) s (PBMid (p.1, 8 + p.2)) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hd, ht, h3, hA⟩ := h
  refine WP.mono (pbIndex_ok hc h3) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off p.1.B p.1.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (8 + p.2)) (by decide)
  rw [← hm₁] at o₁
  have f₁ : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem s₁.mem :=
    Frm.of_outside o₁ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, hc.of_win f₁ k₁.wr (k₁.gpr .x0 (by decide)), hw, hw', by omega_using [hd],
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact ht,
    by rw [hm₁, word_writeW_self], hA⟩

theorem pbSelect_post {p : XPub × Nat} {s : State} (h : PBMid p s) :
    WP isa VG.Impl.Dsa.AArch64.PublicPower.select s (PBMid p) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, hA⟩ := h
  refine WP.mono (PublicPower.select_ok hc hw hw' hv ht hn) fun t ⟨hc₂, _, o₂, _⟩ => ?_
  have hh₂ : ∀ k < 32, word t.mem (off p.1.B p.1.o) (8 * k) = word s.mem (off p.1.B p.1.o) (8 * k) :=
    fun k hk => o₂.word (Or.inl (hdr_lt_slot p.1.wx Crt.aT hk)) (by omega_arith)
  exact ⟨mi, X, Xc, hc₂, hw, hw', hv, (hh₂ _ (by decide)).trans ht, (hh₂ _ (by decide)).trans hn, hA⟩

theorem pbMul_post (M : Mont) {p : XPub × Nat} {s : State} (h : PBMid p s) :
    WP isa (M.mm Crt.aT Crt.aT Crt.aXc) s (PBMid p) := by
  obtain ⟨mi, X, Xc, hc, hw, hw', hv, ht, hn, hA⟩ := h
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _)
    hw (by omega_using [hw']) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨_, _, _, ha₃, k₃⟩ => ?_
  have f₃ : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem :=
    Frm.of_arrays ha₃ (by simp [crtWinRanges])
  exact ⟨mi, X, Xc, hc.of_win f₃ k₃.wr (k₃.gpr .x0 (by decide)), hw, hw', hv,
    (ha₃.hslot (by decide)).trans ht, (ha₃.hslot (by decide)).trans hn, hA⟩

/-- The public digit's bucket is updated at the address the digit names. -/
theorem publicBucket_ct (M : Mont) : RelCT isa (Two PBPre) (publicBucket M.mm) (fun _ _ => True) := by
  unfold publicBucket
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun (p : XPub × Nat) s => PBMid (p.1, 8 + p.2) s) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0) (by taint_decide)
    fun _ _ h => pbIndex_post h) ?_
  refine two_map (fun p : XPub × Nat => (p.1, 8 + p.2)) (fun _ _ h => h) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.sel) PublicPower.select_ct)
    fun _ _ h => pbSelect_post h) ?_
  refine RelCT.seq (two_post (two_map (fun p : XPub × Nat => p.1.ws)
    (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
    (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide))) fun _ _ h => pbMul_post M h) ?_
  exact two_map id (fun _ _ h => h.sel) put_ct

/-- `publicHalf_ok`'s hypotheses, the value in `sMaskX` public. -/
def PHPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sMaskX) = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 64 ∧ Xc < X

/-- The public digit: whether it is zero, and its bucket's address, are the
public data's. -/
theorem publicHalf_ct (M : Mont) : RelCT isa (Two PHPre)
    (seqs [.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket M.mm)]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun (p : XPub × Nat) s => PBPre (p.1, p.2 % 8) s) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0)
    (by unfold publicDigit; taint_decide) fun p s ⟨mi, X, Xc, hc, hw, hw', ht, hQ, hQ', hA⟩ => ?_) ?_
  · refine WP.mono (publicDigit_ok hc hQ hQ') fun u ⟨⟨h3, hm⟩, hk⟩ => ?_
    exact ⟨mi, X, Xc, hc.of_win (hm ▸ Frm.refl _ _ _) hk.wr (hk.gpr .x0 (by decide)), hw, hw',
      Nat.mod_lt _ (by decide), hm ▸ ht, h3, hA⟩
  refine two_ite (fun p s t hs ht => ?_) ?_ ?_
  · obtain ⟨_, _, _, _, _, _, _, _, hs3, _⟩ := hs
    obtain ⟨_, _, _, _, _, _, _, _, ht3, _⟩ := ht
    have hlt : p.2 % 8 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [PublicPower.eval_zero_x3 hs3 hlt, PublicPower.eval_zero_x3 ht3 hlt]
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_map (fun p : XPub × Nat => (p.1, p.2 % 8)) (fun _ _ h => h.1) (publicBucket_ct M)

end VG.Proof.Dsa.AArch64.SharedPower
