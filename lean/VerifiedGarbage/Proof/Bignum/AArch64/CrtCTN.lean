import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront

/-!
# RSA with the CRT on AArch64: the input in constant time

`setWord` (`setWord_ct`), and `nInput`, which loads the input `c` into `X`,
the mask of `c < n` and the number 1 (`nInput_ct`): the bases and counts it
loads from the header, which the taint analysis takes as secret, are pinned
by the steps of `nInput_ok`, and the input's bytes, a secret, flow only into
data.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (borrowMask)
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## `setWord` -/

/-- `setWord`'s hypotheses for its timing: the workspace, `w` in `x12` and
the word's index in `x13`. -/
def SWPre (q : Ws × Nat) (s : State) : Prop :=
  GoodW q.1 s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x13 = BitVec.ofNat 64 q.2

/-- `setWord o` leaks the same in runs with the same workspace and index,
given that the taint analysis checks its load from `x0`. -/
theorem setWord_ct {o : Nat} (ho : o < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr o), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two SWPre) (setWord o) fun _ _ => True := by
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := fun (q : Ws × Nat) t => t.gpr .x8 = off q.1.B (slot q.1.w o) ∧
      t.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ t.gpr .x13 = BitVec.ofNat 64 q.2) [.x0]
    (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1 s₁ s₂ h₁.1 h₂.1) hT ?_)
    (two_taint [.x8, .x12, .x13] (pins_of (fun (q : Ws × Nat) r => if r = .x8 then off q.1.B (slot q.1.w o)
      else if r = .x12 then BitVec.ofNat 64 q.1.w else BitVec.ofNat 64 q.2) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro q s ⟨hgw, h12, h13⟩
  have hl := hgw.hl
  obtain ⟨_, hg, -⟩ := hgw
  exact WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off q.1.B (slot q.1.w o))
    (by brun [hg.x0, hdr_enc (sArr_lt ho), hl (sArr o) (sArr_lt ho), hg.hdr.harr o ho]) rfl rfl rfl)
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13⟩

/-! ## `nInput` -/

/-- The public data of `nInput`: the working space, `k` and the input's
pointer. -/
structure NIPub where
  B : Addr
  Z : Nat
  k : Nat
  ip : Addr

abbrev NIPub.w (p : NIPub) : Nat := (p.k + 7) / 8

/-- The modulus' workspace. -/
abbrev NIPub.ws (p : NIPub) : Ws := ⟨p.B, p.Z, p.w⟩

/-- `nInput_ok`'s hypotheses. -/
def NIPre (p : NIPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (xb : List Byte), Good s p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word s.mem p.B (8 * sIn) = p.ip ∧ Src s p.B p.Z p.ip xb ∧
    xb.length = p.k

/-- The workspace and its size, as the later steps need them. -/
def NIG (p : NIPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, Good s p.B p.Z p.w minv ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024

theorem NIG.x0 {p : NIPub} {s : State} (h : NIG p s) : s.gpr .x0 = p.B := let ⟨_, hg, _⟩ := h; hg.x0

/-- After the input's bases. -/
def NI1 (p : NIPub) (s : State) : Prop :=
  NIPre p s ∧ s.gpr .x1 = p.ip ∧ s.gpr .x2 = BitVec.ofNat 64 p.k ∧ s.gpr .x8 = off p.B (slot p.w aX)

/-- Before the comparison: its bases, and the carry set. -/
def NI3 (p : NIPub) (s : State) : Prop :=
  NIG p s ∧ s.gpr .x16 = off p.B (slot p.w aX) ∧ s.gpr .x17 = off p.B (slot p.w aN) ∧ s.gpr .x7 = 0 ∧
    s.gpr .x14 = BitVec.ofNat 64 p.w ∧ s.c = true

/-- Before `setWord`. -/
def NI5 (p : NIPub) (s : State) : Prop :=
  NIG p s ∧ s.gpr .x12 = BitVec.ofNat 64 p.w ∧ s.gpr .x13 = BitVec.ofNat 64 0

theorem ni1_ok {p : NIPub} {s : State} (h : NIPre p s) :
    WP isa (.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)]) s (NI1 p) := by
  obtain ⟨minv, xb, hg, hZ, hk1, hk2, hK, hIn, hx, hxl⟩ := id h
  exact WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = p.ip ∧ t.gpr .x2 = BitVec.ofNat 64 p.k ∧
      t.gpr .x8 = off p.B (slot p.w aX) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sIn < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (sArr_lt (show aX < 8 by decide)), hg.ld hZ (show sIn < 32 by decide),
      hg.ld hZ (show sK < 32 by decide), hg.ld hZ (sArr_lt (show aX < 8 by decide)), hIn, hK,
      hg.hdr.harr aX (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h1, h2, h8, hm⟩, k⟩ => ⟨⟨minv, xb, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0,
      hm ▸ hg.hdr⟩, hZ, hk1, hk2, hm ▸ hK, hm ▸ hIn, hx.congrK (by rw [hm]; exact InScr.refl _ _ _) k, hxl⟩,
      h1, h2, h8⟩

theorem ni2_ok {p : NIPub} {s : State} (h : NI1 p s) : WP isa loadBE s (NIG p) := by
  obtain ⟨⟨minv, xb, hg, hZ, hk1, hk2, -, -, hx, hxl⟩, h1, h2, h8⟩ := h
  refine WP.mono (loadArr_ok hg.scr (show aX < 8 by decide) hZ hx hxl (by omega) (by omega) h1 h2 h8)
    fun t ⟨_, ha, k⟩ => ⟨minv, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0,
      ⟨by rw [ha.hslot (by decide)]; exact hg.hdr.hw, by rw [ha.hslot (by decide)]; exact hg.hdr.hminv,
        fun j hj => by rw [ha.hslot (sArr_lt hj)]; exact hg.hdr.harr j hj⟩⟩, hZ, hk1, hk2⟩

theorem ni3_ok {p : NIPub} {s : State} (h : NIG p s) :
    WP isa (.block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7]) s (NI3 p) := by
  obtain ⟨minv, hg, hZ, hk1, hk2⟩ := h
  exact WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off p.B (slot p.w aX) ∧ t.gpr .x17 = off p.B (slot p.w aN) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 p.w ∧ t.c = true ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aX < 8 by decide)),
      hdr_enc (sArr_lt (show aN < 8 by decide)), hg.ld hZ (show sW < 32 by decide),
      hg.ld hZ (sArr_lt (show aX < 8 by decide)), hg.ld hZ (sArr_lt (show aN < 8 by decide)), hg.hdr.hw,
      hg.hdr.harr aX (by decide), hg.hdr.harr aN (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h16, h17, h7, h14, hc, hm⟩, k⟩ => ⟨⟨minv, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0,
      hm ▸ hg.hdr⟩, hZ, hk1, hk2⟩, h16, h17, h7, h14, hc⟩

/-- The comparison, its mask and `setWord`'s operands. -/
def niTail : List Instr := borrowMask ++ [sth .x15 sMask, ldh .x12 sW, movi .x9 1, movi .x13 0]

theorem ni5_ok {p : NIPub} {s : State} (h : NI3 p s) : WP isa (.seq cmpLoop (.block niTail)) s (NI5 p) := by
  obtain ⟨⟨minv, hg, hZ, hk1, hk2⟩, h16, h17, h7, h14, hc⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have lX := slot_le (w := p.w) (show aX < 8 by decide)
  have lN := slot_le (w := p.w) (show aN < 8 by decide)
  have eM : sMask = 22 := rfl
  have eW : sW = 6 := rfl
  have eMi : sMinv = 7 := rfl
  have hw : p.w = (p.k + 7) / 8 := rfl
  refine WP.seq (WP.mono (cmpLoop_ok hs h16 h17 h14 hc (by omega) (by omega) (by omega) (by omega))
    fun s₄ ⟨_, hm₄, k₄⟩ => ?_)
  have h0₄ : s₄.gpr .x0 = p.B := (k₄.gpr .x0 (by decide)).trans hg.x0
  have h7₄ : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans h7
  have hs₄ := hs.congr k₄.wr
  have hW' : ∀ v : BitVec 64, word (s₄.mem.writeW (off p.B (8 * sMask)) v) p.B (8 * sW) =
      BitVec.ofNat 64 p.w := fun v => by
    rw [(writeW_outside s₄.mem p.B v (by omega)).word (by rw [eM]; unfold sW; omega) (by omega), hm₄]
    exact hg.hdr.hw
  have st := hs₄.st (show 8 * sMask + 8 ≤ p.Z by rw [eM]; omega)
  have ld := hs₄.ld (show 8 * sW + 8 ≤ p.Z by have := hdr_lt_slot p.w 8 (show sW < 32 by decide); omega)
  have e1 := hdr_enc (show sMask < 32 by decide)
  have e2 := hdr_enc (show sW < 32 by decide)
  have hb : WP isa (.block niTail) s₄ fun t => (∃ v : BitVec 64, t.mem = s₄.mem.writeW (off p.B (8 * sMask)) v) ∧
      t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x13 = BitVec.ofNat 64 0 := by
    brun [niTail, borrowMask, h0₄, h7₄, e1, e2, st, ld, hW']
    exact ⟨_, rfl⟩
  refine WP.mono (WP.keep [.x4, .x9, .x12, .x13, .x15] hb (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨⟨v, hm⟩, h12, h13⟩, k⟩ => ⟨⟨minv, ⟨hs₄.congr k.wr, (k.gpr .x0 (by decide)).trans h0₄, ?_⟩, hZ, hk1, hk2⟩,
      h12, h13⟩
  have hwo : Outside p.B (8 * sMask) 8 s₄.mem t.mem := by rw [hm]; exact writeW_outside _ p.B _ (by omega)
  have hh : ∀ i < 16, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi => by
    rw [hwo.word (by rw [eM]; omega) (by omega), hm₄]
  exact ⟨(hh _ (by decide)).trans hg.hdr.hw, (hh _ (by decide)).trans hg.hdr.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩

/-- `nInput` leaks the same in runs with the same working space, `k` and
input pointer. -/
theorem nInput_ct : RelCT isa (Two NIPre) (seqs nInput) fun _ _ => True := by
  simp only [nInput, seqs]
  refine RelCT.seq (two_piece (Ψ := NI1) [.x0] (pins_x0B (fun p : NIPub => p.B)
    fun _ _ ⟨_, _, hg, _⟩ => hg.x0) (by taint_decide) fun _ _ h => ni1_ok h) ?_
  refine RelCT.seq (two_post (Ψ := NIG) (two_taint [.x0, .x1, .x2, .x8] (pins_of (fun (p : NIPub) r =>
      if r = .x0 then p.B else if r = .x1 then p.ip else if r = .x2 then BitVec.ofNat 64 p.k
      else off p.B (slot p.w aX)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨⟨_, _, hg, _⟩, h1, h2, h8⟩ := h
        rcases hr with rfl | rfl | rfl | rfl
        · exact hg.x0
        · exact h1
        · exact h2
        · exact h8) (by taint_decide)) fun _ _ h => ni2_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := NI3) [.x0] (pins_x0B (fun p : NIPub => p.B) fun _ _ h => h.x0)
    (by taint_decide) fun _ _ h => ni3_ok h) ?_
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := NI5) [.x0, .x14, .x16, .x17] (pins_of (fun (p : NIPub) r =>
      if r = .x0 then p.B else if r = .x14 then BitVec.ofNat 64 p.w else if r = .x16 then off p.B (slot p.w aX)
      else off p.B (slot p.w aN)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨hg, h16, h17, -, h14, -⟩ := h
        rcases hr with rfl | rfl | rfl | rfl
        · exact hg.x0
        · exact h14
        · exact h16
        · exact h17) (by taint_decide) fun _ _ h => ni5_ok h) ?_)
  exact two_map (fun p : NIPub => (p.ws, 0)) (fun p s ⟨⟨minv, hg, hZ, _⟩, h12, h13⟩ => ⟨⟨minv, hg, hZ⟩, h12, h13⟩)
    (setWord_ct (by decide) (by taint_decide))

end VG.Proof.Bignum.AArch64
