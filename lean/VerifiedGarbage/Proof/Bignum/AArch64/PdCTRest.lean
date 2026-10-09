import VerifiedGarbage.Proof.Bignum.AArch64.PdCTExp

/-!
# `vg_rsa_public_precomputed` on AArch64: `rest` is constant time but for `e`

`rest` (the input, the mask of `input < m`, `-m⁻¹`, the number 1, the
exponentiation and the result) leaks the same in runs that agree on the
pointers, the lengths, `e`, `m` and `R² mod m` (`pdRest_ct`). The public-key
operation from the modulus ends with the same `rest`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

variable {M : Mont}

theorem WP.and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-! ## The comparison, `-m⁻¹` and the number 1 -/

/-- The public data of the comparison, `-m⁻¹` and the number 1: the working
space and `w`. -/
structure RPub where
  B : Addr
  Z : Nat
  w : Nat

/-- What the comparison, `-m⁻¹` and the number 1 need: the working space, the
header's `w` and bases, and `m` odd. -/
def SR (p : RPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 31 ∧
    word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧ (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    (word s.mem p.B (slot p.w aN)).toNat % 2 = 1

/-- `SR` with the same memory, and `x0` kept. -/
theorem SR.mem {p : RPub} {s t : State} (h : SR p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : SR p t :=
  let ⟨hs, h0, hZ, hw, hw', hW, hb, hodd⟩ := h
  ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hw, hw', hm ▸ hW, hm ▸ hb, hm ▸ hodd⟩

theorem pins_SR : Pins SR [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the comparison's registers. -/
def S5 (p : RPub) (s : State) : Prop :=
  SR p s ∧ s.gpr .x16 = off p.B (slot p.w aX) ∧ s.gpr .x17 = off p.B (slot p.w aN) ∧
    s.gpr .x14 = BitVec.ofNat 64 p.w ∧ s.c = true

/-- Before `-m⁻¹`: `m`'s base. -/
def S7 (p : RPub) (s : State) : Prop := SR p s ∧ s.gpr .x8 = off p.B (slot p.w aN)

/-- After `-m⁻¹`. -/
def S8 (p : RPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, Hdr s.mem p.B p.w mi ∧ Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧
    s.gpr .x12 = BitVec.ofNat 64 p.w ∧ s.gpr .x13 = BitVec.ofNat 64 0

theorem pins_S8 : Pins S8 [.x0] := fun _ _ _ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]

/-- The mask's store and `m`'s base. -/
theorem setupC1_ok {p : RPub} {s : State} (h : SR p s) :
    WP isa (.block [.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN)]) s (S7 p) := by
  have h' := h
  obtain ⟨hs, h0, hZ, -, -, hW, hb, hodd⟩ := h'
  have hn := hs.nowrap
  obtain ⟨g0, g8⟩ := slot0_ge p.w
  have hsN := slot_le (w := p.w) (show aN < 8 by decide)
  have eK : sMask = 22 := rfl
  have eAN : sArr aN = 8 := rfl
  have hrd : ∀ v : BitVec 64, (s.mem.writeW (off p.B (8 * sMask)) v).readW (off p.B (8 * sArr aN)) 64 =
      off p.B (slot p.w aN) := fun v => by
    rw [← hb aN (by decide)]
    exact (writeW_outside _ p.B _ (by omega_using [eK])).word (by omega_using [eK, eAN]) (by omega_using [eAN])
  refine WP.mono (WP.keep [.x4, .x8, .x15] (Q := fun t => t.gpr .x8 = off p.B (slot p.w aN) ∧
      t.mem = s.mem.writeW (off p.B (8 * sMask)) (t.gpr .x15)) (by
    brun [h0, hdr_enc (show sMask < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
      hs.st (d := 8 * sMask) (by omega_using [hZ, g0, g8, eK]), hs.ld (d := 8 * sArr aN) (by omega_using [hZ, g0, g8, eAN]), hrd])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h8, hm⟩, k⟩ => ⟨?_, h8⟩
  have ho : Outside p.B (8 * sMask) 8 s.mem t.mem := by rw [hm]; exact writeW_outside _ p.B _ (by omega_using [eK])
  exact ⟨hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, hZ, h.2.2.2.1, h.2.2.2.2.1,
    by rw [ho.word (by unfold sW; omega_using [eK]) (by unfold sW; omega_using [])]; exact hW,
    fun j hj => by rw [ho.word (d := 8 * sArr j) (by unfold sArr; omega_using [eK, hj]) (by unfold sArr; omega_using [hj])]; exact hb j hj,
    by rw [ho.word (by have := hdr_lt_slot p.w aN (show sMask < 32 by decide); omega_using [this]) (by omega_using [hZ, hn, hsN])]; exact hodd⟩

/-- `-m⁻¹` into its slot, and the number 1's registers. -/
theorem setupC2_ok {p : RPub} {s : State} (h : S7 p s) :
    WP isa (.block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) s (S8 p) := by
  obtain ⟨⟨hs, h0, hZ, -, -, hW, hb, hodd⟩, h8⟩ := h
  have hn := hs.nowrap
  obtain ⟨g0, g8⟩ := slot0_ge p.w
  have hsN := slot_le (w := p.w) (show aN < 8 by decide)
  have h8' := hdr_lt_slot p.w aN (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = word s.mem p.B (slot p.w aN) ∧ t.mem = s.mem) (by
    brun [h8, hs.ld (d := slot p.w aN) (by omega_using [hZ, hsN])]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [h3₃]; exact hodd)) fun t₄ ⟨_, k₄, hm₄⟩ => ?_
  have hs₄ := (hs.congr k₃.wr).congr k₄.wr
  have h0₄ : t₄.gpr .x0 = p.B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0)
  have hm₄' : t₄.mem = s.mem := hm₄.trans hm₃
  have hW₄ : (t₄.mem.writeW (off p.B (8 * sMinv)) (t₄.gpr .x15)).readW (off p.B (8 * sW)) 64 =
      BitVec.ofNat 64 p.w := by
    rw [← hW, ← hm₄']
    exact (writeW_outside _ p.B _ (d := 8 * sMinv) (by omega_using [eM])).word (d := 8 * sW) (by omega_using [eW, eM]) (by omega_using [eW])
  refine WP.mono (WP.keep [.x9, .x12, .x13] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 p.w ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = t₄.mem.writeW (off p.B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.st (d := 8 * sMinv) (by omega_arith), hs₄.ld (d := 8 * sW) (by omega_using [hZ, hsN, h8', eW]), hW₄]) (by decide) (by decide)
      (by decide +kernel))
    fun t ⟨⟨h12, h13, hm⟩, k₅⟩ => ⟨t₄.gpr .x15, ⟨?_, by rw [hm, word_writeW_self], fun j hj => ?_⟩,
      hs₄.congr k₅.wr, (k₅.gpr .x0 (by decide)).trans h0₄, hZ, h12, h13⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₄']; exact hW
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by unfold sArr; omega_using [hj]) (by unfold sArr sMinv; omega_using []), hm₄']
    exact hb j hj

/-- The comparison, `-m⁻¹` and the number 1 leak the same in runs with the
same working space and `w`. -/
theorem setupRest_ct : RelCT isa (Two SR) (seqs setupSteps) fun _ _ => True := by
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := S5) _ pins_SR (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, h0, hZ, -, -, hW, hb, -⟩ := h'
    have hn := hs.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, g0, g8, hi])
    refine WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
        t.gpr .x16 = off p.B (slot p.w aX) ∧ t.gpr .x17 = off p.B (slot p.w aN) ∧
        t.gpr .x14 = BitVec.ofNat 64 p.w ∧ t.c = true ∧ t.mem = s.mem) (by
      brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
        hdr_enc (show sArr aN < 32 by decide), hl sW (by decide), hl (sArr aX) (by decide),
        hl (sArr aN) (by decide), hW, hb aX (by decide), hb aN (by decide)]) (by decide) (by decide)
        (by decide +kernel))
      fun t ⟨⟨h16, h17, h14, hc, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h16, h17, h14, hc⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := SR) [.x14, .x16, .x17] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) ?_) ?_
  · rintro p s ⟨h, h16, h17, h14, hc⟩
    have h' := h
    obtain ⟨hs, -, hZ, hw, hw', -⟩ := h'
    exact WP.mono (cmpLoop_ok hs h16 h17 h14 hc (by omega_using [hw]) hw'
      (by have := slot_le (w := p.w) (show aX < 8 by decide); omega_using [hZ, this])
      (by have := slot_le (w := p.w) (show aN < 8 by decide); omega_using [hZ, this])) fun t ⟨_, hm, k⟩ => h.mem hm k (by decide)
  -- The mask, `-m⁻¹`, and the number 1's registers.
  refine RelCT.seq (R := Two S8) (RelCT.block_append
    (l₁ := ([.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN)] : List Instr))
    (l₂ := [ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])
    (RelCT.seq (two_piece (Ψ := S7) _ pins_SR (by taint_decide) fun _ _ h => setupC1_ok h)
      (two_piece [.x0, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2.1, h₂.1.2.1]
        · rw [h₁.2, h₂.2]) (by taint_decide) fun _ _ h => setupC2_ok h))) ?_
  -- The number 1.
  show RelCT isa _ (seqs [setWord aOne]) _
  rw [seqs_one, setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : RPub) t => S8 p t ∧ t.gpr .x8 = off p.B (slot p.w aOne) ∧
      t.gpr .x7 = 0) _ pins_S8 (by taint_decide) ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun p s₁ s₂ h₁ h₂ r hr => by
      obtain ⟨⟨_, _, _, _, _, a₁, b₁⟩, c₁, d₁⟩ := h₁
      obtain ⟨⟨_, _, _, _, _, a₂, b₂⟩, c₂, d₂⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [c₁, c₂]
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [d₁, d₂]) (by taint_decide))
  rintro p s ⟨mi, hH, hs, h0, hZ, h12, h13⟩
  have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * sArr aOne)) 8 :=
    hs.ld (by have := hdr_lt_slot p.w 8 (show sArr aOne < 32 by decide); omega_using [hZ, this])
  refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.B (slot p.w aOne) ∧ t.gpr .x7 = 0 ∧
      t.mem = s.mem) (by
    brun [h0, hdr_enc (show sArr aOne < 32 by decide), hl, hH.harr aOne (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h8, h7, hm⟩, k⟩ => ⟨⟨mi, hm ▸ hH, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, hZ,
      (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13⟩, h8, h7⟩


/-! ## The result -/

/-- The public data of the result: the working space, the length `k` and `out`. -/
structure OPub where
  L : Lay
  k : Nat
  op : Addr

/-- `outPhase_ok`'s hypotheses. -/
def OPre (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Good s p.L.B p.L.Z p.L.w p.L.minv ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧ 1 ≤ p.k ∧
    p.k < 2 ^ 31 ∧ word s.mem p.L.B (8 * sOut) = p.op ∧ word s.mem p.L.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.L.B (8 * sMask) = mask c ∧ (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- Before `storeBE`. -/
def O1 (p : OPub) (s : State) : Prop :=
  ∃ c : Bool, Scr s p.L.B p.L.Z ∧ s.gpr .x0 = p.L.B ∧ p.L.w = (p.k + 7) / 8 ∧ slot p.L.w 8 ≤ p.L.Z ∧
    1 ≤ p.k ∧ p.k < 2 ^ 31 ∧ s.gpr .x8 = off p.L.B (slot p.L.w aY) ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 p.k ∧
    s.gpr .x9 = BitVec.ofNat 64 p.k ∧ s.gpr .x15 = mask c ∧
    (∀ j < p.k, InRegions s.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ j < p.k, p.L.Z ≤ ofs p.L.B (p.op + BitVec.ofNat 64 j))

/-- The result's store leaks the same in runs with the same working space,
length and `out`. -/
theorem out_ct : RelCT isa (Two OPre) (seqs outSteps) fun _ _ => True := by
  unfold outSteps
  refine RelCT.seq (two_piece (Ψ := O1) [.x0] (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x0, h₂.x0]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hg, hw, hZ, hk1, hk, hO, hK, hM, hout, hsep⟩
    have hn := hg.scr.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.L.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi => hg.scr.ld (by omega_using [hZ, g0, g8, hi])
    refine WP.mono (WP.keep [.x1, .x8, .x9, .x15] (Q := fun t =>
        t.gpr .x8 = off p.L.B (slot p.L.w aY) ∧ t.gpr .x1 = p.op + BitVec.ofNat 64 p.k ∧
        t.gpr .x9 = BitVec.ofNat 64 p.k ∧ t.gpr .x15 = mask c ∧ t.mem = s.mem) (by
      brun [hg.x0, hdr_enc (show sArr aY < 32 by decide), hdr_enc (show sOut < 32 by decide),
        hdr_enc (show sK < 32 by decide), hdr_enc (show sMask < 32 by decide),
        hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
        hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h8, h1, h9, h15, hm⟩, k⟩ => ⟨c, hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, hw, hZ,
        hk1, hk, h8, h1, h9, h15, fun j hj => by rw [k.wr]; exact hout j hj, hsep⟩
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x0 = p.L.B) [.x8, .x1, .x9]
    (fun p s₁ s₂ ⟨_, _, _, _, _, _, _, a₁, b₁, c₁, _⟩ ⟨_, _, _, _, _, _, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro p s ⟨c, hs, h0, hw, hZ, hk1, hk, h8, h1, h9, h15, hout, hsep⟩
    exact WP.mono (storeBE_ok hs h8 h1 h9 h15 hk1 hk hw
      (by have := slot_le (w := p.L.w) (show aY < 8 by decide); omega_using [hZ, this]) hout hsep)
      fun t ⟨_, _, _, _, k⟩ => (k.gpr .x0 (by decide)).trans h0
  exact two_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## `rest` -/

/-- The public data of `rest`: the working space, `k`, the pointers, `e`
and the values `N` and `R` in the arrays. -/
structure DPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  ep : Addr
  ip : Addr
  len : Nat
  eb : List Byte
  N : Nat
  R : Nat

/-- `pdRest_ok`'s hypotheses. -/
def DRel (p : DPub) (s : State) : Prop :=
  ∃ xb, PdPre s p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R

/-- From `σ`, at `rest`'s start, to `t`: what changed, and the mask. -/
def DG (p : DPub) (xb : List Byte) (σ t : State) : Prop :=
  PdPre σ p.B p.Z p.k p.op p.ep p.ip p.len p.eb xb p.N p.R ∧ Frm p.B (pdAll ((p.k + 7) / 8)) σ.mem t.mem ∧
    Keep mmRegs σ t ∧ word t.mem p.B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < p.N))

theorem PdPre.mem {s t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte}
    {N R : Nat} (h : PdPre s B Z k op ep ip L eb xb N R) (hm : t.mem = s.mem) {regs : List Reg} (kp : Keep regs s t)
    (hr : .x0 ∉ regs) : PdPre t B Z k op ep ip L eb xb N R :=
  { scr := h.scr.congr kp.wr, x0 := (kp.gpr .x0 hr).trans h.x0, z := h.z, k1 := h.k1, k2 := h.k2,
    hO := hm ▸ h.hO, hK := hm ▸ h.hK, hE := hm ▸ h.hE, hL := hm ▸ h.hL, hIn := hm ▸ h.hIn, hW := hm ▸ h.hW,
    hb := hm ▸ h.hb, n := hm ▸ h.n, r := hm ▸ h.r, odd := h.odd, n1 := h.n1, rlt := h.rlt,
    x := h.x.congrK (by rw [hm]; exact InScr.refl _ _ _) kp, e := h.e.congrK (by rw [hm]; exact InScr.refl _ _ _) kp,
    xl := h.xl, el := h.el, L1 := h.L1, L2 := h.L2, out := fun j hj => by rw [kp.wr]; exact h.out j hj,
    outSep := h.outSep }

theorem DG.step {p : DPub} {xb : List Byte} {σ t t' : State} (h : DG p xb σ t)
    (hf : Frm p.B (pdAll ((p.k + 7) / 8)) t.mem t'.mem) (k : Keep mmRegs t t')
    (hm : word t'.mem p.B (8 * sMask) = word t.mem p.B (8 * sMask)) : DG p xb σ t' :=
  ⟨h.1, h.2.1.trans hf, (h.2.2.1.trans k).mono (by decide), hm.trans h.2.2.2⟩

theorem DG.fixed {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : Fixed p.B σ.mem t.mem :=
  Fixed.of_frm h.2.1 (pdAll_fixed _)

theorem DG.inScr {p : DPub} {xb : List Byte} {σ t : State} (h : DG p xb σ t) : InScr p.B p.Z σ.mem t.mem :=
  InScr.of_frm h.2.1 fun r hr => (pdAll_le _ r hr).trans h.1.z

/-- After the input's registers. -/
def DIn (p : DPub) (s : State) : Prop :=
  DRel p s ∧ s.gpr .x1 = p.ip ∧ s.gpr .x2 = BitVec.ofNat 64 p.k ∧ s.gpr .x8 = off p.B (slot ((p.k + 7) / 8) aX)

/-- The input's steps. -/
def pdInSteps : List (Prog isa) := [.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadBE]

/-- The input leaks the same in runs with the same public data. -/
theorem pdIn_ct : RelCT isa (Two DRel) (seqs pdInSteps) (Two fun (p : DPub) s => SR ⟨p.B, p.Z, ((p.k + 7) / 8)⟩ s) := by
  unfold pdInSteps
  refine RelCT.seq (two_piece (Ψ := DIn) [.x0] (fun p s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.x0, h₂.x0]) (by taint_decide) ?_) ?_
  · rintro p s ⟨xb, h⟩
    have hn := h.scr.nowrap
    have hZ := h.z
    obtain ⟨g0, g8⟩ := slot0_ge ((p.k + 7) / 8)
    have eK : sK = 18 := rfl
    have eIn : sIn = 21 := rfl
    have eAX : sArr aX = 9 := rfl
    refine WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = p.ip ∧
        t.gpr .x2 = BitVec.ofNat 64 p.k ∧ t.gpr .x8 = off p.B (slot ((p.k + 7) / 8) aX) ∧ t.mem = s.mem) (by
      brun [h.x0, hdr_enc (show sIn < 32 by decide), hdr_enc (show sK < 32 by decide),
        hdr_enc (show sArr aX < 32 by decide), h.scr.ld (d := 8 * sIn) (by omega_using [hZ, g0, g8, eIn]),
        h.scr.ld (d := 8 * sK) (by omega_using [hZ, g0, g8, eK]),
            h.scr.ld (d := 8 * sArr aX) (by omega_using [hZ, g0, g8, eAX]), h.hIn, h.hK,
        h.hb aX (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h1, h2, h8, hm⟩, k⟩ => ⟨⟨xb, h.mem hm k (by decide)⟩, h1, h2, h8⟩
  rw [seqs_one]
  refine two_piece [.x0, .x1, .x2, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨⟨_, a₁⟩, b₁, c₁, d₁⟩ := h₁
    obtain ⟨⟨_, a₂⟩, b₂, c₂, d₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.x0, a₂.x0]
    · rw [b₁, b₂]
    · rw [c₁, c₂]
    · rw [d₁, d₂]) (by taint_decide) ?_
  rintro p s ⟨⟨xb, h⟩, h1, h2, h8⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hn := h.scr.nowrap
  have hZ := h.z
  have hn' : p.B.toNat + slot ((p.k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hn, hZ]
  refine WP.mono (loadArr_ok h.scr (by decide) hZ h.x h.xl (by omega_using [hk1]) (by omega_using [hk2]) h1 h2 h8) fun t ⟨_, ha, k⟩ =>
    ⟨h.scr.congr k.wr, (k.gpr .x0 (by decide)).trans h.x0, hZ, show 2 ≤ (p.k + 7) / 8 by omega_using [hk1],
      show (p.k + 7) / 8 < 2 ^ 31 by omega_using [hk2], by rw [ha.hslot (by decide)]; exact h.hW,
      fun j hj => by rw [ha.hslot (by unfold sArr; omega_using [hj])]; exact h.hb j hj, ?_⟩
  rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hk1]),
    ← wv_mod64 _ _ _ (show 1 ≤ (p.k + 7) / 8 by omega_using [hk1]), Nat.mod_mod_of_dvd _ (by decide), h.n, h.odd]

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem so_minv {t t' : State} {B : Addr} {Z w : Nat} {mi mi' : BitVec 64} {N X X' : Nat}
    (h : SetupOut t B Z w mi N X) (h' : SetupOut t' B Z w mi' N X') (hodd : N % 2 = 1) (hw : 1 ≤ w) :
    mi = mi' := by
  have e : ∀ {t : State} {mi : BitVec 64} {X : Nat}, SetupOut t B Z w mi N X →
      (word t.mem B (slot w aN)).toNat = N % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ hw, h.n]
  have i := h.inv
  have i' := h'.inv
  rw [e h] at i
  rw [e h'] at i'
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) i i'

/-- After the setup, for `-m⁻¹ = q.2`. -/
def DA (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ SetupOut t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N (Spec.Rsa.os2ip xb) ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aR2) ((q.1.k + 7) / 8) = q.1.R

/-- The setup leaks the same in runs with the same public data. -/
theorem pdSetup_ct : RelCT isa (Two DRel) (seqs (pdInSteps ++ setupSteps)) (Two DA) := by
  refine two_post (Ψ := fun p t => ∃ mi, DA (p, mi) t)
    (RelCT.seqs_append (by simp [pdInSteps]) (by simp [setupSteps]) (RelCT.seq pdIn_ct
      (two_map (fun p : DPub => (⟨p.B, p.Z, ((p.k + 7) / 8)⟩ : RPub)) (fun _ _ h => h) setupRest_ct))) ?_ |>.mono
      (fun _ _ h => h) fun _ _ h => two_bind (fun p t₁ t₂ H₁ H₂ => ?_) h
  · rintro p s ⟨xb, h⟩
    exact WP.mono (pdSetupAll_ok h) fun t ⟨mi, so, f, k, hR⟩ => ⟨mi, xb, s, ⟨h, f, k, so.mask⟩, so, hR⟩
  · obtain ⟨mi₁, h₁⟩ := H₁
    obtain ⟨mi₂, h₂⟩ := H₂
    have ⟨xb₁, σ₁, g₁, so₁, _⟩ := h₁
    have ⟨xb₂, σ₂, g₂, so₂, _⟩ := h₂
    have : 64 ≤ p.k := g₁.1.k1
    obtain rfl := so_minv so₁ so₂ g₁.1.odd (show 1 ≤ ((p.k + 7) / 8) by omega_using [this])
    exact ⟨(p, mi₁), h₁, h₂⟩

/-- `rest`'s public data with `-m⁻¹`. -/
abbrev DPub.L (q : DPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, ((q.1.k + 7) / 8), q.2⟩

/-- After `X := input R`. -/
def DB (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aN) ((q.1.k + 7) / 8) = q.1.N ∧
    ((word t.mem q.1.B (slot ((q.1.k + 7) / 8) aN)).toNat * q.2.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8) < q.1.N ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem arrays_pdAll {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [aAcc, aTmp, aXm] m m') :
    Frm B (pdAll w) m m' :=
  Frm.of_arrays h (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])

/-- `X := input R` leaks the same in runs with the same public data. -/
theorem pdMm_ct : RelCT isa (Two DA) (M.mm aXm aX aR2) (Two DB) := by
  refine two_post (two_map DPub.L (fun _ _ ⟨_, σ, g, so, _⟩ => ⟨so.good, g.1.z⟩)
    (M.ctL (by unfold MmUse; decide))) ?_
  rintro q t ⟨xb, σ, g, so, hR⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hn : q.1.B.toNat + slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega_arith
  refine WP.mono (M.mm_ok (o := aXm) (a := aX) (b := aR2) so.good g.1.z (by omega_using [hk1]) (by omega_using [hk2]) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) so.inv
    (by rw [hR, so.n]; exact g.1.rlt)) fun t' ⟨hg, hlt, _, ha, k⟩ =>
    ⟨xb, σ, g.step (arrays_pdAll ha) k (ha.hslot (by decide)), hg, ?_, ?_, ?_, ?_⟩
  · rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact so.n
  · rw [ha.word0_of_not_mem (by decide) (by decide) hn (by omega_using [hk1])]; exact so.inv
  · rw [so.n] at hlt; exact hlt
  · rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact so.one

/-- The exponentiation's public data. -/
def DPub.E (q : DPub × BitVec 64) : EPub := ⟨DPub.L q, q.1.N, q.1.ep, q.1.len, q.1.eb⟩

theorem src_esrc {a : EPub} {s : State} (h : Src s a.L.B a.L.Z a.ep a.eb) (hl : a.eb.length = a.len)
    (hl' : a.len < 2 ^ 31) : ESrc a s :=
  ⟨hl, hl', fun i hi => h.rd i (by omega_using [hl, hi]), fun i hi => by
    rw [h.val i (by omega_using [hl, hi])]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by omega_using [hl, hi]],
    fun i hi => h.out i (by omega_using [hl, hi])⟩

theorem db_pre {q : DPub × BitVec 64} {t : State} (h : DB q t) : PExpPre (DPub.E q) t := by
  obtain ⟨xb, σ, g, hg, hn, hinv, hlt, -⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hL2 := g.1.L2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  obtain ⟨x, hx⟩ := exists_mont hR g.1.n1 (wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aXm) ((q.1.k + 7) / 8))
  have he := g.1.e.congrK g.inScr g.2.2.1
  exact ⟨_, x, ⟨hg, hn, hinv, rfl⟩, ⟨g.1.z, show 2 ≤ ((q.1.k + 7) / 8) by omega_using [hk1],
    show ((q.1.k + 7) / 8) < 2 ^ 31 by omega_using [hk2], hR, hlt, hx⟩,
    (g.fixed sE (by decide)).trans g.1.hE, (g.fixed sElen (by decide)).trans g.1.hL, g.1.L1,
    src_esrc he g.1.el (show q.1.len < 2 ^ 31 by omega_using [hk2, hL2])⟩

/-- After the exponentiation. -/
def DC (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ X x, DG q.1 xb σ t ∧ ExpCtx t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2 q.1.N X ∧
    YSt t.mem q.1.B ((q.1.k + 7) / 8) q.1.N x (Spec.Rsa.os2ip q.1.eb) ∧
    wv t.mem q.1.B (slot ((q.1.k + 7) / 8) aOne) ((q.1.k + 7) / 8) = 1

theorem pExpRanges_pdAll (w : Nat) : ∀ r ∈ pExpRanges w, r ∈ pdAll w :=
  fun _ hr => List.mem_append_right _ hr

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pdExp_ct : RelCT isa (Two DB) (Precomputed.expLoop M.mm) (Two DC) := by
  refine two_post ((two_map DPub.E (fun _ _ h => db_pre h) pExpLoop_ct).mono (fun _ _ h => h)
    fun _ _ _ => trivial) ?_
  rintro q t h
  obtain ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩ := db_pre h
  obtain ⟨xb, σ, g, -, -, -, -, hone⟩ := h
  have hn : q.1.B.toNat + slot ((q.1.k + 7) / 8) 8 ≤ 2 ^ 64 := by have := g.1.scr.nowrap; have := g.1.z; omega_arith
  refine WP.mono (pExpLoop_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 he hlen hsrc.1 hL1
    hsrc.2.1 hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2) fun t' ⟨hc', hy, f₀, k⟩ => ?_
  have f : Frm q.1.B (pExpRanges ((q.1.k + 7) / 8)) t.mem t'.mem := f₀
  refine ⟨xb, σ, X, x, g.step (f.mono (pExpRanges_pdAll _)) k
      (f.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega_using [])), hc', hy, ?_⟩
  rw [f.wv_eq (fun r hr => by
      have := hdr_lt_slot ((q.1.k + 7) / 8) aOne (show 31 < 32 by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aAcc by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aTmp by decide)
      have := slot_sep (w := ((q.1.k + 7) / 8)) (show aOne ≠ aY by decide)
      simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sI, sV, sBit, sStarted, sFn] at * <;> omega_arith)
      (by have := slot_le (w := ((q.1.k + 7) / 8)) (show aOne < 8 by decide); omega_using [hn, this])]
  exact hone

/-- After `finish`. -/
def DD (q : DPub × BitVec 64) (t : State) : Prop :=
  ∃ xb σ, DG q.1 xb σ t ∧ Good t q.1.B q.1.Z ((q.1.k + 7) / 8) q.2

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem pdFinish_ct : RelCT isa (Two DC) (Precomputed.finish M.mm) (Two DD) := by
  refine two_post (two_map (fun q => (⟨DPub.L q, q.1.N, Spec.Rsa.os2ip q.1.eb⟩ : FPub))
    (fun q _ ⟨_, _, X, x, g, hc, hy, _⟩ => ⟨X, x, hc, hy, g.1.z, show 2 ≤ (q.1.k + 7) / 8 by have := g.1.k1; omega_using [this],
      show (q.1.k + 7) / 8 < 2 ^ 31 by have := g.1.k2; omega_using [this]⟩) finish_ct) ?_
  rintro q t ⟨xb, σ, X, x, g, hc, hy, hone⟩
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  have hR := VG.Proof.Bignum.coprime_pow2 g.1.odd (64 * ((q.1.k + 7) / 8))
  refine WP.mono (pFinish_ok hc g.1.z (by omega_using [hk1]) (by omega_using [hk2]) hR g.1.n1 hone hy)
    fun t' ⟨hg, _, f, k⟩ => ⟨xb, σ, g.step (f.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])) k
      (f.word_eq (fun r hr => by
        have := hdr_lt_slot ((q.1.k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((q.1.k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega_arith) (by unfold sMask sFn; omega_using [])), hg⟩

theorem dd_oPre {q : DPub × BitVec 64} {t : State} (h : DD q t) : OPre ⟨DPub.L q, q.1.k, q.1.op⟩ t := by
  obtain ⟨xb, σ, g, hg⟩ := h
  have hk1 := g.1.k1
  have hk2 := g.1.k2
  exact ⟨_, hg, rfl, g.1.z, show 1 ≤ q.1.k by omega_using [hk1], show q.1.k < 2 ^ 31 by omega_using [hk2],
    by rw [g.fixed sOut (by decide)]; exact g.1.hO, by rw [g.fixed sK (by decide)]; exact g.1.hK, g.2.2.2,
    fun j hj => by rw [g.2.2.1.wr]; exact g.1.out j hj, g.1.outSep⟩

/-- `rest` leaks the same in runs with the same public data and `e`. -/
theorem pdRest_ct : RelCT isa (Two DRel) (Precomputed.rest M.mm) fun _ _ => True := by
  rw [pdRest_eq]
  refine RelCT.seqs_append (by simp) (by simp [pdExp]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [pdExp]) (by simp [outSteps]) (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (RelCT.seq pdExp_ct pdFinish_ct)
  · exact two_map (fun q => (⟨DPub.L q, q.1.k, q.1.op⟩ : OPub)) (fun _ _ h => dd_oPre h) out_ct

end VG.Proof.Bignum.AArch64
