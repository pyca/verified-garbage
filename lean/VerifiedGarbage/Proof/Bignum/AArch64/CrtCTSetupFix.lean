import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad

/-!
# RSA with the CRT on AArch64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop runs from the array's base and `w_X`, the low word's fix from
the array's base, and `-X⁻¹` and the number 1 from `x0`. What each piece
keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `minv` changes only its registers, whatever `x3`. -/
theorem minv_keep (s : State) :
    WP isa (.block VG.Impl.Bignum.AArch64.minv) s fun t => Keep [.x4, .x5, .x6, .x15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.x4, .x5, .x6, .x15] (Q := fun t => t.mem = s.mem)
    (by brun [VG.Impl.Bignum.AArch64.minv, newton]) (by decide) (by decide) (by decide +kernel))
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-- The low word's fix: its base, then the fix. -/
def fixA : List Instr :=
  [movi .x4 3, .logic .and .x .x5 .x15 .x4, .logic .eor .x .x5 .x5 .x4, ldh .x16 (sArr Public.aN)]

def fixB : List Instr := [ld .x3 .x16, .logic .orr .x .x3 .x3 .x5, st .x3 .x16]

theorem fixLow_eq : fixLow = fixA ++ fixB := rfl

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ word t.mem (off B o) (8 * sMaskX) = mask c ∧
      Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ Keep [.x5] s t := by
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * sMaskX) (mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega) k.wr
    (k.gpr .x0 (by decide)), by rw [hm]; exact word_writeW_self _ _ _ _, f₁, k⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : word s.mem (off B o) (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (maskArr_ok hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨_, _, ho, _, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

theorem pfA_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv) :
    WP isa (.block fixA) s fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem ∧
      Keep [.x4, .x5, .x16] s t :=
  WP.mono (WP.keep [.x4, .x5, .x16] (Q := fun t => t.gpr .x16 = off B (o + slot wx Public.aN) ∧ t.mem = s.mem)
    (by brun [fixA, hc.x0, hdr_enc (sArr_lt (show Public.aN < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aN < 8 by decide)), hc.harr' (show Public.aN < 8 by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, hm⟩, k⟩ => ⟨h16, hm, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (off (off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx v := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have h8x := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hh : ∀ k < 32, k ≠ sMinv → word t.mem (off B o) (8 * k) = word s.mem (off B o) (8 * k) := fun k hk hne => by
    rw [hm]; exact hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hne)
  have hb : ∀ k < 32, word t.mem B (8 * k) = word s.mem B (8 * k) := fun k hk => by
    rw [hm, off_off]
    exact (writeW_outside s.mem B (d := o + 8 * sMinv) v (by unfold sMinv; omega)).word
      (Or.inl (by unfold sMinv; omega)) (by omega)
  exact ⟨h.scr.congr hwr, h0.trans h.x0, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega) (by unfold sArr sMinv; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (h16 : s.gpr .x16 = off B (o + slot wx Public.aN)) :
    WP isa (.block (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) ∧ t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : o + slot wx Public.aN + 8 ≤ Z := by omega
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (c := .block fixB) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (off B (o + slot wx Public.aN)) v) (by
    brun [fixB, h16, hc.scr.ld hd, hc.scr.st hd]; exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  rw [← off_off] at hm₁
  have o₁ := writeW_outside s.mem (off B o) (d := slot wx Public.aN) v (by omega)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k₁.wr
    (k₁.gpr .x0 (by decide))
  refine WP.mono (minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  have hW : ∀ v : BitVec 64, word (s₂.mem.writeW (off B (o + 8 * sMinv)) v) B (o + 8 * sW) =
      BitVec.ofNat 64 wx := fun v => by
    rw [← off_off, ← word_off, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hc₂.hdr.hw
  refine WP.mono (WP.keep [.x9, .x12, .x13] (c := .block fixTail) (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 wx ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem.writeW (off (off B o) (8 * sMinv)) (s₂.gpr .x15)) (by
    rw [off_off]
    brun [fixTail, hc₂.x0, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hc₂.st' (show sMinv < 32 by decide), hc₂.ld' (show sW < 32 by decide), hW])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h12, h13, hm₃⟩, k₃⟩ => ?_
  have o₃ := writeW_outside s₂.mem (off B o) (d := 8 * sMinv) (s₂.gpr .x15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, word_writeW_self]) k₃.wr (k₃.gpr .x0 (by decide)), h12, h13, ?_,
    K.mono (by decide)⟩
  rw [hm₂] at f₃
  exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .x12 = BitVec.ofNat 64 wx)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.x0 hc.hdr (Nat.le_refl _) h12 hw' (o := Public.aOne) (by decide)
    (i := 0) (by omega) h13) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.wr
    (k.gpr .x0 (by decide)), f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_eq' : primeFix = ([.block fixMask] : List (Prog isa)) ++ (maskArr Public.aN ++
    ([.block (fixA ++ (fixB ++ VG.Impl.Bignum.AArch64.minv ++ fixTail)), setWord Public.aOne] : List (Prog isa))) := by
  rw [primeFix_eq, fixLow_eq]; simp only [List.append_assoc]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (off B o) (pfRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [primeFix_eq']
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pfA_ok hc₂) fun s₃ ⟨h16, hm₃, k₃⟩ => ?_
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  refine WP.mono (pf3_ok hc₃ h16) fun s₄ ⟨hc₄, h12₄, h13₄, f₄, k₄⟩ => ?_
  refine WP.mono (pf4_ok hc₄ hw hw' h12₄ h13₄) fun t ⟨hc₅, f₅, k₅⟩ => ⟨_, hc₅, ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  rw [hm₃] at f₄
  exact (((f₁.append f₂).append f₄).append f₅).mono fun r hr => by
    simp only [pfRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp [h]

/-! ## Constant time -/

/-- `primeFix`'s hypotheses: a prime's workspace (some `-X⁻¹`), and the
modulus' mask (some value). -/
def PF (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem p.B (8 * Public.sMask) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the mask's load. -/
def PF1 (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (c : Bool), SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    word s.mem (off p.B p.o) (8 * sMaskX) = mask c ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the masking. -/
def PF2 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 31

/-- After the low word's base. -/
def PFA (p : XPub) (s : State) : Prop := PF2 p s ∧ s.gpr .x16 = off p.B (p.o + slot p.wx Public.aN)

/-- After `-X⁻¹`. -/
def PF3 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : XPub) (s : State) : Prop :=
  s.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne) ∧ s.gpr .x12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .x13 = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([ldh .x5 sLink] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => PF p t ∧ t.gpr .x5 = p.B) [.x0]
      (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x0, .x5] (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, h5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.B ∧ t.mem = s.mem)
    (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h5, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, h5⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq']
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := PF1) fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := PF2)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (pf2_ok hc (by omega) h2 hm) fun t ⟨hc', _⟩ =>
      ⟨minv, hc', h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_piece (Ψ := PFA) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide)
    fun p s h => by
      obtain ⟨minv, hc, h1, h2⟩ := h
      exact WP.mono (pfA_ok hc) fun t ⟨h16, hm, k⟩ => ⟨⟨minv, hc.mem hm k (by decide), h1, h2⟩, h16⟩)
    (two_piece (Ψ := PF3) [.x0, .x16]
      (pins_of (fun (p : XPub) r => if r = .x0 then off p.B p.o else off p.B (p.o + slot p.wx Public.aN))
        fun p s ⟨⟨_, hc, _⟩, h16⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hc.x0
          · exact h16) (by taint_decide)
      fun p s ⟨⟨_, hc, _⟩, h16⟩ => WP.mono (pf3_ok hc h16) fun t ⟨hc', h12', h13, _⟩ =>
        ⟨_, hc', h12', h13⟩))) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := PF4) [.x0]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.x0) (by taint_decide) ?_)
    (two_taint [.x8, .x12, .x13] (pins_of (fun (p : XPub) r => if r = .x8 then
      off p.B (p.o + slot p.wx Public.aOne) else if r = .x12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, h13⟩
  exact WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off p.B (p.o + slot p.wx Public.aOne))
    (by brun [hc.x0, hdr_enc (sArr_lt (show Public.aOne < 8 by decide)),
      hc.ld' (sArr_lt (show Public.aOne < 8 by decide)), hc.harr' (show Public.aOne < 8 by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13⟩

end VG.Proof.Bignum.AArch64
