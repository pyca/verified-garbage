import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# RSA with the CRT on x86-64: constant time of a prime's fixes

`primeFix` in a prime's workspace (`primeFix_ct`): the mask's load reads
`n`'s header through the workspace's link, pinned by correctness; the
masking loop, the low word's fix, `-X⁻¹` and the number 1 then run from
registers that correctness pins (the array's base and `w_X`). What each
piece keeps and changes (`pf1_ok` to `pf4_ok`) gives `primeFix_frm`, what
`primeFix` changes whatever the mask and the prime.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `minv` changes only its registers, whatever `rbx`. -/
theorem minv_keep (s : State) :
    WP isa (.block minv) s fun t => Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem :=
  WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi, .r15] (Q := fun t => t.mem = s.mem) (by unfold minv newton; simp only [List.cons_append, List.nil_append]; xrun) rfl)
    fun _ ⟨h, k⟩ => ⟨k, h⟩

/-! ## The pieces' correctness -/

theorem pf1_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block fixMask) s fun t => SubCtx t B Z o w wx minv ∧ word t.mem (off B o) (8 * sMaskX) = mask c ∧
      Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem ∧ Keep [.rax] s t := by
  have h8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine WP.mono (fixMask_ok hc hM) fun t ⟨hm, k⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := 8 * sMaskX) (mask c) (by decide)
  rw [← hm] at o₁
  have f₁ : Frm (off B o) [(8 * sMaskX, 8)] s.mem t.mem := Frm.of_outside o₁ (by simp)
  exact ⟨hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; unfold sMaskX sFn; omega) k.2.2
    (k.gpr (by decide)), by rw [hm]; exact word_writeW_self _ _ _ _, f₁, k⟩

/-- `maskArr_ok`, with the registers it leaves. -/
theorem maskArr_regs {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : word s.mem B (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr j)) s fun t => Outside B (slot w j) (8 * w) s.mem t.mem ∧
      t.gpr .rbx = off B (slot w j) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sj := (slot_le (w := w) hj).trans hZ
  unfold maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sMaskX (by decide),
      hl (sArr j) (by unfold sArr; omega), hl sW (by decide), hm, hg.hdr.harr j hj,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      MaskInv s₁ B Z (slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (MaskInv s₁ B Z (slot w j) c) h0
    (fun i _ hi t hI => maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun t hI => ?_
  have ho := hI.out
  rw [hm₁] at ho
  exact ⟨ho, (hI.keep.gpr (by decide)).trans hbx, (hI.keep.gpr (by decide)).trans h12,
    (k₁.trans hI.keep).mono (by decide)⟩

theorem pf2_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31)
    (hm : word s.mem (off B o) (8 * sMaskX) = mask c) :
    WP isa (seqs (maskArr Public.aN)) s fun t => SubCtx t B Z o w wx minv ∧
      t.gpr .rbx = off (off B o) (slot wx Public.aN) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  refine WP.mono (maskArr_regs hc.good (Nat.le_refl _) hw hw' (by decide) hm) fun t ⟨ho, hbx, h12, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.2.2 (k.gpr (by decide)),
    hbx, h12, f, k⟩

/-- A prime's workspace context after a store of its `-X⁻¹`. -/
theorem SubCtx.setMinv {s t : State} {B : Addr} {Z o w wx : Nat} {minv v : BitVec 64}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem.writeW (off (off B o) (8 * sMinv)) v)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx v := by
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
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi, ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw,
    by rw [hm]; exact word_writeW_self _ _ _ _,
    fun j hj => (hh _ (by unfold sArr; omega) (by unfold sArr sMinv; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), hlo, hi⟩

theorem pf3_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w wx mi) (hbx : s.gpr .rbx = off (off B o) (slot wx Public.aN))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wx) :
    WP isa (.block (fixLow ++ VG.Impl.Bignum.X86_64.minv ++ fixTail)) s fun t =>
      SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  have h0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aN < 8 by decide)
  have hd : slot wx Public.aN + 8 ≤ slot wx 8 := by omega
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbx] (c := .block fixLow) (Q := fun t =>
      ∃ v : BitVec 64, t.mem = s.mem.writeW (off (off B o) (slot wx Public.aN)) v) (by
    unfold fixLow
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hg.scr.ld hd,
      hg.scr.st hd]
    exact ⟨_, rfl⟩) rfl) fun s₁ ⟨⟨v, hm₁⟩, k₁⟩ => ?_
  have o₁ := writeW_outside s.mem (off B o) (d := slot wx Public.aN) v (by omega)
  rw [← hm₁] at o₁
  have f₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem :=
    Frm.of_outside (o₁.mono (o' := slot wx Public.aN) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)) (by simp)
  have hc₁ := hc.of_frm f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k₁.2.2
    (k₁.gpr (by decide))
  refine WP.mono (minv_keep s₁) fun s₂ ⟨k₂, hm₂⟩ => ?_
  have hc₂ := hc₁.mem hm₂ k₂ (by decide)
  have hs₂ := hc₂.good.scr
  refine WP.mono (WP.keep [.rdx, .rcx] (c := .block fixTail) (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = s₂.mem.writeW (off (off B o) (8 * sMinv)) (s₂.gpr .r15)) (by
    unfold fixTail
    xrun [State.ea, hdr, hc₂.rdi, hdrOff, hs₂.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t ⟨⟨hcx, hm₃⟩, k₃⟩ => ?_
  have o₃ := writeW_outside s₂.mem (off B o) (d := 8 * sMinv) (s₂.gpr .r15) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm (off B o) [(8 * sMinv, 8)] s₂.mem t.mem := Frm.of_outside o₃ (by simp)
  have K := (k₁.trans k₂).trans k₃
  refine ⟨hc₂.setMinv (by rw [hm₃, word_writeW_self]) k₃.2.2 (k₃.gpr (by decide)), ?_, hcx, ?_,
    K.mono (by decide)⟩
  · exact ((k₂.trans k₃).gpr (by decide)).trans ((k₁.gpr (by decide)).trans h12)
  · rw [hm₂] at f₃
    exact (f₁.append f₃).mono fun r hr => by simpa using hr

theorem pf4_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw : 1 ≤ wx) (hw' : wx < 2 ^ 31) (h12 : s.gpr .r12 = BitVec.ofNat 64 wx)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (setWord Public.aOne .rcx) s fun t => SubCtx t B Z o w wx minv ∧
      Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem ∧ Keep [.rax, .r8, .r14] s t := by
  have h0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have h1 := slot_le (w := wx) (show Public.aOne < 8 by decide)
  refine WP.mono (setWord_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) h12 hw hw' (o := Public.aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t ⟨_, ho, k⟩ => ?_
  have f : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s.mem t.mem := Frm.of_outside ho (by simp)
  exact ⟨hc.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) k.2.2 (k.gpr (by decide)),
    f, k⟩

/-- What `primeFix` changes, whatever the mask and the prime. -/
def pfRanges (wx : Nat) : List (Nat × Nat) :=
  [(8 * sMaskX, 8), (slot wx Public.aN, 8 * (wx + 2)), (8 * sMinv, 8), (slot wx Public.aOne, 8 * (wx + 2))]

theorem primeFix_frm {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {c : Bool}
    (hc : SubCtx s B Z o w wx minv) (hM : word s.mem B (8 * Public.sMask) = mask c) (hw : 1 ≤ wx)
    (hw' : wx < 2 ^ 31) :
    WP isa (seqs primeFix) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      Frm (off B o) (pfRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [maskArr]) ?_
  refine WP.mono (pf1_ok hc hM) fun s₁ ⟨hc₁, hm₁, f₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp [maskArr]) (by simp) ?_
  refine WP.mono (pf2_ok hc₁ hw hw' hm₁) fun s₂ ⟨hc₂, hbx₂, h12₂, f₂, k₂⟩ => ?_
  simp only [seqs]
  refine WP.seq (WP.mono (pf3_ok hc₂ hbx₂ h12₂) fun s₃ ⟨hc₃, h12₃, hcx₃, f₃, k₃⟩ => ?_)
  refine WP.mono (pf4_ok hc₃ hw hw' h12₃ hcx₃) fun t ⟨hc₄, f₄, k₄⟩ => ⟨_, hc₄, ?_,
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  exact (((f₁.append f₂).append f₃).append f₄).mono fun r hr => by
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
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧
    s.gpr .rbx = off (off p.B p.o) (slot p.wx Public.aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 31

/-- After `-X⁻¹`. -/
def PF3 (p : XPub) (s : State) : Prop :=
  ∃ minv : BitVec 64, SubCtx s p.B p.Z p.o p.w p.wx minv ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

/-- `setWord`'s registers. -/
def PF4 (p : XPub) (s : State) : Prop :=
  s.gpr .r8 = off (off p.B p.o) (slot p.wx Public.aOne) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rcx = BitVec.ofNat 64 0

theorem fixMask_ct : RelCT isa (Two PF) (.block fixMask) fun _ _ => True := by
  unfold fixMask
  refine RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => PF p t ∧ t.gpr .rax = p.B) [.rdi]
      (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, _, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.rdi, .rax] (pins_of (fun (p : XPub) r => if r = .rdi then off p.B p.o else p.B)
      fun p s ⟨⟨_, _, hc, _⟩, hax⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hax) (by taint_decide)))
  rintro p s ⟨minv, c, hc, hM, h1, h2⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (off (off p.B p.o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.link]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ⟨⟨minv, c, hc.mem hm k (by decide), hm ▸ hM, h1, h2⟩, hax⟩

/-- `primeFix` is constant time. -/
theorem primeFix_ct : RelCT isa (Two PF) (seqs primeFix) fun _ _ => True := by
  rw [primeFix_eq]
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [maskArr]) (RelCT.seq (two_post (Ψ := PF1) fixMask_ct
    fun p s ⟨minv, c, hc, hM, h1, h2⟩ => WP.mono (pf1_ok hc hM) fun t ⟨hc', hm, _⟩ =>
      ⟨minv, c, hc', hm, h1, h2⟩) ?_)
  refine RelCT.seqs_append (by simp [maskArr]) (by simp) (RelCT.seq (two_post (Ψ := PF2)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (maskArr_ct (by decide) (by taint_decide)))
    fun p s ⟨minv, c, hc, hm, h1, h2⟩ => WP.mono (pf2_ok hc (by omega) h2 hm) fun t ⟨hc', hbx, h12, _⟩ =>
      ⟨minv, hc', hbx, h12, h1, h2⟩) ?_)
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := PF3) [.rdi, .rbx]
    (pins_of (fun (p : XPub) r => if r = .rdi then off p.B p.o else off (off p.B p.o) (slot p.wx Public.aN))
      fun p s ⟨_, hc, hbx, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hbx) (by taint_decide)
    fun p s ⟨_, hc, hbx, h12, _⟩ => WP.mono (pf3_ok hc hbx h12) fun t ⟨hc', h12', hcx, _⟩ =>
      ⟨_, hc', h12', hcx⟩) ?_
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := PF4) [.rdi]
    (pins_of (fun p _ => off p.B p.o) fun p s ⟨_, hc, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (pins_of (fun (p : XPub) r => if r = .r8 then
      off (off p.B p.o) (slot p.wx Public.aOne) else if r = .r12 then BitVec.ofNat 64 p.wx else BitVec.ofNat 64 0)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨_, hc, h12, hcx⟩
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hl₁ : InRegions (s.rd ++ s.wr) (off (off p.B p.o) (8 * sArr Public.aOne)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sArr Public.aOne < 32 by decide); omega)
  exact WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off (off p.B p.o) (slot p.wx Public.aOne))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.hdr.harr Public.aOne (by decide)]) rfl)
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

end VG.Proof.Bignum.X86_64
