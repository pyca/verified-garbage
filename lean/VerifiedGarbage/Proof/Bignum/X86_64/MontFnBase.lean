import VerifiedGarbage.Impl.Bignum.X86_64.MontFn
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl
theorem setXmm_xmm (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl
theorem setReg_xmm (s : State) (d : Reg) (v : BitVec 64) : (s.setReg d v).xmm = s.xmm := rfl

theorem qword_movq (v : BitVec 64) : qword ((0 : BitVec 64) ++ v) 0 = v := by
  ext i hi; simp only [qword, BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hi]

theorem ofNat32_64 {o : Nat} (h : o < 2 ^ 32) : (BitVec.ofNat 32 o).setWidth 64 = BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega

theorem arr_off (B : Addr) {j : Nat} (hj : j < 2 ^ 32) :
    off (B + (BitVec.ofNat 32 j).setWidth 64 * 8#64) (8 * sArr 0) = off B (8 * sArr j) := by
  rw [ofNat32_64 hj]
  simp only [off, sArr, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- `enter` and `basesR`: the bases of the arrays whose indices are in `edx`,
`ecx` and `r8d`, as `bases` gives them, and the callee-saved registers in
`xmm0`–`xmm2`. -/
theorem fnHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block (enter ++ basesR)) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] s t ∧
      t.xmm .xmm0 = s.gpr .rbp ++ s.gpr .rbx ∧ t.xmm .xmm1 = s.gpr .r13 ++ s.gpr .r12 ∧
      t.xmm .xmm2 = s.gpr .r15 ++ s.gpr .r14 := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] (c := .block (enter ++ basesR))
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      t.xmm .xmm0 = s.gpr .rbp ++ s.gpr .rbx ∧ t.xmm .xmm1 = s.gpr .r13 ++ s.gpr .r12 ∧
      t.xmm .xmm2 = s.gpr .r15 ++ s.gpr .r14) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, k, h.2.2.2.2.2.2.2.2.2⟩
  unfold enter basesR
  simp only [List.cons_append, List.nil_append]
  xrun [XOp.exec, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm, setReg_xmm, XBinOp.eval, qword_movq,
    State.ea, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off B (show o < 2 ^ 32 by omega),
    arr_off B (show a < 2 ^ 32 by omega), arr_off B (show b < 2 ^ 32 by omega),
    hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega), hl (sArr b) (by unfold sArr; omega),
    hl (sArr aN) (by decide), hl (sArr aAcc) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr aN (by decide),
    hH.harr aAcc (by decide), hH.harr aTmp (by decide), hH.hw, hH.hminv]

/-! ## Restoring the callee-saved registers -/

theorem fnReadW_writeW128 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j ≤ 8) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 j) 64 = v.extractLsb' (8 * j) 64 := by
  simp only [Mem.readW, Mem.writeW]
  rw [BitVec.setWidth_eq]
  have : (Mem.write m a 16 (BitVec.setWidth (8 * 16) v)).read (a + BitVec.ofNat 64 j) 8 = v.extractLsb' (8 * j) 64 := by
    refine Mem.read_eq_of_bytes fun i hi => ?_
    simp only [Mem.write]
    rw [Offset.add_add, Mem.sub_ofNat_toNat a (by omega)]
    simp only [show j + i < 16 by omega, ite_true]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    simp [show 8 * (j + i) + k < 128 by omega, show 8 * i + k < 64 by omega]
    congr 1; omega
  exact this

theorem fnExtract_lo (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

theorem fnExtract_hi (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  ext i h; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [h]

theorem off_add_ofInt (B : Addr) (d k : Nat) : off B d + BitVec.ofInt 64 (k : Int) = off B (d + k) := by
  rw [BitVec.ofInt_natCast]; simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem word_lo128 (m : Mem) (B : Addr) (d : Nat) (v : BitVec 128) :
    (m.writeW (off B d) v).readW (off B d) 64 = v.extractLsb' 0 64 := by
  simpa using fnReadW_writeW128 m (off B d) v (j := 0) (by decide)

theorem word_hi128 (m : Mem) (B : Addr) (d : Nat) (v : BitVec 128) :
    (m.writeW (off B d) v).readW (off B (d + 8)) 64 = v.extractLsb' 64 64 := by
  rw [show off B (d + 8) = off B d + BitVec.ofNat 64 8 by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact fnReadW_writeW128 m (off B d) v (j := 8) (by decide)

/-- A write of `w` bits changes only those bytes. -/
theorem writeW_outsideN (m : Mem) (base : Addr) {d w : Nat} (v : BitVec w) (h : d + w / 8 ≤ 2 ^ 64)
    (hw : 0 < w / 8) :
    Outside base d (w / 8) m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `leave`: the callee-saved registers from `xmm0`–`xmm2`, through the
first four words of the accumulator and two of the temporary. -/
theorem fnLeave_ok {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (h8 : t.gpr .r8 = off B (slot w aAcc)) (hsi : t.gpr .rsi = off B (slot w aTmp)) :
    WP isa (.block leave) t fun t' =>
      t'.gpr .rbx = (t.xmm .xmm0).extractLsb' 0 64 ∧ t'.gpr .rbp = (t.xmm .xmm0).extractLsb' 64 64 ∧
      t'.gpr .r12 = (t.xmm .xmm1).extractLsb' 0 64 ∧ t'.gpr .r13 = (t.xmm .xmm1).extractLsb' 64 64 ∧
      t'.gpr .r14 = (t.xmm .xmm2).extractLsb' 0 64 ∧ t'.gpr .r15 = (t.xmm .xmm2).extractLsb' 64 64 ∧
      Arrays B w [aAcc, aTmp] t.mem t'.mem ∧ Keep [.rbx, .rbp, .r12, .r13, .r14, .r15] t t' := by
  have hn := hs.nowrap
  have sa := slot_le (w := w) (show aAcc < 8 by decide)
  have st := slot_le (w := w) (show aTmp < 8 by decide)
  have sat : slot w aAcc + 8 * (w + 2) ≤ slot w aTmp := by unfold slot aAcc aTmp; omega
  have hst : ∀ {d n}, d + n ≤ Z → 0 < n → InRegions t.wr (off B d) n := fun {d n} h hn =>
    let ⟨_, hm, hc⟩ := hs.region (d := d) (n := n) (by simpa using h) hn
    ⟨_, hm, by simpa [off] using hc⟩
  have hld : ∀ {d}, d + 8 ≤ Z → InRegions (t.rd ++ t.wr) (off B d) 8 := fun {d} h =>
    let ⟨r, hm, hc⟩ := hst h (by decide); ⟨r, List.mem_append_right _ hm, hc⟩
  have e0 : ∀ d, off B d + BitVec.ofInt 64 0 = off B d := fun d => by simp
  have e8 : ∀ d, off B d + BitVec.ofInt 64 8 = off B (d + 8) := fun d => off_add_ofInt B d 8
  have e16 : ∀ d, off B d + BitVec.ofInt 64 16 = off B (d + 16) := fun d => off_add_ofInt B d 16
  have e24 : ∀ d, off B d + BitVec.ofInt 64 24 = off B (d + 24) := fun d => off_add_ofInt B d 24
  let m₃ := ((t.mem.writeW (off B (slot w aAcc)) (t.xmm .xmm0)).writeW (off B (slot w aAcc + 16))
    (t.xmm .xmm1)).writeW (off B (slot w aTmp)) (t.xmm .xmm2)
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 16 ≤ d → d + 8 ≤ 2 ^ 64 → e + 16 ≤ 2 ^ 64 →
      Mem.Sep (off B d) (64 / 8) (off B e) (128 / 8) := fun h h₁ h₂ => Offset.sep B h h₁ h₂
  have r₀ : m₃.readW (off B (slot w aAcc)) 64 = (t.xmm .xmm0).extractLsb' 0 64 := by
    simp only [m₃]
    rw [Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide), word_lo128]
  have r₁ : m₃.readW (off B (slot w aAcc + 8)) 64 = (t.xmm .xmm0).extractLsb' 64 64 := by
    simp only [m₃]
    rw [Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide), word_hi128]
  have r₂ : m₃.readW (off B (slot w aAcc + 16)) 64 = (t.xmm .xmm1).extractLsb' 0 64 := by
    simp only [m₃]
    rw [Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide), word_lo128]
  have r₃ : m₃.readW (off B (slot w aAcc + 24)) 64 = (t.xmm .xmm1).extractLsb' 64 64 := by
    simp only [m₃]
    rw [Mem.readW_writeW_sep (sep (by omega) (by omega) (by omega)) (by decide),
      show slot w aAcc + 24 = slot w aAcc + 16 + 8 by omega, word_hi128]
  have r₄ : m₃.readW (off B (slot w aTmp)) 64 = (t.xmm .xmm2).extractLsb' 0 64 := word_lo128 _ _ _ _
  have r₅ : m₃.readW (off B (slot w aTmp + 8)) 64 = (t.xmm .xmm2).extractLsb' 64 64 := word_hi128 _ _ _ _
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (c := .block leave)
    (Q := fun t' => t'.gpr .rbx = (t.xmm .xmm0).extractLsb' 0 64 ∧ t'.gpr .rbp = (t.xmm .xmm0).extractLsb' 64 64 ∧
      t'.gpr .r12 = (t.xmm .xmm1).extractLsb' 0 64 ∧ t'.gpr .r13 = (t.xmm .xmm1).extractLsb' 64 64 ∧
      t'.gpr .r14 = (t.xmm .xmm2).extractLsb' 0 64 ∧ t'.gpr .r15 = (t.xmm .xmm2).extractLsb' 64 64 ∧
      t'.mem = m₃) ?_ rfl) fun t' ⟨⟨h1, h2, h3, h4, h5, h6, hm⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, ?_, k⟩
  · unfold leave
    xrun [State.ea, at_, State.store128, h8, hsi, e0, e8, e16, e24,
      hst (d := slot w aAcc) (n := 16) (by omega) (by decide),
      hst (d := slot w aAcc + 16) (n := 16) (by omega) (by decide),
      hst (d := slot w aTmp) (n := 16) (by omega) (by decide), hld (d := slot w aAcc) (by omega),
      hld (d := slot w aAcc + 8) (by omega), hld (d := slot w aAcc + 16) (by omega),
      hld (d := slot w aAcc + 24) (by omega), hld (d := slot w aTmp) (by omega),
      hld (d := slot w aTmp + 8) (by omega)]
    exact ⟨r₀, r₁, r₂, r₃, r₄, r₅, rfl⟩
  · rw [hm]
    have o₁ := writeW_outsideN t.mem B (d := slot w aAcc) (t.xmm .xmm0) (by omega) (by decide)
    have o₂ := writeW_outsideN (t.mem.writeW (off B (slot w aAcc)) (t.xmm .xmm0)) B
      (d := slot w aAcc + 16) (t.xmm .xmm1) (by omega) (by decide)
    have o₃ := writeW_outsideN ((t.mem.writeW (off B (slot w aAcc)) (t.xmm .xmm0)).writeW
      (off B (slot w aAcc + 16)) (t.xmm .xmm1)) B (d := slot w aTmp) (t.xmm .xmm2) (by omega) (by decide)
    refine ((Arrays.of_outside (j := aAcc) (by simp) o₁ (Nat.le_refl _) (by omega)).trans
      (Arrays.of_outside (j := aAcc) (by simp) o₂ (by omega) (by omega))).trans
      (Arrays.of_outside (j := aTmp) (by simp) o₃ (Nat.le_refl _) (by omega))

/-- `vg_rsa_mont_mul`'s code: `[o] = [a] [b] R⁻¹ mod m` for the arrays whose
indices are in `edx`, `ecx` and `r8d`, as `montMul` computes it, changing
only `aAcc`, `aTmp` and `o`; and the callee-saved registers as they were. -/
theorem mulBase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (hb1 : b ≠ aAcc) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, x0, x1, x2⟩ => ?_)
  rw [← hm₁] at hinv hB
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp, .r13, .r14] (WP.vecKeep (by decide) (mmTail_ok hs₁ hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
    (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
    h8₁ h12 h15 hsi₁ hinv hB)) (by decide)) fun s₂ ⟨⟨⟨hlt, heq, har, k₂⟩, hx₂, _⟩, k₂'⟩ => ?_)
  refine WP.mono (fnLeave_ok (hs₁.congr k₂.2.2) hZ hw ((k₂'.gpr (by decide)).trans h8₁) ((k₂'.gpr (by decide)).trans hsi₁))
    fun t ⟨r1, r2, r3, r4, r5, r6, har₂, k₃⟩ => ?_
  have hv : wv t.mem B (slot w o) w = wv s₂.mem B (slot w o) w :=
    har₂.wv_of_not_mem ho (by simp [ho1, ho2]) (by omega)
  rw [hm₁] at hlt heq har
  refine ⟨by rw [hv]; exact hlt, by rw [hv]; exact heq, har.trans (har₂.mono (by simp)),
    ((k₁.trans k₂).trans k₃).mono (by decide), ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [r1, hx₂, x0, fnExtract_lo]
  · rw [r2, hx₂, x0, fnExtract_hi]
  · rw [r3, hx₂, x1, fnExtract_lo]
  · rw [r4, hx₂, x1, fnExtract_hi]
  · rw [r5, hx₂, x2, fnExtract_lo]
  · rw [r6, hx₂, x2, fnExtract_hi]

/-- The indices, as `args` leaves them. -/
theorem fnArgs_ok (s : State) (o a b : Nat) :
    WP isa (.block (args o a b)) s fun t =>
      (t.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o ∧ (t.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a ∧
      (t.gpr .r8).setWidth 32 = BitVec.ofNat 32 b ∧ t.mem = s.mem ∧ Keep [.rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rdx, .rcx, .r8] (c := .block (args o a b))
    (Q := fun t => (t.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o ∧ (t.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a ∧
      (t.gpr .r8).setWidth 32 = BitVec.ofNat 32 b ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold args
  xrun

/-- The call of `vg_rsa_mont_mul`, inlined: what calls of it run as. -/
def mmFnBase (o a b : Nat) : Prog isa := (call "vg_rsa_mont_mul" mulBase o a b).inline

theorem mmFnBase_eq (o a b : Nat) : mmFnBase o a b = .seq (.block (args o a b)) mulBase := rfl

theorem mmFnBase_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (h₁ : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ basesR))) hc₁).isSome = true)
    (h₂ : (taint.check (Taint.ofRegs [.rbx, .r11, .r9, .r10, .r8, .r12, .rsi])
      (.seq (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc))) (.block leave)) hc₂).isSome = true) :
    RelCT isa (Two GoodW) (mmFnBase o a b) fun _ _ => True := by
  rw [mmFnBase_eq]
  unfold mulBase
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := BasesL aN aAcc aTmp o a b) [.rdi] pins_goodW h₁
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_taint _ (pins_bases aN aAcc aTmp o a b) h₂))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  have hH : Hdr t.mem L.B L.w _ := hm ▸ hg.hdr
  exact WP.mono (fnHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) hH hZ ho ha hb hdx hcx h8)
    fun u ⟨h1, h2, h3, h4, h5, h6, _, h8', _⟩ => ⟨h1, h2, h3, h4, h5, h6, h8'⟩

/-- Montgomery multiplication by calls of `vg_rsa_mont_mul`, as inlined code. -/
def Mont.fnBase : Mont where
  mm := mmFnBase
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 _ d4 _ hinv hB := by
    rw [mmFnBase_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv hB ⊢
    refine WP.mono (mulBase_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      ho ha hb d1 d2 d3 d4 hdx hcx h8 hinv hB) fun t' ⟨h1, h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      h1, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mmFnBase_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
