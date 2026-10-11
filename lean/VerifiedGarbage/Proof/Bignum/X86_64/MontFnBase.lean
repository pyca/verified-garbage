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
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega_arith

theorem arr_off (B : Addr) {j : Nat} (hj : j < 2 ^ 32) :
    off (B + (BitVec.ofNat 32 j).setWidth 64 * 8#64) (8 * sArr 0) = off B (8 * sArr j) := by
  rw [ofNat32_64 hj]
  simp only [off, sArr, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
  omega_arith

/-- The callee-saved registers of `s` in the low quadwords of `xmm8`–`xmm13`
of `t`, as `saves` leaves them. -/
def Saved (s t : State) : Prop :=
  t.xmm .xmm8 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm9 = (0 : BitVec 64) ++ s.gpr .rbp ∧
    t.xmm .xmm10 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm11 = (0 : BitVec 64) ++ s.gpr .r13 ∧
    t.xmm .xmm12 = (0 : BitVec 64) ++ s.gpr .r14 ∧ t.xmm .xmm13 = (0 : BitVec 64) ++ s.gpr .r15

theorem Saved.of_xmm {s t t' : State} (h : Saved s t) (hx : t'.xmm = t.xmm) : Saved s t' := by
  unfold Saved at *; rw [hx]; exact h

theorem Saved.of_keep {s s' t : State} {rs : List Reg} (h : Saved s' t) (hk : Keep rs s s')
    (hr : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], r ∉ rs) : Saved s t := by
  unfold Saved at *
  rw [hk.gpr (hr .rbx (by simp)), hk.gpr (hr .rbp (by simp)), hk.gpr (hr .r12 (by simp)),
    hk.gpr (hr .r13 (by simp)), hk.gpr (hr .r14 (by simp)), hk.gpr (hr .r15 (by simp))] at h
  exact h

/-- `enter` and `basesR`: the bases of the arrays whose indices are in `edx`,
`ecx` and `r8d`, as `bases` gives them, and the callee-saved registers in
`xmm8`–`xmm13`. -/
theorem fnHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block (enter ++ basesR)) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] s t ∧
      Saved s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rdx, .rcx, .r8, .rbx, .r11, .r9, .r10, .r12, .r15, .rsi] (c := .block (enter ++ basesR))
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Saved s t) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, k, h.2.2.2.2.2.2.2.2.2⟩
  unfold enter zext saves basesR Saved
  simp only [List.cons_append, List.nil_append]
  xrun [XOp.exec, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm, setReg_xmm, XBinOp.eval, qword_movq,
    State.ea, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off B (show o < 2 ^ 32 by omega_arith),
    arr_off B (show a < 2 ^ 32 by omega_arith), arr_off B (show b < 2 ^ 32 by omega_arith),
    hl (sArr o) (by unfold sArr; omega_arith), hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
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
    rw [Offset.add_add, Mem.sub_ofNat_toNat a (by omega_arith)]
    simp only [show j + i < 16 by omega_arith, ite_true]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    simp [show 8 * (j + i) + k < 128 by omega_arith, show 8 * i + k < 64 by omega_arith]
    congr 1; omega_arith
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
    Offset.toNat_sub_add x base (by omega_arith)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- `unsaves`: the callee-saved registers of `s` back, from `t`'s `xmm8`–`xmm13`
as `saves` left them. -/
theorem unsaves_ok {s t : State} (h : Saved s t) :
    WP isa (.block unsaves) t fun t' =>
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t'.gpr r = s.gpr r) ∧ t'.mem = t.mem ∧
        t'.xmm = t.xmm ∧ Keep [.rbx, .rbp, .r12, .r13, .r14, .r15] t t' := by
  obtain ⟨x8, x9, x10, x11, x12, x13⟩ := h
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (c := .block unsaves)
    (Q := fun t' => (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t'.gpr r = s.gpr r) ∧ t'.mem = t.mem ∧
      t'.xmm = t.xmm) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold unsaves
  xrun [setReg_xmm, x8, x9, x10, x11, x12, x13, fnExtract_lo]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

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
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv hB
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp, .r13, .r14] (WP.vecKeep (by decide) (mmTail_ok hs₁ hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
    (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
    h8₁ h12 h15 hsi₁ hinv hB)) (by decide)) fun s₂ ⟨⟨⟨hlt, heq, har, k₂⟩, hx₂, _⟩, _⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_xmm hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  rw [hm₁] at hlt heq har
  rw [← mt] at hlt heq har
  exact ⟨hlt, heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

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
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mmFnBase_ct (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
