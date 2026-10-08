import VerifiedGarbage.Proof.Cast5.X86_64.Scan
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# CAST5 on x86-64: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `xmm0` (`spread`), scans `VG_CAST5_S1234` and combines the four
values into `f` (`combine`), then makes the Feistel step (`feistel`).
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly)

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .rax = a.setWidth 64) (h9 : s.gpr .r9 = kb.setWidth 64) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .rax = (Proof.Cast5.step a kb b).setWidth 64 ∧
      t.gpr .r9 = (if b < 4 then kb >>> 1 else kb).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    xrun [imm, hax, h9, execShift32, hn, List.cons_append, List.nil_append, xmm_setReg, xmm_setFlags]
    exact ⟨rfl, by rw [ite_eq_left h4]⟩
  · rw [ite_eq_right h4]
    xrun [imm, hax, h9, execShift32, hn, List.append_nil, xmm_setReg, xmm_setFlags]
    exact ⟨rfl, by rw [ite_eq_right h4]⟩

/-- The register state the blocks of a round leave alone. -/
structure Same (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm

theorem rotate_ok (s : State) {a kb : BitVec 32}
    (hax : s.gpr .rax = a.setWidth 64) (h9 : s.gpr .r9 = kb.setWidth 64) :
    WP isa (.block rotate) s fun t =>
      t.gpr .rax = (a.rotateLeft (kb.toNat % 32)).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.xmm = s.xmm := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax h9) fun t₁ ⟨a₁, k₁, m₁, r₁, w₁, x₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, m₂, r₂, w₂, x₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, m₃, r₃, w₃, x₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, m₄, r₄, w₄, x₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, m₅, r₅, w₅, x₅⟩ => ?_
  refine ⟨?_, by rw [m₅, m₄, m₃, m₂, m₁], by rw [r₅, r₄, r₃, r₂, r₁], by rw [w₅, w₄, w₃, w₂, w₁],
    by rw [x₅, x₄, x₃, x₂, x₁]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-- Lane `k` of the indices `spread` makes of `I`: byte `3 - k` of `I`. -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => (i >>> 8) &&& 255
  | 2 => (i >>> 16) &&& 255
  | _ => i >>> 24

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := i.isLt; omega

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 8] <;>
    omega

theorem lanes_eq (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (a.setWidth 64 ||| b.setWidth 64 <<< 32))
      ((0 : BitVec 64) ++ (c.setWidth 64 ||| d.setWidth 64 <<< 32)) = ofDwords a b c d := by
  rw [punpcklqdq_eq]
  have lo (x y : BitVec 32) : dword ((0 : BitVec 64) ++ (x.setWidth 64 ||| y.setWidth 64 <<< 32)) 0 = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp (disch := omega) only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
      BitVec.getLsbD_append, ite_eq_left, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, Nat.mul_zero, Nat.zero_add, decide_eq_true, Bool.not_true,
      Bool.false_and, Bool.or_false]
  have hi (x y : BitVec 32) : dword ((0 : BitVec 64) ++ (x.setWidth 64 ||| y.setWidth 64 <<< 32)) 1 = y := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp (disch := omega) only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
      BitVec.getLsbD_append, ite_eq_left, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, Nat.mul_one, decide_eq_true, Nat.add_sub_cancel_left]
    rw [BitVec.getLsbD_of_ge x _ (by omega), Bool.false_or, decide_eq_false (by omega), Bool.not_false,
      Bool.true_and]
  rw [lo, hi, lo, hi]

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .rax = i.setWidth 64) :
    WP isa (.block spread) s fun t =>
      t.xmm .xmm0 = L (idx i) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        (∀ x, x ≠ .xmm0 → x ≠ .xmm4 → t.xmm x = s.xmm x) := by
  unfold spread
  xrun [imm, hax, execShift32, XOp.exec, xmm_setReg, xmm_setFlags, gpr_setXmm, mem_setXmm, rd_setXmm,
    wr_setXmm, xmm_setXmm_self, xmm_setXmm_of_ne]
  refine ⟨lanes_eq _ _ _ _, fun x h0 h4 => ?_⟩
  simp only [xmm_setXmm_of_ne _ _ h0, xmm_setXmm_of_ne _ _ h4, xmm_setReg, xmm_setFlags]

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr d : Spec.Cast5.Word}
    (hbp : s.gpr .rbp = d.setWidth 64)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr .r12) 4) (hmv : s.mem.readW (s.gpr .r12) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 64) 4)
    (hrv : s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block (mask t ++ ([.mov32 .r9 (.mem (at_ .r12 64))] : List Instr))) s fun u =>
      u.gpr .rax = (Proof.Cast5.mix t km d).setWidth 64 ∧ u.gpr .r9 = kr.setWidth 64 ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.xmm = s.xmm ∧ u.gpr .r12 = s.gpr .r12 := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    xrun [VG.Proof.Cast5.X86_64.ea_at, hbp, hm, hmv, hr, hrv, xmm_setReg, xmm_setFlags,
      List.cons_append, List.nil_append]
    rfl

theorem rd_lane (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * j)) 32 = dword v j := readW_writeW128 m a v hj

theorem rd_lane0 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 32 = dword v 0 := by
  rw [← readW_writeW128 m a v (j := 0) (by decide), BitVec.add_zero]

theorem rd_lane1 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 4) 32 = dword v 1 := readW_writeW128 m a v (j := 1) (by decide)
theorem rd_lane2 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 8) 32 = dword v 2 := readW_writeW128 m a v (j := 2) (by decide)
theorem rd_lane3 (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 12) 32 = dword v 3 := readW_writeW128 m a v (j := 3) (by decide)

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.xmm .xmm1 = L v) (hbx : s.gpr .rbx = l.setWidth 64) (hbp : s.gpr .rbp = r.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r8) 16) :
    WP isa (.block (([.movdquStore (at_ .r8 0) .xmm1] : List Instr) ++ combine t ++ feistel up)) s
      fun u => u.gpr .rbx = r.setWidth 64 ∧
        u.gpr .rbp = (l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0)).setWidth 64 ∧
        u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
        u.mem = s.mem.writeW (s.gpr .r8) (L v) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.xmm = s.xmm := by
  have hc (k : Nat) (hk : k < 4) :
      InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 (4 * k)) 4 := by
    obtain ⟨g, hg, hgc⟩ := hw
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hgc⟩ (by omega) (by decide)
  have e0 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4 := by
    have := hc 0 (by decide); rwa [BitVec.add_zero] at this
  have e1 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4 := hc 1 (by decide)
  have e2 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 8) 4 := hc 2 (by decide)
  have e3 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 12) 4 := hc 3 (by decide)
  have d0 : dword (L v) 0 = v 0 := dword_L v (by decide)
  have d1 : dword (L v) 1 = v 1 := dword_L v (by decide)
  have d2 : dword (L v) 2 = v 2 := dword_L v (by decide)
  have d3 : dword (L v) 3 = v 3 := dword_L v (by decide)
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    xrun [VG.Proof.Cast5.X86_64.ea_at, imm, State.store128, hw, h1, hbx, hbp, e0, e1, e2, e3, rd_lane0,
      rd_lane1, rd_lane2, rd_lane3, d0, d1, d2, d3, xmm_setReg, xmm_setFlags, List.cons_append,
      List.nil_append, sx_ofNat (show 4 < 2 ^ 31 by decide)]
    exact ⟨by rw [BitVec.xor_comm]; rfl, rfl⟩

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- The registers a round writes. -/
def roundRegs : List Reg := [.rax, .rbx, .rbp, .r9, .r10, .r11, .r12, .r14, .r15]

/-- What a round needs: `(L, R)` in `ebx`, `ebp`; `Kmᵢ` at `r12` and `Krᵢ` at
`r12 + 64`; 16 writable bytes at `r8`; the table. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) : Prop where
  bx : s.gpr .rbx = l.setWidth 64
  bp : s.gpr .rbp = r.setWidth 64
  inM : InRegions (s.rd ++ s.wr) (s.gpr .r12) 4
  valM : s.mem.readW (s.gpr .r12) 32 = km
  inR : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 64) 32 = kr
  w : InRegions s.wr (s.gpr .r8) 16
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

/-- The first block of a round: `I`, and its bytes in the lanes of `xmm0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr l r : Spec.Cast5.Word}
    (h : RoundPre s km kr l r) :
    WP isa (.block (mask t ++ ([.mov32 .r9 (.mem (at_ .r12 64))] : List Instr) ++ rotate ++ spread)) s
      fun u => u.xmm .xmm0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.bp h.inM h.valM h.inR h.valR) fun u ⟨ua, u9, um, urd, uwr, _, _⟩ => ?_
  refine WP.mono (rotate_ok u ua u9) fun v ⟨va, vm, vrd, vwr, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm, wrd, wwr, _⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um), wrd.trans (vrd.trans urd), wwr.trans (vwr.trans uwr)⟩

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .rbx = r.setWidth 64 ∧ u.gpr .rbp = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
      Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧
      Keep roundRegs s u := by
  have hw : writesOnly roundRegs (round t up) = true := by
    rcases ht with rfl | rfl | rfl <;> cases up <;> decide
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .rbx = r.setWidth 64 ∧ u.gpr .rbp = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .r12 = (if up then s.gpr .r12 + 4 else s.gpr .r12 - 4) ∧
      Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr by
    exact WP.mono_syms (WP.keep roundRegs main hw) fun u ⟨⟨a, b, c, d, e, f⟩, hku⟩ hsy =>
      ⟨a, b, c, d, e, f, hsy, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  refine WP.seq (WP.mono_syms (WP.keep [.rax, .r9, .r14, .r15] (first_ok s ht h) (by
    rcases ht with rfl | rfl | rfl <;> decide)) fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have hT : Readable u (u.syms s1234Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono (scan_ok u s1234Sym u0 (fun k hk => idx_lt i hk) hT) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.rax, .r9, .r14, .r15]) (h10 : q ≠ .r10) (h11 : q ≠ .r11) :
      v.gpr q = s.gpr q := (vk.gpr q h10 h11).trans (uk.gpr hq)
  have hvw : InRegions v.wr (v.gpr .r8) 16 := by
    rw [vk.wr, uwr, g .r8 (by decide) (by decide) (by decide)]; exact h.w
  refine WP.mono (post_ok v ht up (l := l) (r := r) v1 (by rw [g .rbx (by decide) (by decide) (by decide)]; exact h.bx)
    (by rw [g .rbp (by decide) (by decide) (by decide)]; exact h.bp) hvw)
    fun w ⟨wbx, wbp, w12, wm, wrd, wwr, _⟩ => ?_
  refine ⟨wbx, ?_, ?_, ?_, by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩
  · rw [wbp]
    congr 2
    unfold fT
    rw [hi]
    have e (k : Nat) (hk : k < 4) : ent u.mem (u.syms s1234Sym) (idx i k).toNat k =
        tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx i k).toNat k :=
      ent_table (by rw [um, usy]; exact h.held) (idx_lt i hk) hk
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [w12, g .r12 (by decide) (by decide) (by decide)]
  · rw [wm, vk.mem, um, g .r8 (by decide) (by decide) (by decide)]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

end VG.Proof.Cast5.X86_64
