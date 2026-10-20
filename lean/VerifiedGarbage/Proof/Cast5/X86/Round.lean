module

public import VerifiedGarbage.Proof.Cast5.X86.Scan
public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# CAST5 on 32-bit x86: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `xmm0` (`spread`), scans `VG_CAST5_S1234`, stores the four values
in the working space and combines them into `f` (`combine`), then makes the
Feistel step and moves the subkeys' pointer in its slot (`feistel`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (tableEnt)

/-! ## The working space -/

/-- A slot of the working space at `S`, readable. -/
theorem slot_rd {s : State} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {d n : Nat} (h : d + n ≤ 256) (hn : 0 < n := by decide) :
    InRegions (s.rd ++ s.wr) (addr S d) n := by
  rw [addr_off hfit d (by omega)]
  obtain ⟨g, hg, hc⟩ := hw
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ h (by decide)

/-- A slot of the working space at `S`, writable. -/
theorem slot_wr {s : State} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {d n : Nat} (h : d + n ≤ 256) (hn : 0 < n := by decide) :
    InRegions s.wr (addr S d) n := by
  rw [addr_off hfit d (by omega)]
  exact CallLay.inRegions_sub hw h (by decide)

/-- Slots that do not overlap. -/
theorem slot_sep {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) {d n e k : Nat}
    (hd : d < 256) (he : e < 256) (h : d + n ≤ e ∨ e + k ≤ d) (hn : n ≤ 256) (hk : k ≤ 256) :
    Mem.Sep (addr S d) n (addr S e) k := by
  rw [addr_off hfit d (by omega), addr_off hfit e (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

/-- The region of slot `d`, `n` bytes. -/
abbrev slotR (S : BitVec 32) (d n : Nat) : Region := ⟨S.setWidth 64 + BitVec.ofNat 64 d, n⟩

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = kb) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .eax = Proof.Cast5.step a kb b ∧ t.gpr .ecx = (if b < 4 then kb >>> 1 else kb) ∧
      t.mem = s.mem ∧ t.xmm = s.xmm := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [hax, hcx, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], funext fun _ => rfl⟩
  · rw [ite_eq_right h4]
    crun [hax, hcx, hn, List.append_nil]
    exact ⟨rfl, by rw [ite_eq_right h4], funext fun _ => rfl⟩

theorem rotate_ok (s : State) {a kb : BitVec 32} (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = kb) :
    WP isa (.block rotate) s fun t =>
      t.gpr .eax = a.rotateLeft (kb.toNat % 32) ∧ t.mem = s.mem ∧ t.xmm = s.xmm := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax hcx) fun t₁ ⟨a₁, k₁, m₁, x₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, m₂, x₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, m₃, x₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, m₄, x₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, m₅, x₅⟩ => ?_
  refine ⟨?_, by rw [m₅, m₄, m₃, m₂, m₁], by rw [x₅, x₄, x₃, x₂, x₁]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-! ## The indices -/

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

theorem dword_movd0 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_zero, Nat.zero_add, ite_true]

theorem dword_movd1 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_one]
  rw [ite_eq_right (by omega)]
  simp

theorem lanes_eq (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ a) ((0 : BitVec 96) ++ b))
      (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ c) ((0 : BitVec 96) ++ d)) = ofDwords a b c d := by
  rw [punpcklqdq_eq, punpckldq_eq, punpckldq_eq]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_movd0]

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .eax = i) :
    WP isa (.block spread) s fun t => t.xmm .xmm0 = L (idx i) ∧ t.mem = s.mem := by
  unfold spread lanes
  crun [hax]
  exact lanes_eq _ _ _ _

/-! ## The round function -/

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {S P : BitVec 32} {km kr d : Spec.Cast5.Word}
    (hsi : s.gpr .esi = S) (hbp : s.gpr .ebp = d)
    (hp : InRegions (s.rd ++ s.wr) (addr S kpOff) 4) (hpv : s.mem.readW (addr S kpOff) 32 = P)
    (hm : InRegions (s.rd ++ s.wr) (addr P 0) 4) (hmv : s.mem.readW (addr P 0) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (addr P 64) 4) (hrv : s.mem.readW (addr P 64) 32 = kr) :
    WP isa (.block (mask t)) s fun u =>
      u.gpr .eax = Proof.Cast5.mix t km d ∧ u.gpr .ecx = kr ∧ u.mem = s.mem ∧ u.xmm = s.xmm := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    crun [hsi, hbp, hp, hpv, hm, hmv, hr, hrv]
    exact ⟨rfl, funext fun _ => rfl⟩

/-- What a round needs: `(L, R)` in `ebx`, `ebp`; the working space at `S`
(`esi`), its slot `kpOff` pointing at `Kmᵢ` (and `Krᵢ` 64 bytes on); the
table; four bytes of stack below `esp`, apart from the working space and the
table. -/
structure RoundPre (s : State) (S P : BitVec 32) (km kr l r : Spec.Cast5.Word) : Prop where
  bx : s.gpr .ebx = l
  bp : s.gpr .ebp = r
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  kp : s.mem.readW (addr S kpOff) 32 = P
  inM : InRegions (s.rd ++ s.wr) (addr P 0) 4
  valM : s.mem.readW (addr P 0) 32 = km
  inR : InRegions (s.rd ++ s.wr) (addr P 64) 4
  valR : s.mem.readW (addr P 64) 32 = kr
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  tab : TabAt s.mem (s.syms s1234Sym) (tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1)

/-- The first block of a round: `I`, and its bytes in the lanes of `xmm0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {S P : BitVec 32}
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s S P km kr l r) :
    WP isa (.block (mask t ++ rotate ++ spread)) s
      fun u => u.xmm .xmm0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.si h.bp (slot_rd h.fitS h.wS (by decide)) h.kp h.inM h.valM h.inR h.valR)
    fun u ⟨ua, uc, um, _⟩ => ?_
  refine WP.mono (rotate_ok u ua uc) fun v ⟨va, vm, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um)⟩

theorem rd_lane (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * j)) 32 = dword v j := readW_writeW128 m a v hj

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool) {S P : BitVec 32}
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.xmm .xmm1 = L v) (hbx : s.gpr .ebx = l) (hbp : s.gpr .ebp = r) (hsi : s.gpr .esi = S)
    (hfit : S.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (S.setWidth 64) 256)
    (hp : s.mem.readW (addr S kpOff) 32 = P) :
    WP isa (.block (([.movdquStore (at_ .esi 0) .xmm1] : List Instr) ++ combine t ++ feistel up)) s
      fun u => u.gpr .ebx = r ∧
        u.gpr .ebp = l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0) ∧
        u.mem = (s.mem.writeW (addr S 0) (L v)).writeW (addr S kpOff) (if up then P + 4 else P - 4) ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ u.xmm = s.xmm := by
  have e (j : Nat) (hj : j < 4) : (s.mem.writeW (addr S 0) (L v)).readW (addr S (4 * j)) 32 = v j := by
    rw [addr_off hfit (4 * j) (by omega), addr_off hfit 0 (by omega), BitVec.add_zero, rd_lane _ _ _ hj,
      dword_L _ hj]
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  have eP : (s.mem.writeW (addr S 0) (L v)).readW (addr S kpOff) 32 = P := by
    rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (d := kpOff) (n := 4) (e := 0) (k := 16)
      (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)]
    exact hp
  have r0 := slot_rd hfit hw (d := 0) (n := 4) (by decide)
  have r4 := slot_rd hfit hw (d := 4) (n := 4) (by decide)
  have r8 := slot_rd hfit hw (d := 8) (n := 4) (by decide)
  have r12 := slot_rd hfit hw (d := 12) (n := 4) (by decide)
  have rP := slot_rd hfit hw (d := kpOff) (n := 4) (by decide)
  have w0 := slot_wr hfit hw (d := 0) (n := 16) (by decide)
  have wP := slot_wr hfit hw (d := kpOff) (n := 4) (by decide)
  simp only [kpOff] at eP rP wP ⊢
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    crun [hsi, hbx, hbp, h1, r0, r4, r8, r12, rP, w0, wP, e0, e1, e2, e3, eP, kpOff]
    refine ⟨?_, rfl, funext fun _ => rfl⟩
    rw [BitVec.xor_comm]; rfl

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- The registers a round writes. -/
def roundRegs : List Reg := [.eax, .ecx, .edx, .ebx, .ebp, .edi]

/-- The memory a round writes: the stack word, the scan's result and the
subkeys' pointer. -/
def roundMem (S sp : BitVec 32) : List Region := [below sp 4, slotR S 0 16, slotR S kpOff 4]

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {S P : BitVec 32} {km kr l r : Spec.Cast5.Word} (h : RoundPre s S P km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .ebx = r ∧ u.gpr .ebp = l ^^^ fT t km kr r ∧
      u.mem.readW (addr S kpOff) 32 = (if up then P + 4 else P - 4) ∧
      Frame (roundMem S (s.gpr .esp)) s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧
      Keep roundRegs s u := by
  have hw : writesOnly roundRegs (round t up) = true := by
    rcases ht with rfl | rfl | rfl <;> cases up <;> decide
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .ebx = r ∧ u.gpr .ebp = l ^^^ fT t km kr r ∧
      u.mem.readW (addr S kpOff) 32 = (if up then P + 4 else P - 4) ∧
      Frame (roundMem S (s.gpr .esp)) s.mem u.mem ∧ u.syms = s.syms by
    exact WP.mono (WP.keep roundRegs main hw) fun u ⟨⟨a, b, c, d, e⟩, hku⟩ =>
      ⟨a, b, c, d, hku.rd, hku.wr, e, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  refine WP.seq (WP.mono_syms (WP.keep [.eax, .ecx, .edx, .edi] (first_ok s ht h) (by
    rcases ht with rfl | rfl | rfl <;> decide)) fun u ⟨⟨u0, um⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have usp : u.gpr .esp = s.gpr .esp := uk.gpr .esp (by decide)
  have usi : u.gpr .esi = S := (uk.gpr .esi (by decide)).trans h.si
  refine WP.seq (WP.mono (scan_ok u s1234Sym (tab := tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1) u0 (fun k hk => idx_lt i hk) (by rw [usp]; exact h.sp)
    (by rw [usy]; exact h.fitT) (by rw [uk.rd, uk.wr, usy]; exact h.inT) (by rw [usy, usp]; exact h.dT)
    (by rw [um, usy]; exact h.tab)) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.eax, .ecx, .edx, .edi]) (ha : q ≠ .eax) (hc : q ≠ .ecx) (hd : q ≠ .edx) :
      v.gpr q = s.gpr q := (vk.gpr q ha hc hd).trans (uk.gpr q hq)
  have vsi : v.gpr .esi = S := (g .esi (by decide) (by decide) (by decide) (by decide)).trans h.si
  have hvw : InRegions v.wr (S.setWidth 64) 256 := by rw [vk.wr, uk.wr]; exact h.wS
  have vP : v.mem.readW (addr S kpOff) 32 = P := by
    have hc : Region.Contains ⟨S.setWidth 64, 256⟩ (addr S kpOff) (32 / 8) := by
      rw [addr_off h.fitS kpOff (by decide)]
      exact Offset.contains_base _ (by decide) (by decide)
    have hd : ∀ r' ∈ [below (u.gpr .esp) 4], Region.Disjoint ⟨S.setWidth 64, 256⟩ r' := by
      intro r' hr'; rw [List.mem_singleton] at hr'; subst hr'; rw [usp]; exact h.dS
    rw [vk.mem.readW hc hd (by decide), um]
    exact h.kp
  refine WP.mono (post_ok v ht up (S := S) (l := l) (r := r) v1
    (by rw [g .ebx (by decide) (by decide) (by decide) (by decide)]; exact h.bx)
    (by rw [g .ebp (by decide) (by decide) (by decide) (by decide)]; exact h.bp) vsi h.fitS hvw vP)
    fun w ⟨wbx, wbp, wm, _, _, wsy, _⟩ => ?_
  refine ⟨wbx, ?_, ?_, ?_, wsy.trans (vk.syms.trans usy)⟩
  · rw [wbp]
    congr 1
    unfold fT
    rw [hi]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [wm, Mem.readW_writeW_self32]
  · rw [wm]
    have hS0 : Region.Contains (slotR S 0 16) (addr S 0) (128 / 8) := by
      rw [addr_off h.fitS 0 (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)
    have hSP : Region.Contains (slotR S kpOff 4) (addr S kpOff) (32 / 8) := by
      rw [addr_off h.fitS kpOff (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)
    refine Frame.writeW (Frame.writeW ?_ (by simp [roundMem]) _ hS0) (by simp [roundMem]) _ hSP
    have vf := vk.mem
    rw [um, usp] at vf
    exact vf.mono (by intro r' hr'; rw [List.mem_singleton] at hr'; subst hr'; simp [roundMem])

end VG.Proof.Cast5.X86
