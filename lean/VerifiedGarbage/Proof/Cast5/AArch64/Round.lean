import VerifiedGarbage.Proof.Cast5.AArch64.Scan
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Cast5.Round

/-!
# CAST5 on AArch64: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `v0` (`spread`), scans `VG_CAST5_S1234` and combines the four
values into `f` (`combine`), then makes the Feistel step (`feistel`).
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym)
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .x4 = a.setWidth 64) (h13 : s.gpr .x13 = kb.setWidth 64) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .x4 = (Proof.Cast5.selStep a kb b).setWidth 64 ∧
      t.gpr .x13 = (if b < 4 then kb >>> 1 else kb).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.v = s.v := by
  have hn : 32 - 2 ^ b < 32 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [hax, h13, hn, CondCode.holds, zf_write]
    refine ⟨?_, by rw [ite_eq_left h4]⟩
    unfold Proof.Cast5.selStep
    simp
  · rw [ite_eq_right h4]
    crun [hax, h13, hn, CondCode.holds, zf_write]
    refine ⟨?_, by rw [ite_eq_right h4]⟩
    unfold Proof.Cast5.selStep
    simp

theorem rotate_ok (s : State) {a kb : BitVec 32}
    (hax : s.gpr .x4 = a.setWidth 64) (h13 : s.gpr .x13 = kb.setWidth 64) :
    WP isa (.block rotate) s fun t =>
      t.gpr .x4 = (a.rotateLeft (kb.toNat % 32)).setWidth 64 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.v = s.v := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax h13) fun t₁ ⟨a₁, k₁, m₁, r₁, w₁, x₁⟩ => ?_
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
  rw [a₅]
  simp only [Proof.Cast5.selStep_eq_step _ _ (show 0 < 5 by decide),
    Proof.Cast5.selStep_eq_step _ _ (show 1 < 5 by decide), Proof.Cast5.selStep_eq_step _ _ (show 2 < 5 by decide),
    Proof.Cast5.selStep_eq_step _ _ (show 3 < 5 by decide), Proof.Cast5.selStep_eq_step _ _ (show 4 < 5 by decide),
    Proof.Cast5.steps_eq]

/-! ## The indices -/

/-- Lane `k` of the indices `spread` makes of `I`: byte `3 - k` of `I`. -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i <<< 24 >>> 24
  | 1 => i <<< 16 >>> 24
  | 2 => i <<< 8 >>> 24
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq] <;> omega

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> omega

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .x4 = i.setWidth 64) :
    WP isa (.block spread) s fun t =>
      t.v .v0 = L (idx i) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        (∀ x, x ≠ .v0 → t.v x = s.v x) := by
  unfold spread
  crun [hax]
  refine ⟨?_, fun x h0 => ?_⟩
  · rw [setLane_four]
    rfl
  · simp only [v_write, v_setV_of_ne _ _ h0]

/-! ## The round -/

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr d : Spec.Cast5.Word}
    (h6 : s.gpr .x6 = d.setWidth 64)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr .x12) 4) (hmv : s.mem.readW (s.gpr .x12) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 64) 4)
    (hrv : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 64) 32 = kr) :
    WP isa (.block (mask t)) s fun u =>
      u.gpr .x4 = (Proof.Cast5.mix t km d).setWidth 64 ∧ u.gpr .x13 = kr.setWidth 64 ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  have e0 : s.gpr .x12 + BitVec.ofNat 64 0 = s.gpr .x12 := BitVec.add_zero _
  have hm' : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 0) 4 := by rw [e0]; exact hm
  have hmv' : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 32 = km := by rw [e0]; exact hmv
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    crun [h6, hm', hmv', hr, hrv]
    rfl

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.v .v1 = L v) (h5 : s.gpr .x5 = l.setWidth 64) (h6 : s.gpr .x6 = r.setWidth 64) :
    WP isa (.block (combine t ++ feistel up)) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧
        u.gpr .x6 = (l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0)).setWidth 64 ∧
        u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v := by
  have d0 : vword (L v) 0 = v 0 := vword_L v (by decide)
  have d1 : vword (L v) 1 = v 1 := vword_L v (by decide)
  have d2 : vword (L v) 2 = v 2 := vword_L v (by decide)
  have d3 : vword (L v) 3 = v 3 := vword_L v (by decide)
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    crun [h1, h5, h6, d0, d1, d2, d3, BitVec.or_self]
    exact ⟨by rw [BitVec.xor_comm]; rfl, rfl⟩

/-- The registers a round writes. -/
def roundRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- What a round needs: `(L, R)` in `w5`, `w6`; `Kmᵢ` at `x12` and `Krᵢ` at
`x12 + 64`; the table. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) : Prop where
  x5 : s.gpr .x5 = l.setWidth 64
  x6 : s.gpr .x6 = r.setWidth 64
  inM : InRegions (s.rd ++ s.wr) (s.gpr .x12) 4
  valM : s.mem.readW (s.gpr .x12) 32 = km
  inR : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 64) 4
  valR : s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 64) 32 = kr
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

/-- The first block of a round: `I`, and its bytes in the lanes of `v0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km kr l r : Spec.Cast5.Word}
    (h : RoundPre s km kr l r) :
    WP isa (.block (mask t ++ rotate ++ spread)) s
      fun u => u.v .v0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.x6 h.inM h.valM h.inR h.valR) fun u ⟨ua, u13, um, urd, uwr, _⟩ => ?_
  refine WP.mono (rotate_ok u ua u13) fun v ⟨va, vm, vrd, vwr, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm, wrd, wwr, _⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um), wrd.trans (vrd.trans urd), wwr.trans (vwr.trans uwr)⟩

theorem round_writes {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool) :
    writesOnly roundRegs (round t up) = true ∧ (round t up).noCalls = true ∧
      (round t up).allInstrs keepsV = true := by
  rcases ht with rfl | rfl | rfl <;> cases up <;> exact ⟨by decide, by decide, by decide +kernel⟩

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧ u.gpr .x6 = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ Keep roundRegs s u := by
  obtain ⟨hw, hn, hv⟩ := round_writes ht up
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .x5 = r.setWidth 64 ∧ u.gpr .x6 = (l ^^^ fT t km kr r).setWidth 64 ∧
      u.gpr .x12 = (if up then s.gpr .x12 + 4 else s.gpr .x12 - 4) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr by
    exact WP.mono_syms (WP.keep roundRegs main hw hn hv) fun u ⟨⟨a, b, c, d, e, f⟩, hku⟩ hsy =>
      ⟨a, b, c, d, e, f, hsy, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  have hw1 : writesOnly [.x4, .x9, .x13, .x14, .x15] (.block (mask t ++ rotate ++ spread)) = true ∧
      (.block (mask t ++ rotate ++ spread) : Prog isa).allInstrs keepsV = true := by
    rcases ht with rfl | rfl | rfl <;> exact ⟨by decide, by decide +kernel⟩
  refine WP.seq (WP.mono_syms (WP.keep [.x4, .x9, .x13, .x14, .x15] (first_ok s ht h) hw1.1 rfl hw1.2)
    fun u ⟨⟨u0, um, urd, uwr⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have hT : Readable u (u.syms s1234Sym) := by unfold Readable; rw [usy, urd, uwr]; exact h.tab
  refine WP.seq (WP.mono (scan_ok u s1234Sym u0 (fun k hk => idx_lt i hk) hT) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.x4, .x9, .x13, .x14, .x15]) (h10 : q ≠ .x10) (h11 : q ≠ .x11) :
      v.gpr q = s.gpr q := (vk.gpr q h10 h11).trans (uk.gpr q hq)
  refine WP.mono (post_ok v ht up (l := l) (r := r) v1 (by rw [g .x5 (by decide) (by decide) (by decide)]; exact h.x5)
    (by rw [g .x6 (by decide) (by decide) (by decide)]; exact h.x6))
    fun w ⟨w5, w6, w12, wm, wrd, wwr, _⟩ => ?_
  refine ⟨w5, ?_, ?_, by rw [wm, vk.mem, um], by rw [wrd, vk.rd, urd], by rw [wwr, vk.wr, uwr]⟩
  · rw [w6]
    congr 2
    unfold fT
    rw [hi]
    have e (k : Nat) (hk : k < 4) : ent u.mem (u.syms s1234Sym) (idx i k).toNat k =
        tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1 (idx i k).toNat k :=
      ent_table (by rw [um, usy]; exact h.held) (idx_lt i hk) hk
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [w12, g .x12 (by decide) (by decide) (by decide)]

end VG.Proof.Cast5.AArch64
