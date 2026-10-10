import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.Booth

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- A signed Booth entry, with an explicit zero-or-one projective coordinate. -/
structure TEntryPostJ (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  x19 : s'.gpr .x19 = s.gpr .x19
  keep : KeepRegs (tcombClob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  z : wordsVal s'.mem base K.E.z K.M.n =
    if 1 ≤ bmag K.w k i then K.one else 0
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (bentry C K.w k i)

/-- The existing full-table selector followed by masked Booth sign correction. -/
theorem tentryJ_after_digit_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hm : s.gpr .x2 = BitVec.ofNat 64 (bmag K.w k i))
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hout : ∀ i < (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPostJ K C base size k i s s' → WP isa rest s' Q) :
    WP isa (.block K.select) s fun s₂ =>
      WP isa (.seq (.block K.bnegY) rest) s₂ Q := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hn4 := hL.n8
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_arith
  have hbits' := hL.bits
  have hbitsw := hL.bitsw
  have hH2 : 2 ^ K.w = 2 * K.H := by
    unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega_arith
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_arith))
      (by decide)
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have htmp : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.comb.lay.tmp x hx
  obtain ⟨hE, hap⟩ := combLay_E hL.comb hA
  dsimp only [TCombCfg.toComb] at hE hap
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi); rwa [Nat.mul_succ] at this
  have hwJ : K.w ≤ K.w * K.J := by have := Nat.mul_le_mul_left K.w (show 1 ≤ K.J by omega_arith); omega_arith
  let s₁ := s
  have m₁ : s₁.gpr .x2 = BitVec.ofNat 64 (bmag K.w k i) := hm
  have k₁ : Keeps [.x2,.x3,.x4,.x9,.x16] s s₁ := ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  have sy₁ : s₁.syms = s.syms := rfl
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hx₁ : s₁.gpr .x19 = BitVec.ofNat 64 i := by rw [k₁.gpr _ (by decide), hx]
  have hmag : bmag K.w k i ≤ K.H := bmag_le (by omega_arith) k i
  have hlen := tcombWords_length (n := K.M.n) (R := 2 ^ (64 * K.M.n)) (p := C.p) hV.len hV.lenH
  have hreg : InRegions (s₁.rd ++ s₁.wr) (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * K.H) := by
    obtain ⟨r, hr, hc⟩ := hTM.rd
    refine ⟨r, by rw [k₁.rd, k₁.wr]; exact hr, Region.contains_off hc ?_⟩
    rw [hlen, TCombCfg.tblBytes]
    have h2 := Nat.mul_le_mul_right (16 * K.M.n * K.H) (show i + 1 ≤ K.J from hi)
    rw [Nat.succ_mul] at h2
    have e : 16 * K.M.n * K.H = 8 * (K.H * (2 * K.M.n)) := by
      rw [Nat.mul_comm K.H, ← Nat.mul_assoc, ← Nat.mul_assoc]
    rw [Nat.mul_left_comm 8 K.J, ← e]
    omega_arith
  have hHe : K.H % 2 = 0 := by
    unfold TCombCfg.H; rw [show K.w - 1 = (K.w - 2) + 1 by omega_arith, Nat.pow_succ]; omega_arith
  have hout' : ∀ e < K.H, ∀ i' < 2 * K.M.n, ∀ b < 8, size ≤ ofs base
      (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i') + BitVec.ofNat 64 b) :=
    fun e he i' hi' b hb => by
      rw [TCombCfg.tblBytes, tbl_addr]
      refine hout _ ?_ b hb
      rw [hlen]
      have h1 : i * (K.H * (2 * K.M.n)) + e * (2 * K.M.n) + i' < i * (K.H * (2 * K.M.n)) + K.H * (2 * K.M.n) := by
        have := Nat.mul_le_mul_right (2 * K.M.n) (show e + 1 ≤ K.H from he)
        rw [Nat.succ_mul] at this; omega_arith
      have h2 := Nat.mul_le_mul_right (K.H * (2 * K.M.n)) (show i + 1 ≤ K.J from hi)
      rw [Nat.succ_mul] at h2
      omega_arith
  have WSelect : WP isa (.block K.select) s₁ fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ bmag K.w k i then
        wordsVal s₁.mem (T + BitVec.ofNat 64 (i * K.tblBytes))
          (16 * K.M.n * (bmag K.w k i - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ bmag K.w k i then
        wordsVal s₁.mem (T + BitVec.ofNat 64 (i * K.tblBytes))
          (16 * K.M.n * (bmag K.w k i - 1) + 8 * K.M.n) K.M.n else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ bmag K.w k i then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s₁ t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s₁.mem t.mem := by
    exact tselect_ok K hn4 hL.n2 hs₁ hx₁ m₁ hmag hHe hL.tbl.1 hL.tbl.2 (by omega_arith)
      (by rw [sy₁]; exact hT) hE hL.e16 hap (Nat.lt_trans hV.one_lt hpn) hreg hout'
  refine WP.mono WSelect fun s₂ h₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := h₂
  rw [k₁.mem] at ex₂ ey₂ U₂
  generalize ha : bmag K.w k i = a at ex₂ ey₂ ez₂ hmag
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  -- The selected coordinates.
  have hent : 1 ≤ a → wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n =
        (combAt tbl i (a - 1)).1 * 2 ^ (64 * K.M.n) % C.p ∧
      wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
        (combAt tbl i (a - 1)).2 * 2 ^ (64 * K.M.n) % C.p := fun h1 => by
    rw [TCombCfg.tblBytes]
    exact tbl_entry hTM hV.len hV.lenH hi (by omega_arith) (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
      (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
  have hs₂ := hs₁.of_keepRegs k₂ (sel_regs hn4 (Or.inl rfl))
  have hEW := entryW_sub (K := K.toComb)
  dsimp only [TCombCfg.toComb] at hEW
  have U₂' : Unch base (combW K.toComb) s.mem s₂.mem := U₂.mono fun w hw => hEW w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h | h <;> simp [h])
  have hmoW := combW_mo hL.comb hM
  have hM₂ : ModOkA K.M size C.p s₂.mem base := hM.unch U₂' hmoW hn
  have hzW := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb])
  dsimp only [TCombCfg.toComb] at hzW
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [U₂'.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega_arith), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · rw [(hent ‹_›).2]; exact Nat.mod_lt _ hp0
    · exact hV.one_lt
  refine WP.seq ?_
  rw [TCombCfg.bnegY, List.append_assoc, WP.block_append_iff]
  have hneg := hle K.neg (by tcomb_mem)
  have hzl := hle K.zero (by tcomb_mem)
  have W3 := sub_ok hs₂ hM₂ hA.mod (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl
    (hE K.E.y (by simp)).1 (hA.sl _ (by tcomb_mem)) (hA.sl _ (by tcomb_mem)) (hE K.E.y (by simp)).2
    (by rw [hz₂]; exact hp0) hEy₂
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨k₃, e₃⟩ := h₃
  have hs₃ : Scr s₃ base size := ⟨(k₃.gpr _ (x0_not_clob _)).trans hs₂.x0, k₃.wr ▸ hs₂.wr,
    hs₂.nowrap, hs₂.enc⟩
  have U₃ := k₃.unch
  have U₂₃ : Unch base (combW K.toComb) s.mem s₃.mem := (U₂'.trans U₃).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hEW w (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; clear * - hw; grind)
  have hx₃ : s₃.gpr .x19 = BitVec.ofNat 64 i := by
    rw [k₃.gpr _ (x19_not_clob _), k₂.gpr _ (sel_regs hn4 (Or.inr rfl)), hx₁]
  have hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [U₂₃.byte (fun w hw => by have := hL.bits_w w hw; omega_arith) (by omega_arith)]; exact hbits t ht
  rw [WP.block_append_iff]
  have W4 := bsignMask_ok K hs₃ (k := k) (j := i) (N := K.w * K.J) (by omega_arith) (by omega_arith)
    hwi (by omega_arith) (by omega_arith) hx₃ hbits₃
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨x₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have yneg := hL.comb.apart₂ (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_find hnd)
  have xy := hap.1
  have xz := hap.2.1
  have yz := hap.2.2
  have xneg := hL.comb.apart₂ (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_find hnd)
  have zneg := hL.comb.apart₂ (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by nd_find hnd)
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  have tx := htmp K.E.x (by tcomb_mem)
  have ty := htmp K.E.y (by tcomb_mem)
  have tz := htmp K.E.z (by tcomb_mem)
  dsimp only [TCombCfg.toComb] at yneg xneg zneg
  have W5 := sel_ok (decide (bcar K.w k (i+1)=1)) K.M.n hs₄ (by rw [x₄]; rfl) (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy.1 hEy.1 hneg hEy.2 hEy.2 (hA.sl _ (by tcomb_mem))
    (Or.inl (Nat.le_refl _)) (by omega_arith)
  refine WP.mono W5 fun s₅ h₅ => h s₅ ?_
  obtain ⟨e₅, k₅, O₅⟩ := h₅
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.mem
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (bcar K.w k (i+1)=1) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  have hk : KeepRegs (tcombClob K.M.n) s s₅ := by
    have cl : ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x16, .x17] ++ entryRegs K.M.n,
        r ∈ tcombClob K.M.n := tcombClob_sub _ hn4
    have c1 : ∀ r ∈ clob K.M.n, r ∈ tcombClob K.M.n := fun r hr =>
      combClob_tcombClob r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr)))
    refine (((((Keeps.regs k₁).mono fun r hr => cl r ?_).trans (k₂.mono fun r hr => cl r ?_)).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr, k₃.sp⟩ : KeepRegs (clob K.M.n) s₂ s₃).mono c1)).trans
      ((Keeps.regs k₄).mono fun r hr => cl r ?_)).trans (k₅.mono fun r hr => cl r ?_) <;>
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; clear * - hr; grind
  -- The point the selected entry represents.
  have hR : Rep C (tmv C K.M.n base s₂ K.E.x) (tmv C K.M.n base s₂ K.E.y) (tmv C K.M.n base s₂ K.E.z)
      (combPtW C K.w i a) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [ex₂, ey₂, ez₂]
    by_cases h1 : 1 ≤ a
    · obtain ⟨hx, hy⟩ := hent h1
      simp only [h1, ↓reduceIte, hx, hy, toM_mont hV.unit, hV.one]
      have := hV.entry i hi (a - 1) (by omega_arith)
      rwa [Nat.sub_add_cancel h1] at this
    · have h0 : a = 0 := by omega_arith
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega_arith, ↓reduceIte, toM_zero, hV.one]
      rw [show combPtW C K.w i 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
      exact rep_infinity' hC
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, hk, ?_, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (x19_not_clob _),
      k₂.gpr _ (sel_regs hn4 (Or.inr rfl)), k₁.gpr _ (by decide)]
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    clear * - hw
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; split
      · rw [(hent ‹_›).1]; exact Nat.mod_lt _ hp0
      · exact hp0
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact hV.one_lt
      · exact hp0
  · rw [vz,ez₂,ha]
  · have ex : tmv C K.M.n base s₅ K.E.x = tmv C K.M.n base s₂ K.E.x := by
      show toM _ _ _ = toM _ _ _; rw [vx]
    have ez : tmv C K.M.n base s₅ K.E.z = tmv C K.M.n base s₂ K.E.z := by
      show toM _ _ _ = toM _ _ _; rw [vz]
    rw [ex, ez]
    unfold bentry
    rw [ha]
    by_cases hb : bcar K.w k (i+1)=1
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy,decide_eq_true hb]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₂]),toM_zero]
        clear * -
        grind
      rw [hy,ite_eq_left hb]
      exact Rep.negY hR
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy,decide_eq_false hb]; rfl
      rw [hy,ite_eq_right hb]
      exact hR

/-- Compute a Booth magnitude, scan its public row, and apply its sign. -/
theorem tentryJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hb1 : 1≤K.bits) {c : Bool} (hc : (c=true ∧ 1≤i) ∨ (c=false ∧ i=0))
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hout : ∀ i < (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPostJ K C base size k i s s' → WP isa rest s' Q) :
    WP isa (.block (K.bdigit c ++ K.select)) s fun s₂ =>
      WP isa (.seq (.block K.bnegY) rest) s₂ Q := by
  rw [WP.block_append_iff]
  have hw := hL.w
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi)
    rwa [Nat.mul_succ] at this
  have hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega_arith
  have hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega_arith
  refine WP.mono_syms (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J)
    (by omega_arith) (by omega_arith) hwi hb hb1 hwb hx hbits hc) fun t ⟨hm,hk⟩ hsy => ?_
  have hs' := hs.of_keeps hk (by decide)
  have hM' : ModOkA K.M size C.p t.mem base := hk.mem ▸ hM
  refine tentryJ_after_digit_ok hL hA hC hV hpn hs' hM' hi
    (by rw [hk.gpr _ (by decide)]; exact hx) hm
    (fun q hq => by rw [hk.mem]; exact hbits q hq)
    (by rw [hk.mem]; exact hz) (by rw [hsy]; exact hT)
    (hTM.unch (by rw [hk.rd,hk.wr]) (fun _ _ _ _ => by rw [hk.mem])) hout
    fun u hu => h u ?_
  refine ⟨hu.scr,?_,?_,?_,hu.lt,hu.z,hu.rep⟩
  · rw [hu.x19,hk.gpr _ (by decide)]
  · exact ((Keeps.regs hk).mono (fun r hr => tcombClob_sub _ hL.n8 r (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      grind))).trans hu.keep
  · rw [← hk.mem]; exact hu.unch

end VG.Proof.Weierstrass.AArch64
