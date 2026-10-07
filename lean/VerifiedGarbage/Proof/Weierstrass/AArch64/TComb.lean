import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombTbl
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic
import VerifiedGarbage.Proof.Weierstrass.CombW

/-!
# The fixed-base comb from tables in memory on AArch64

As the comb (`Proof/Weierstrass/AArch64/Comb.lean`), for digits of `w` bits
and tables in memory (`Impl/Weierstrass/AArch64/TComb.lean`): iteration `j`
selects the entry of the digit's magnitude (`digitW_ok`, `tselect_ok`, whose
words are the entry's coordinates in Montgomery form, `tbl_entry`), negates
`y` for a negative digit (`tentry_ok`), and adds it to `A` (`combSum_ok`, the
comb's, on `toComb`), so that `A`, which represented `[combEW (j+1)]G`,
represents `[combEW j]G` (`combW_add`, `tstep_ok`); after the `J` digits,
`[k]G` (`tcomb_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The registers the comb from tables changes: the comb's and the rest of the
entry's. -/
def tcombClob (n : Nat) : List Reg := entryRegs n ++ combClob n

theorem combClob_tcombClob {n : Nat} : ∀ r ∈ combClob n, r ∈ tcombClob n := fun _ hr =>
  List.mem_append_right _ hr

/-- What the comb needs of its tables `tbl` (affine points, below `p`, whose
Montgomery forms `tcombWords` are in memory) and constants: `J` tables of `H`
entries, entry `m` of table `j` the point `[(m + 1) 2^(wj)]G`, the start
(in Montgomery form) `[H Σ_{i<J} 2^(wi)]G`, and `R mod p` one. -/
structure TCombVals (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : Prop where
  len : tbl.length = K.J
  lenH : ∀ j < K.J, (tbl.getD j []).length = K.H
  tbl_lt : ∀ j < K.J, ∀ m < K.H, (combAt tbl j m).1 < C.p ∧ (combAt tbl j m).2 < C.p
  unit : UnitMod C.p (2 ^ (64 * K.M.n))
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < K.H, Rep C (Fin.ofNat C.p (combAt tbl j m).1)
    (Fin.ofNat C.p (combAt tbl j m).2) 1 (combPtW C K.w j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (K.H * geomW K.w K.J) (G C))

/-- `x ∈ l` for the comb's lists, through `toComb`. -/
macro "tcomb_mem" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, combSlots, combWs, combRo, rcbW, rcbR, List.cons_append,
  List.nil_append, TCombCfg.toComb]))

/-- The selection's registers are neither `x0` nor `x19`. -/
theorem sel_regs {n : Nat} (hn : n ≤ 9) {r : Reg} (hr : r = .x0 ∨ r = .x19) :
    r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: Reg.x4 :: Reg.x5 :: Reg.x6 :: Reg.x7 :: Reg.x16 :: Reg.x17 ::
      entryRegs n := by
  intro h
  simp only [List.mem_cons] at h
  rcases hr with rfl | rfl <;>
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    first | exact absurd h (by decide) | exact entryRegs_regs n hn _ h (by simp)

theorem tcombClob_sub : ∀ n ≤ 9, ∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x16, .x17] ++
    entryRegs n, r ∈ tcombClob n := by decide

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
structure TEntryPost (K : TCombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  x19 : s'.gpr .x19 = s.gpr .x19
  keep : KeepRegs (tcombClob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  z : wordsVal s'.mem base K.E.z K.M.n =
    if 1 ≤ magH K.H (combWin K.w k i) then K.one else 0
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (signedPtW C K.w k i)

/-- The table's words are where the selection loads them. -/
theorem tbl_addr (T : Addr) (n H j e i : Nat) :
    T + BitVec.ofNat 64 (j * (16 * n * H)) + BitVec.ofNat 64 (16 * n * e + 8 * i) =
      T + BitVec.ofNat 64 (8 * (j * (H * (2 * n)) + e * (2 * n) + i)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  grind

/-- The entry of digit `i`, selected (from `x19 = i`) and negated for a
negative digit. -/
theorem tentry_after_digit_ok {publicLookup : Bool} {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hm : s.gpr .x2 = BitVec.ofNat 64 (magH K.H (combWin K.w k i)))
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hout : ∀ i < (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPost K C base size k i s s' → WP isa rest s' Q) :
    WP isa (.block (if publicLookup then K.selectPublic else K.select)) s fun s₂ =>
      WP isa (.seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) rest) s₂ Q := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hn4 := hL.n8
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  have hbits' := hL.bits
  have hbitsw := hL.bitsw
  have hH2 : 2 ^ K.w = 2 * K.H := by
    unfold TCombCfg.H; rw [← Nat.pow_succ']; congr 1; omega
  have hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega))
      (by decide)
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have htmp : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ K.M.tmp ∨ K.M.tmp + 8 * K.M.n ≤ x :=
    fun x hx => hL.comb.lay.tmp x hx
  obtain ⟨hE, hap⟩ := combLay_E hL.comb hA
  dsimp only [TCombCfg.toComb] at hE hap
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi); rwa [Nat.mul_succ] at this
  have hwJ : K.w ≤ K.w * K.J := by have := Nat.mul_le_mul_left K.w (show 1 ≤ K.J by omega); omega
  let s₁ := s
  have m₁ : s₁.gpr .x2 = BitVec.ofNat 64 (magH K.H (combWin K.w k i)) := hm
  have k₁ : Keeps [.x2,.x3,.x4,.x9,.x16] s s₁ := ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  have sy₁ : s₁.syms = s.syms := rfl
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hx₁ : s₁.gpr .x19 = BitVec.ofNat 64 i := by rw [k₁.gpr _ (by decide), hx]
  have hwlt := combWin_lt K.w k i
  have hmag : magH K.H (combWin K.w k i) ≤ K.H := magH_le (by rw [← hH2]; exact hwlt)
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
    omega
  have hHe : K.H % 2 = 0 := by
    unfold TCombCfg.H; rw [show K.w - 1 = (K.w - 2) + 1 by omega, Nat.pow_succ]; omega
  have hout' : ∀ e < K.H, ∀ i' < 2 * K.M.n, ∀ b < 8, size ≤ ofs base
      (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i') + BitVec.ofNat 64 b) :=
    fun e he i' hi' b hb => by
      rw [TCombCfg.tblBytes, tbl_addr]
      refine hout _ ?_ b hb
      rw [hlen]
      have h1 : i * (K.H * (2 * K.M.n)) + e * (2 * K.M.n) + i' < i * (K.H * (2 * K.M.n)) + K.H * (2 * K.M.n) := by
        have := Nat.mul_le_mul_right (2 * K.M.n) (show e + 1 ≤ K.H from he)
        rw [Nat.succ_mul] at this; omega
      have h2 := Nat.mul_le_mul_right (K.H * (2 * K.M.n)) (show i + 1 ≤ K.J from hi)
      rw [Nat.succ_mul] at h2
      omega
  have WSelect : WP isa (.block (if publicLookup then K.selectPublic else K.select)) s₁ fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ magH K.H (combWin K.w k i) then
        wordsVal s₁.mem (T + BitVec.ofNat 64 (i * K.tblBytes))
          (16 * K.M.n * (magH K.H (combWin K.w k i) - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ magH K.H (combWin K.w k i) then
        wordsVal s₁.mem (T + BitVec.ofNat 64 (i * K.tblBytes))
          (16 * K.M.n * (magH K.H (combWin K.w k i) - 1) + 8 * K.M.n) K.M.n else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ magH K.H (combWin K.w k i) then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s₁ t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s₁.mem t.mem := by
    cases publicLookup
    · exact tselect_ok K hn4 hL.n2 hs₁ hx₁ m₁ hmag hHe hL.tbl.1 hL.tbl.2 (by omega)
        (by rw [sy₁]; exact hT) hE hL.e16 hap (Nat.lt_trans hV.one_lt hpn) hreg hout'
    · exact tselectPublic_ok K hn4 hs₁ hx₁ m₁ hmag (Nat.two_pow_pos _) hL.tbl.2 (by omega)
        (by rw [sy₁]; exact hT) hE hap (Nat.lt_trans hV.one_lt hpn) hreg hout'
  refine WP.mono WSelect fun s₂ h₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, U₂⟩ := h₂
  rw [k₁.mem] at ex₂ ey₂ U₂
  generalize ha : magH K.H (combWin K.w k i) = a at ex₂ ey₂ ez₂ hmag
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  -- The selected coordinates.
  have hent : 1 ≤ a → wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n =
        (combAt tbl i (a - 1)).1 * 2 ^ (64 * K.M.n) % C.p ∧
      wordsVal s.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n =
        (combAt tbl i (a - 1)).2 * 2 ^ (64 * K.M.n) % C.p := fun h1 => by
    rw [TCombCfg.tblBytes]
    exact tbl_entry hTM hV.len hV.lenH hi (by omega) (Nat.lt_trans (Nat.mod_lt _ hp0) hpn)
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
    rw [U₂'.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; split
    · rw [(hent ‹_›).2]; exact Nat.mod_lt _ hp0
    · exact hV.one_lt
  refine WP.seq ?_
  rw [negYW, List.append_assoc, WP.block_append_iff]
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
      rw [U₂₃.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega)]; exact hbits t ht
  rw [WP.block_append_iff]
  have W4 := signMaskW_ok hs₃ K.w K.bits (k := k) (j := i) (N := K.w * K.J) (by omega) (by omega)
    hwi (by omega) (by omega) hx₃ hbits₃
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨x₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have yneg := hL.comb.apart₂ (x := K.E.y) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by clear * - hnd; grind)
  have xy := hap.1
  have xz := hap.2.1
  have yz := hap.2.2
  have xneg := hL.comb.apart₂ (x := K.E.x) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by clear * - hnd; grind)
  have zneg := hL.comb.apart₂ (x := K.E.z) (y := K.neg) (by tcomb_mem) (by tcomb_mem) (by clear * - hnd; grind)
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  have tx := htmp K.E.x (by tcomb_mem)
  have ty := htmp K.E.y (by tcomb_mem)
  have tz := htmp K.E.z (by tcomb_mem)
  dsimp only [TCombCfg.toComb] at yneg xneg zneg
  have W5 := sel_ok (decide (combWin K.w k i < 2 ^ (K.w - 1))) K.M.n hs₄ (by rw [x₄]; rfl) (o := K.E.y)
    (a := K.E.y) (b := K.neg) hEy.1 hEy.1 hneg hEy.2 hEy.2 (hA.sl _ (by tcomb_mem))
    (Or.inl (Nat.le_refl _)) (by omega)
  refine WP.mono W5 fun s₅ h₅ => h s₅ ?_
  obtain ⟨e₅, k₅, O₅⟩ := h₅
  -- The values.
  have m₄ : s₄.mem = s₃.mem := k₄.mem
  have vx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.E.x K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)]
  have vz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.E.z K.M.n := by
    rw [O₅.wordsVal (by omega) (by omega), m₄, U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)]
  have vy₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (combWin K.w k i < 2 ^ (K.w - 1)) then
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
      have := hV.entry i hi (a - 1) (by omega)
      rwa [Nat.sub_add_cancel h1] at this
    · have h0 : a = 0 := by omega
      subst h0
      simp only [show ¬ 1 ≤ 0 by omega, ↓reduceIte, toM_zero, hV.one]
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
    unfold signedPtW
    have hHd : K.H = 2 ^ (K.w - 1) := rfl
    by_cases h8 : 2 ^ (K.w - 1) ≤ combWin K.w k i
    · have hy : tmv C K.M.n base s₅ K.E.y = tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = toM _ _ _
        rw [vy, decide_eq_false (show ¬ combWin K.w k i < 2 ^ (K.w - 1) from Nat.not_lt_of_ge h8)]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = combWin K.w k i - 2 ^ (K.w - 1) := by rw [← ha, hHd, magH]; simp [h8]
      rw [this] at hR
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -tmv C K.M.n base s₂ K.E.y := by
        show toM _ _ _ = -toM _ _ _
        rw [vy, decide_eq_true (show combWin K.w k i < 2 ^ (K.w - 1) from Nat.lt_of_not_ge h8)]
        simp only [↓reduceIte]
        rw [toM_sub (by omega_using [hEy₂]), toM_zero]
        clear * -
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : a = 2 ^ (K.w - 1) - combWin K.w k i := by rw [← ha, hHd, magH]; simp [h8]
      rw [this] at hR
      exact Rep.negY hR


theorem tentry_ok {publicLookup : Bool} {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hbits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) (hT : s.syms K.tsym = T)
    (hTM : TblMem s T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hout : ∀ i < (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl).length, ∀ b < 8,
      size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b))
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPost K C base size k i s s' → WP isa rest s' Q) :
    WP isa (.block (K.digit ++ (if publicLookup then K.selectPublic else K.select))) s fun s₂ =>
      WP isa (.seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) rest) s₂ Q := by
  rw [WP.block_append_iff]
  have hw := hL.w
  have hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi)
    rwa [Nat.mul_succ] at this
  have hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega
  have hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega
  refine WP.mono_syms (digitW_ok K hs (k := k) (j := i) (N := K.w * K.J)
    (by omega) (by omega) hwi hb hwb hx hbits) fun t ⟨hm,hk⟩ hsy => ?_
  have hs' := hs.of_keeps hk (by decide)
  have hM' : ModOkA K.M size C.p t.mem base := hk.mem ▸ hM
  refine tentry_after_digit_ok hL hA hC hV hpn hs' hM' hi
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

/-! ## The loop -/

/-- The tables survive a change of the working space only. -/
theorem TblMem.of_unch {s s' : State} {T : Addr} {ws : List (BitVec 64)} {base : Addr} {size : Nat}
    {W : List (Nat × Nat)} (h : TblMem s T ws) (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr)
    (hU : Unch base W s.mem s'.mem) (hW : ∀ w ∈ W, w.1 + w.2 ≤ size)
    (hout : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    TblMem s' T ws :=
  h.unch hrd fun i hi b hb => hU _ fun w hw => Or.inr (by have := hW w hw; have := hout i hi b hb; omega)

/-- What the comb reads and never writes, at the start: the curve's `a` and
`3b`, zero, the table of the scalar's bits (`kbytes` bytes, the rest of its
`w J` zero after `init`), the tables' address, and the tables, apart from the
working space. -/
structure TCombFixed (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (k : Nat)
    (T : Addr) (ws : List (BitVec 64)) : Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K.toComb, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < K.kbytes, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  k_lt : k < 2 ^ K.kbytes
  tsym : s₀.syms K.tsym = T
  tbl : TblMem s₀ T ws
  out : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)

/-- The loop's invariant at `x19 = j`: `A` represents `[combEW w k J j]G`, and
the table of bits (all `w J` bytes) and the tables are where the digits and
the selection read them. -/
structure TCombInv (K : TCombCfg) (C : Curve) (base : Addr) (size k : Nat) (T : Addr)
    (ws : List (BitVec 64)) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (tcombClob K.M.n) s₀ s
  unch : Unch base (tcombW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combEW K.w k K.J j) (G C))
  bits : ∀ t < K.w * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  tbl : TblMem s T ws
  tsym : s.syms K.tsym = T

/-- What the comb writes is in the working space. -/
theorem tcombW_size {K : TCombCfg} {C : Curve} {size : Nat} {mem : Mem} {base : Addr}
    (hL : TCombLay K size) (hM : ModOkA K.M size C.p mem base) : ∀ w ∈ tcombW K, w.1 + w.2 ≤ size := by
  intro w hw
  simp only [tcombW, combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
  · exact hL.comb.lay.le y (combWs_slots _ y hy)
  · exact hM.tmp
  · exact hL.bits

/-- A slot read only is apart from what the comb writes. -/
theorem tcombW_ro {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {x : Nat}
    (hx : x ∈ combRo K.toComb) : ∀ w ∈ tcombW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ro hL.comb hx w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.bits_sl x (List.mem_cons_of_mem _ (combRo_slots x hx)); dsimp only; omega

/-- The bytes of the table of bits, apart from what the loop writes. -/
theorem combW_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.w * K.J) :
    ∀ w ∈ combW K.toComb, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  have : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  intro w hw; have := hL.bits_w w hw; omega

/-- An iteration. -/
theorem tstep_ok {publicLookup : Bool} {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hM3 : AM3 C) (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j) :
    WP isa (K.step publicLookup) s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j - 1) ∧
        s'.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hn4 := hL.n8
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hmoW := combW_mo hL.comb hI.mod
  have hEW := entryW_sub (K := K.toComb)
  dsimp only [TCombCfg.toComb] at hEW
  refine WP.of_syms ?_
  unfold TCombCfg.step
  refine WP.seq ?_
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono_syms (decCounter_ok s hj (by omega) hI.x19) fun s₁ h₁ sy₁ => ?_
  obtain ⟨b₁, k₁⟩ := h₁
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  have hM₁ : ModOkA K.M size C.p s₁.mem base := by rw [hm₁]; exact hI.mod
  have hbits₁ : ∀ t < K.w * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [hm₁]; exact hI.bits t ht
  have hzW := tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb])
  have hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [hm₁, hI.unch.wordsVal hzW (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have hT : s₁.syms K.tsym = T := by rw [sy₁]; exact hI.tsym
  have hTM : TblMem s₁ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    hI.tbl.unch (by rw [k₁.rd, k₁.wr]) fun _ _ _ _ => by rw [hm₁]
  refine tentry_ok (publicLookup := publicLookup) hL hA hC hV hpn hs₁ hM₁ (i := j - 1) (by omega) b₁ hbits₁ hz hT hTM hF.out
    fun s₃ E₃ => ?_
  have U₁₃ : Unch base (combW K.toComb) s.mem s₃.mem := by
    rw [← hm₁]
    exact E₃.unch.mono fun w hw => hEW w hw
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hM₃ : ModOkA K.M size C.p s₃.mem base := hI.mod.unch U₁₃ hmoW hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [E₃.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.apart₂ hxs (by tcomb_mem) (by grind)
        · exact hL.comb.lay.tmp x (combWs_slots _ x hxs))
        (by have := hle x (combWs_slots _ x hxs); omega), hm₁]
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by
      have := hle x (combRo_slots x hx); omega)
  have hlt₃ : ∀ x ∈ rcbR K.toComb.S K.toComb.A K.toComb.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  refine WP.mono (combSum_ok hL.comb hA hV.unit E₃.scr hM₃ hlt₃) fun s₄ S₄ => ?_
  dsimp only [TCombCfg.toComb] at S₄
  have tb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.b
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combEW K.w k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  have hS := S₄.val
  rw [tb] at hS
  have hP := hC.onCurve_mul hG (combEW K.w k K.J j)
  have hQ : onCurve C (signedPtW C K.w k (j - 1)) = true := by
    unfold signedPtW combPtW
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hR := hC.add3 hM3 hP hQ hRA E₃.rep hS.symm
  have hadd := combW_add hC hG (w := K.w) (k := k) (J := K.J) (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPtW C K.w k (j - 1) = (if 2 ^ (K.w - 1) ≤ combWin K.w k (j - 1) then
      combPtW C K.w (j - 1) (combWin K.w k (j - 1) - 2 ^ (K.w - 1))
      else negPt (combPtW C K.w (j - 1) (2 ^ (K.w - 1) - combWin K.w k (j - 1)))) := rfl
  rw [hsp, hadd] at hR
  have hx₄ : s₄.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [S₄.keep.gpr _ (x19_not_clob _), E₃.x19, b₁]
  have U₄ : Unch base (combW K.toComb) s.mem s₄.mem := (U₁₃.trans S₄.unch).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw <;> exact hw
  intro sy₄
  refine ⟨⟨S₄.scr, hx₄, ?_, (U₃.trans S₄.unch).mono fun w hw => ?_,
    hM₃.unch S₄.unch (combW_mo hL.comb hM₃) hn, S₄.lt, hR, fun t ht => ?_, ?_,
    by rw [sy₄]; exact hI.tsym⟩, hx₄⟩
  · refine (((hI.keep.trans ((Keeps.regs k₁).mono ?_)).trans E₃.keep).trans
      (S₄.keep.mono fun r hr => ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact combClob_tcombClob _ (by simp [combClob])
    · exact combClob_tcombClob _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_right _ hr)))
  · rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact List.mem_append_left _ hw
  · have hb := hL.bits
    have hz : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
    rw [U₄.byte (combW_bits hL ht) (by omega_using [hb, hz, ht, hn])]
    exact hI.bits t ht
  · exact TblMem.of_unch hI.tbl (by rw [S₄.keep.rd, S₄.keep.wr, E₃.keep.rd, E₃.keep.wr, k₁.rd, k₁.wr])
      U₄ (fun w hw => tcombW_size hL hI.mod w (List.mem_append_left _ hw)) hF.out

/-- Zero stored to the `m` words at `o`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .x7 = 0)
    {o : Nat} (ho8 : o % 8 = 0) : ∀ m, o + 8 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => st .x7 (o + 8 * i))) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (8 * m) s.mem s'.mem ∧
        ∀ d < 8 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega)⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz ho8 m (by omega)) fun s₁ h₁ => ?_
    obtain ⟨k₁, O₁, z₁⟩ := h₁
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    refine WP.mono (st_ok hs₁ (d := o + 8 * m) (by omega) (by omega) .x7) fun s₂ h₂ => ?_
    subst h₂
    have hx7 : s₁.gpr .x7 = 0 := (k₁.gpr _ (by simp)).trans hz
    rw [hx7]
    have Ow := writeW_outside s₁.mem base (d := o + 8 * m) (0 : BitVec 64) (by omega)
    refine ⟨⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩, fun x hx => (Ow x (by omega)).trans (O₁ x (by omega)),
      fun d hd => ?_⟩
    by_cases hd' : d < 8 * m
    · show (s₁.mem.writeW (off base (o + 8 * m)) (0 : BitVec 64)) (off base (o + d)) = 0
      rw [Ow _ (by rw [ofs_off0 base (by omega)]; omega)]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 8 * m) = BitVec.ofNat 64 (d - 8 * m) := by
        simp only [off]; rw [show o + d = o + 8 * m + (d - 8 * m) by omega, Offset.add_ofNat_add_sub]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 8 * m < 2 ^ 64 by omega), show d - 8 * m < 64 / 8 by omega,
        ↓reduceIte]
      simp

/-- Initialize the comb accumulator and pad the scalar bits. -/
theorem tcomb_init_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (.block K.init) s fun s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ size := fun x hx =>
    hL.comb.lay.le x (combWs_slots _ x hx)
  have al : ∀ x ∈ combWs K.toComb, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots _ x hx)
  have b64 : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have axy := hL.comb.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have axz := hL.comb.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have ayz := hL.comb.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  dsimp only [TCombCfg.toComb] at axy axz ayz
  have hsl : ∀ x ∈ combWs K.toComb, K.bits + K.kbytes + 8 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ (combWs_slots _ x hx))
  have hbz := hL.bits
  have hzw : K.w * K.J ≤ K.kbytes + 8 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega
  refine WP.of_syms ?_
  have e : K.init = setConst K.M.n K.A.x K.start.1 ++ (setConst K.M.n K.A.y K.start.2 ++
      (setConst K.M.n K.A.z K.one ++ ([zero7] ++ ((List.range K.zw).map
        (fun i => st .x7 (K.bits + K.kbytes + 8 * i)) ++ [.movz .x .x19 (BitVec.ofNat 16 K.J) 0])))) := by
    unfold TCombCfg.init TCombCfg.zw
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  have W1 := setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.start_lt.1 hpn)
  refine WP.mono W1 fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.start_lt.2 hpn)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) (le _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (Nat.lt_trans hV.one_lt hpn)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s₃) fun s₄ h₄ => ?_
  obtain ⟨z₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zstores_ok hs₄ z₄ hL.bits8 K.zw hL.bits) fun s₅ h₅ => ?_
  obtain ⟨k₅, O₅, z₅⟩ := h₅
  have hs₅ := hs₄.of_keepRegs k₅ (by simp)
  refine WP.mono (setCounter_ok s₅ (j := K.J) (by omega)) fun s₆ h₆ => ?_
  obtain ⟨b₆, k₆⟩ := h₆
  have m₆ : s₆.mem = s₅.mem := k₆.mem
  have U₃ : Unch base (combW K.toComb) s.mem s₃.mem :=
    (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, TCombCfg.toComb] at hw ⊢
      grind
  have U₆ : Unch base (tcombW K) s.mem s₆.mem := by
    rw [m₆]
    refine (U₃.trans (show Unch base [(K.bits + K.kbytes, 8 * K.zw)] s₃.mem s₅.mem by
      rw [← k₄.mem]; exact O₅.unch)).mono fun w hw => hw
  have hmo : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact combW_mo hL.comb hM w hw
    · simp only [List.mem_singleton] at hw; subst hw
      have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega
  -- `A`, apart from the cleared words.
  have hA5 : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s₃.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K.toComb := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> tcomb_mem
      rw [m₆, O₅.wordsVal (by have := hsl x hxs; omega) (b64 x hxs), k₄.mem]
  have vx : wordsVal s₆.mem base K.A.x K.M.n = K.start.1 := by
    rw [hA5 _ (by simp), O₃.wordsVal axz (b64 _ (by tcomb_mem)), O₂.wordsVal axy (b64 _ (by tcomb_mem)), e₁]
  have vy : wordsVal s₆.mem base K.A.y K.M.n = K.start.2 := by
    rw [hA5 _ (by simp), O₃.wordsVal ayz (b64 _ (by tcomb_mem)), e₂]
  have vz : wordsVal s₆.mem base K.A.z K.M.n = K.one := by rw [hA5 _ (by simp), e₃]
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  intro sy₆
  have I₆ : TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s₆ K.J := by
    refine ⟨hs₅.of_keeps k₆ (by decide), b₆, ?_, U₆, hM.unch U₆ hmo hn, ?_, ?_, fun t ht => ?_, ?_,
      by rw [sy₆]; exact hF.tsym⟩
    · have c1 : ∀ r ∈ [Reg.x1], r ∈ tcombClob K.M.n := fun r hr => combClob_tcombClob _
        (combClob_mem (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))
      exact ((((k₁.mono c1).trans (k₂.mono c1)).trans (k₃.mono c1)).trans
        ((Keeps.regs k₄).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact combClob_tcombClob _ (combClob_mem (by simp)))).trans
        ((k₅.mono fun r hr => absurd hr (List.not_mem_nil)).trans
        ((Keeps.regs k₆).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact combClob_tcombClob _ (by simp [combClob])))
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hV.start_lt.1
      · rw [vy]; exact hV.start_lt.2
      · rw [vz]; exact hV.one_lt
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, hV.one, combEW_top]
      exact hV.start
    · by_cases htk : t < K.kbytes
      · rw [U₆.byte (fun w hw => by
          rcases List.mem_append.mp hw with hw | hw
          · exact combW_bits hL ht w hw
          · simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega)
          (by omega_using [hbz, hzw, ht, hn])]
        exact hF.bits t htk
      · have := z₅ (t - K.kbytes) (by omega)
        rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega] at this
        rw [m₆, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
          (Nat.pow_le_pow_right (by decide) (by omega)))]
        rfl
    · exact TblMem.of_unch hF.tbl (by rw [k₆.rd, k₆.wr, k₅.rd, k₅.wr, k₄.rd, k₄.wr, k₃.rd, k₃.wr,
        k₂.rd, k₂.wr, k₁.rd, k₁.wr]) U₆ (tcombW_size hL hM) hF.out
  exact I₆

/-- `[k]G` into `A`, for `k < 2^kbytes` whose bits are the table at `K.bits`;
only `tcombClob` and `tcombW` change. -/
theorem tcomb_ok {publicLookup : Bool} {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hM3 : AM3 C) (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (K.comb publicLookup) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  unfold TCombCfg.comb
  refine WP.seq (WP.mono (tcomb_init_ok hL hA hV hpn hs hM hF) fun s₆ I₆ => ?_)

  exact countLoop_ok (Inv := fun j s' =>
      TCombInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' j) (n := K.J)
    (by omega) (fun j s' h1 h2 hi => tstep_ok (publicLookup := publicLookup) hL hA hC hM3 hG hV hpn hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combEW_zero hk]; exact hi.rep⟩)
    hJ.1 I₆

end VG.Proof.Weierstrass.AArch64
