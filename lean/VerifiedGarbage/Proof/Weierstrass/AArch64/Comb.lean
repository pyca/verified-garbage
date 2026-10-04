import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# The fixed-base comb on AArch64

An iteration of `comb K` (`combStep_ok`) selects the entry of table `j` for
the magnitude of digit `j` (`select_ok`), negates its `y` for a negative
digit, and adds it to the accumulator `A` by the complete addition, so that
`A`, which represented `[combE k J (j+1)]G`, represents `[combE k J j]G`
(`comb_add`, by the group law). From the start `[8 Σ_{i<J} 16^i]G`, after all
`J` digits `A` represents `[k]G` (`comb_ok`), for `k < 16^J` whose bits are
the table at `K.bits`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass CombCfg

/-- The registers the comb changes. -/
def combClob (n : Nat) : List Reg := .x19 :: .x9 :: maskRegs ++ clob n

/-! ## Representatives -/

/-- The reflection of a representative. -/
theorem Rep.negY {C : Curve} {X Y Z : Fe C} {P : Point C} (h : Rep C X Y Z P) :
    Rep C X (-Y) Z (negPt P) := by
  cases P with
  | infinity =>
    obtain ⟨hX, hY, hZ⟩ := h
    exact ⟨hX, fun h' => hY (by grind), hZ⟩
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := h
    exact ⟨hZ, hX, by rw [hY]; grind⟩

/-! ## The digit's sign -/

theorem testBit_three (k j : Nat) : k.testBit (4 * j + 3) = decide (8 ≤ nib k j) := by
  have := nib_eq k j
  have h0 := Bool.toNat_le (k.testBit (4 * j))
  have h1 := Bool.toNat_le (k.testBit (4 * j + 1))
  have h2 := Bool.toNat_le (k.testBit (4 * j + 2))
  cases h3 : k.testBit (4 * j + 3) <;> simp only [h3, Bool.toNat_true, Bool.toNat_false] at this <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq, Bool.true_eq] <;> omega

theorem sign_byte (b : Bool) :
    ((((if b then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64) - BitVec.ofNat 64 1 =
      bmask (!b) := by
  cases b <;> decide

/-- `x3` all ones if digit `j = x19` is negative. -/
theorem signMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (bits : Nat)
    {k j N : Nat} (hj : 4 * j + 4 ≤ N) (hN : bits + N ≤ size) (hb4 : bits + 3 < 4096)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (signMask bits)) s fun t =>
      t.gpr .x3 = bmask (decide (nib k j < 8)) ∧ Keeps [.x3, .x16] s t := by
  have hn := hs.nowrap
  rw [signMask, show ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16, .ldrb .x3 .x16 (bits + 3),
      .subImm .x .x3 .x3 1] : List Instr) = ([.lsl .x .x16 .x19 2, .add .x .x16 .x0 .x16] : List Instr) ++
      [.ldrb .x3 .x16 (bits + 3), .subImm .x .x3 .x3 1] from rfl, WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs (by omega) hx) fun a ⟨a16, ka⟩ => ?_
  have hr : InRegions (a.rd ++ a.wr) (off base (bits + (4 * j + 3))) 1 :=
    ⟨_, List.mem_append_right _ (ka.wr ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  have he : a.gpr .x16 + BitVec.ofNat 64 (bits + 3) = off base (bits + (4 * j + 3)) := by
    rw [a16, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg (off base) (by omega)
  have hv : ((a.mem.read (off base (bits + (4 * j + 3))) 1).setWidth 32).setWidth 64 =
      (((if k.testBit (4 * j + 3) then 1 else 0 : BitVec 8)).setWidth 32).setWidth 64 := by
    rw [read1_zext, ka.mem, hbits _ (by omega)]
    rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, Nat.mod_one,
    show bits + 3 < 4096 * 1 by omega, show (1 : Nat) < 4096 by decide,
    and_self, he, hr, hv, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  · rw [sign_byte, testBit_three]
    by_cases h : 8 ≤ nib k j
    · simp [h, show ¬ nib k j < 8 by omega]
    · simp [h, show nib k j < 8 by omega]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, ite_false]
    exact ka.gpr r (by simpa using hr.2)

/-! ## The entry -/

/-- What the comb needs of its constants as the code holds them: the
tables' and the start's coordinates and `R mod p` below `p`, and what they
represent, read as Montgomery forms: entry `m` of table `j` the point
`[(m + 1) 16^j]G`, the start `[8 Σ_{i<J} 16^i]G`, and `R mod p` one. -/
structure CombVals (K : CombCfg) (C : Curve) : Prop where
  tbl_lt : ∀ j < K.J, ∀ i, ((K.tbl.getD j []).map (·.1)).getD i 0 < C.p ∧
    ((K.tbl.getD j []).map (·.2)).getD i 0 < C.p
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < 8, Rep C (toM C.p (2 ^ (64 * K.M.n)) (combAt K.tbl j m).1)
    (toM C.p (2 ^ (64 * K.M.n)) (combAt K.tbl j m).2) 1 (combPt C j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (8 * geom K.J) (G C))

theorem getD_map_fst (t : List (Nat × Nat)) (i : Nat) :
    (t.map (·.1)).getD i 0 = (t.getD i (0, 0)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases t[i]? <;> rfl

theorem getD_map_snd (t : List (Nat × Nat)) (i : Nat) :
    (t.map (·.2)).getD i 0 = (t.getD i (0, 0)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases t[i]? <;> rfl

/-- The selected entry represents the point of its magnitude. -/
theorem entry_rep {K : CombCfg} {C : Curve} (hC : Law C) (hV : CombVals K C) {j a : Nat}
    (hj : j < K.J) (ha : a ≤ 8) :
    Rep C (toM C.p (2 ^ (64 * K.M.n)) (selVal 0 ((K.tbl.getD j []).map (·.1)) a))
      (toM C.p (2 ^ (64 * K.M.n)) (selVal K.one ((K.tbl.getD j []).map (·.2)) a))
      (toM C.p (2 ^ (64 * K.M.n)) (if a = 0 then 0 else K.one)) (combPt C j a) := by
  by_cases h0 : a = 0
  · subst h0
    simp only [selVal, ite_true, toM_zero, hV.one]
    have : combPt C j 0 = .infinity := by
      rw [combPt, Nat.zero_mul, Spec.Weierstrass.mul]; simp
    rw [this]
    exact rep_infinity' hC
  · simp only [selVal, h0, ite_false, hV.one, getD_map_fst, getD_map_snd]
    have := hV.entry j hj (a - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at this
    exact this

/-- The signed entry of digit `j`: `[d_j 16^j]G` as `comb_add` has it. -/
def signedPt (C : Curve) (k j : Nat) : Point C :=
  if 8 ≤ nib k j then combPt C j (nib k j - 8) else negPt (combPt C j (8 - nib k j))

theorem _root_.VG.Proof.Mont.OpKeep.unch {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n)] s.mem s'.mem :=
  fun x hx => h.mem x (hx (o, 8 * M.n) (by simp)) (hx (M.tmp, 8 * M.n) (by simp))

/-- The modulus survives a change of memory apart from it. -/
theorem _root_.VG.Proof.Mont.ModOk.unch {M : Mod} {size m : Nat} {base : Addr} {mem mem' : Mem}
    (hM : ModOk M size m mem base) {W : List (Nat × Nat)} (hU : Unch base W mem mem')
    (hW : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOk M size m mem' base :=
  ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep,
    by rw [hU.wordsVal hW (by have := hM.mo; omega)]; exact hM.val, hM.inv, hM.red⟩

/-- The comb's slots and modulus at offsets that loads and stores can encode. -/
structure CombA (K : CombCfg) : Prop where
  sl : ∀ x ∈ combSlots K, x % 8 = 0
  mod : ModA K.M

/-- After the selection and negation: `E` represents the signed entry of
digit `i`, and only `E`, `-y` and the temporary area changed. -/
structure EntryPost (K : CombCfg) (C : Curve) (base : Addr) (size k i : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  x19 : s'.gpr .x19 = s.gpr .x19
  keep : KeepRegs (combClob K.M.n) s s'
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)] s.mem s'.mem
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s'.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s' K.E.x) (tmv C K.M.n base s' K.E.y) (tmv C K.M.n base s' K.E.z)
    (signedPt C k i)

theorem combE_mem {K : CombCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ combWs K := by
  intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> comb_mem

theorem combLay_E {K : CombCfg} {size : Nat} (hL : CombLay K size) (hA : CombA K) :
    (∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0) ∧
    ((K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y)) := by
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  refine ⟨fun d hd => ⟨hL.lay.le d (combWs_slots K d (combE_mem d hd)),
    hA.sl d (combWs_slots K d (combE_mem d hd))⟩, ?_, ?_, ?_⟩
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)
  · exact hL.apart₂ (by comb_mem) (by comb_mem) (by grind)

theorem entryW_sub {K : CombCfg} : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n),
    (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ combW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inl ⟨_, by comb_mem, rfl⟩
  · exact Or.inr rfl

/-- The modulus is apart from what the comb writes. -/
theorem combW_mo {K : CombCfg} {size : Nat} (hL : CombLay K size) {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOk K.M size m mem base) :
    ∀ w ∈ combW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · have := hL.lay.mo y (combWs_slots K y hy); dsimp only; omega
  · have := hM.sep; dsimp only; omega

/-- A slot read only is apart from what the comb writes. -/
theorem combW_ro {K : CombCfg} {size : Nat} (hL : CombLay K size) {x : Nat} (hx : x ∈ combRo K) :
    ∀ w ∈ combW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  have hs : x ∈ combSlots K := by
    simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> comb_mem
  exact hL.apart_w hs (hL.ro x hx)

/-- The selection and the negation. -/
theorem combEntry_ok {K : CombCfg} {C : Curve} {base : Addr} {size k i : Nat}
    (hL : CombLay K size) (hA : CombA K) (hC : Law C) (hV : CombVals K C)
    (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base) (hi : i < K.J) (hx : s.gpr .x19 = BitVec.ofNat 64 i)
    (hm : MasksOf s (mag (nib k i)))
    (hbits : ∀ t < 4 * K.J, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal s.mem base K.zero K.M.n = 0)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', EntryPost K C base size k i s s' → WP isa rest s' Q) :
    WP isa (.seq (selectFrom K (List.range K.J)) (.seq (.block (negY K.M K.neg K.zero K.E.y K.bits)) rest))
      s Q := by
  have hn := hs.nowrap
  obtain ⟨hE, hap⟩ := combLay_E hL hA
  have hJ := hL.J
  have hmag := mag_le (nib_lt k i)
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
      (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ combW K := entryW_sub
  have hzW := combW_ro hL (x := K.zero) (by simp [combRo])
  have hmoW := combW_mo hL hM
  refine WP.seq (selectFrom_ok K (j := i) (by omega) (List.range K.J) hx (List.mem_range.mpr hi)
    (fun j hj => by have := List.mem_range.mp hj; omega) fun s₁ k₁ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : MasksOf s₁ (mag (nib k i)) := hm.keep (k₁.mono (by decide))
  have W := select_ok hs₁ K hmag hm₁ (K.tbl.getD i []) hE hap
    (fun i' => ⟨Nat.lt_trans (hV.tbl_lt i hi i').1 hpn, Nat.lt_trans (hV.tbl_lt i hi i').2 hpn⟩)
    (Nat.lt_trans hV.one_lt hpn)
  refine WP.mono W fun s₂ h₂ => ?_
  obtain ⟨ex₂, ey₂, ez₂, k₂, -, U₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [k₁.mem] at U₂
  have U₂' : Unch base (combW K) s.mem s₂.mem := U₂.mono fun w hw => hEW w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; rcases hw with h | h | h <;> simp [h])
  have hM₂ : ModOk K.M size C.p s₂.mem base := hM.unch U₂' hmoW hn
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [U₂'.wordsVal hzW (by have := hL.lay.le K.zero (by comb_mem); omega), hz]
  have hEy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [ey₂]; exact selVal_lt hV.one_lt (fun j => (hV.tbl_lt i hi j).2) _
  refine WP.seq ?_
  rw [negY, List.append_assoc, WP.block_append_iff]
  have hneg := hL.lay.le K.neg (by comb_mem)
  have hzl := hL.lay.le K.zero (by comb_mem)
  have W3 := sub_ok hs₂ hM₂ hA.mod (o := K.neg) (a := K.zero) (b := K.E.y) hneg hzl
    (hE K.E.y (by simp)).1 (hA.sl _ (by comb_mem)) (hA.sl _ (by comb_mem)) (hE K.E.y (by simp)).2
    (by rw [hz₂]; exact hp0) hEy₂
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨k₃, e₃⟩ := h₃
  have hs₃ : Scr s₃ base size := ⟨(k₃.gpr _ (x0_not_clob _ hM.n7)).trans hs₂.x0, k₃.wr ▸ hs₂.wr,
    hs₂.nowrap, hs₂.enc⟩
  have U₃ := k₃.unch
  have U₂₃ : Unch base (combW K) s.mem s₃.mem := (U₂'.trans U₃).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact hEW w (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢; grind)
  have hx₃ : s₃.gpr .x19 = BitVec.ofNat 64 i := by
    rw [k₃.gpr _ (x19_not_clob _), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hx]
  have hbits₃ : ∀ t < 4 * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [U₂₃.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega)]; exact hbits t ht
  rw [WP.block_append_iff]
  have W4 := signMask_ok hs₃ K.bits (k := k) (j := i) (N := 4 * K.J) (by omega) hL.bits hL.bits4 hx₃ hbits₃
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨x₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have yneg := hL.apart₂ (x := K.E.y) (y := K.neg) (by comb_mem) (by comb_mem) (by grind)
  have xy := hap.1
  have xz := hap.2.1
  have yz := hap.2.2
  have xneg := hL.apart₂ (x := K.E.x) (y := K.neg) (by comb_mem) (by comb_mem) (by grind)
  have zneg := hL.apart₂ (x := K.E.z) (y := K.neg) (by comb_mem) (by comb_mem) (by grind)
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  have tx := hL.lay.tmp K.E.x (by comb_mem)
  have ty := hL.lay.tmp K.E.y (by comb_mem)
  have tz := hL.lay.tmp K.E.z (by comb_mem)
  have W5 := sel_ok (decide (nib k i < 8)) K.M.n hs₄ (by rw [x₄]; rfl) (o := K.E.y) (a := K.E.y)
    (b := K.neg) hEy.1 hEy.1 hneg hEy.2 hEy.2 (hA.sl _ (by comb_mem)) (Or.inl (Nat.le_refl _))
    (by omega)
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
  have vy : wordsVal s₅.mem base K.E.y K.M.n = if decide (nib k i < 8) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [e₅, m₄, e₃, hz₂, vy₃]
  have hk : KeepRegs (combClob K.M.n) s s₅ := by
    have c1 : ∀ r ∈ clob K.M.n, r ∈ combClob K.M.n := fun r hr =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))
    refine (((((Keeps.regs k₁).mono ?_).trans (k₂.mono ?_)).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr, k₃.sp⟩ : KeepRegs (clob K.M.n) s₂ s₃).mono c1)).trans
      ((Keeps.regs k₄).mono ?_)).trans (k₅.mono ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [combClob, clob]
  have hYv := selVal_lt hV.one_lt (fun j => (hV.tbl_lt i hi j).2) (mag (nib k i))
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, hk, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (x19_not_clob _), k₂.gpr _ (by decide),
      k₁.gpr _ (by decide)]
  · refine ((U₂.trans (U₃.trans (m₄ ▸ O₅.unch))).mono ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx, ex₂]; exact selVal_lt hp0 (fun j => (hV.tbl_lt i hi j).1) _
    · rw [vy]; split
      · exact Nat.mod_lt _ hp0
      · exact hEy₂
    · rw [vz, ez₂]; split
      · exact hp0
      · exact hV.one_lt
  · have hR := entry_rep hC hV hi hmag
    have ex : tmv C K.M.n base s₅ K.E.x = toM C.p (2 ^ (64 * K.M.n))
        (selVal 0 ((K.tbl.getD i []).map (·.1)) (mag (nib k i))) := by
      show toM _ _ _ = _; rw [vx, ex₂]
    have ez : tmv C K.M.n base s₅ K.E.z = toM C.p (2 ^ (64 * K.M.n))
        (if mag (nib k i) = 0 then 0 else K.one) := by
      show toM _ _ _ = _; rw [vz, ez₂]
    rw [ex, ez]
    unfold signedPt
    by_cases h8 : 8 ≤ nib k i
    · have hy : tmv C K.M.n base s₅ K.E.y = toM C.p (2 ^ (64 * K.M.n))
          (selVal K.one ((K.tbl.getD i []).map (·.2)) (mag (nib k i))) := by
        show toM _ _ _ = _
        rw [vy, decide_eq_false (show ¬ nib k i < 8 by omega), ey₂]; rfl
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = nib k i - 8 := by simp [mag, h8]
      rw [this] at hR ⊢
      exact hR
    · have hy : tmv C K.M.n base s₅ K.E.y = -toM C.p (2 ^ (64 * K.M.n))
          (selVal K.one ((K.tbl.getD i []).map (·.2)) (mag (nib k i))) := by
        show toM _ _ _ = _
        rw [vy, decide_eq_true (show nib k i < 8 by omega)]
        simp only [↓reduceIte]
        rw [toM_sub (by omega), toM_zero, ey₂]
        grind
      rw [hy]
      simp only [h8, ↓reduceIte]
      have : mag (nib k i) = 8 - nib k i := by simp [mag, h8]
      rw [this] at hR ⊢
      exact Rep.negY hR

/-! ## The addition -/

/-- After the addition: `A` holds `rcbAdd` of what `A` and `E` held. -/
structure SumPost (K : CombCfg) (C : Curve) (base : Addr) (size : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob K.M.n) s s'
  unch : Unch base (combW K) s.mem s'.mem
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p
  val : (tmv C K.M.n base s' K.A.x, tmv C K.M.n base s' K.A.y, tmv C K.M.n base s' K.A.z) =
    VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s K.S.b3)
      (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
      (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)

/-- `A = A + E` by the complete addition into `D`, then copied. -/
theorem combSum_ok {K : CombCfg} {C : Curve} {base : Addr} {size : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (.seq (fprogB K.M (rcb3 K.S K.A K.E K.D)) (.block (copyPt K.M.n K.A K.D))) s
      (SumPost K C base size s) := by
  have hn := hs.nowrap
  have hR : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  have hI : Inv K.M base size C.p (· ∈ combSlots K) (rcbR K.S K.A K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, hR, hlt, fun _ _ => rfl⟩
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> comb_mem
  have W := rcb3_ok hL.lay ⟨hA.sl, hA.mod⟩ hp hL.add hSl hI (fun x hx => hx)
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono W fun s₁ h₁ => ?_))
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  have al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  have axd := hL.apart₂ (x := K.A.x) (y := K.D.x) (by comb_mem) (by comb_mem) (by grind)
  have ayd := hL.apart₂ (x := K.A.y) (y := K.D.y) (by comb_mem) (by comb_mem) (by grind)
  have azd := hL.apart₂ (x := K.A.z) (y := K.D.z) (by comb_mem) (by comb_mem) (by grind)
  have axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dxay := hL.apart₂ (x := K.D.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have dxaz := hL.apart₂ (x := K.D.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have dyaz := hL.apart₂ (x := K.D.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have W2 := copy_ok K.M.n hs₁ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have dyax := hL.apart₂ (x := K.D.y) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzax := hL.apart₂ (x := K.D.z) (y := K.A.x) (by comb_mem) (by comb_mem) (by grind)
  have dzay := hL.apart₂ (x := K.D.z) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have bAx := b64 K.A.x (by comb_mem)
  have bAy := b64 K.A.y (by comb_mem)
  have bAz := b64 K.A.z (by comb_mem)
  have bDx := b64 K.D.x (by comb_mem)
  have bDy := b64 K.D.y (by comb_mem)
  have bDz := b64 K.D.z (by comb_mem)
  have wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← v₁]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]

/-! ## The loop -/

/-- What the comb reads and never writes, at the start: the curve's `a` and
`3b`, zero, and the table of the bits of `k`. -/
structure CombFixed (K : CombCfg) (C : Curve) (base : Addr) (s₀ : State) (k : Nat) : Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < 4 * K.J, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- The loop's invariant at `x19 = j`: `A` represents `[combE k J j]G`. -/
structure CombInv (K : CombCfg) (C : Curve) (base : Addr) (size k : Nat) (s₀ s : State) (j : Nat) :
    Prop where
  scr : Scr s base size
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (combClob K.M.n) s₀ s
  unch : Unch base (combW K) s₀.mem s.mem
  mod : ModOk K.M size C.p s.mem base
  lt : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y) (tmv C K.M.n base s K.A.z)
    (mul (combE k K.J j) (G C))

theorem combRo_slots {K : CombCfg} : ∀ x ∈ combRo K, x ∈ combSlots K := by
  intro x hx
  simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> comb_mem

theorem combClob_mem {n : Nat} {r : Reg} (h : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]) :
    r ∈ combClob n := by
  simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]

/-- An iteration. -/
theorem combStep_ok {K : CombCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true)
    (hV : CombVals K C) (hpn : C.p < 2 ^ (64 * K.M.n)) {s₀ : State} (hF : CombFixed K C base s₀ k)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J) (hI : CombInv K C base size k s₀ s j) :
    WP isa (step K) s fun s' =>
      CombInv K C base size k s₀ s' (j - 1) ∧ s'.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have hn := hI.scr.nowrap
  have hJ := hL.J
  have hmoW := combW_mo hL hI.mod
  rw [step]
  refine WP.seq ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok s hj (by omega) hI.x19) fun s₁ h₁ => ?_
  obtain ⟨b₁, k₁⟩ := h₁
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have U₁ : Unch base (combW K) s₀.mem s₁.mem := by rw [k₁.mem]; exact hI.unch
  have hbits₁ : ∀ t < 4 * K.J, s₁.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [U₁.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega)]; exact hF.bits t ht
  have W2 := digit_ok hs₁ K.bits (k := k) (j := j - 1) (N := 4 * K.J) (by omega) hL.bits hL.bits4 b₁ hbits₁
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨m₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₂ : Unch base (combW K) s₀.mem s₂.mem := by rw [k₂.mem]; exact U₁
  have hM₂ : ModOk K.M size C.p s₂.mem base := by rw [k₂.mem, k₁.mem]; exact hI.mod
  have hx₂ : s₂.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [k₂.gpr _ (by decide), b₁]
  have hbits₂ : ∀ t < 4 * K.J, s₂.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by rw [k₂.mem]; exact hbits₁ t ht
  have hzW := combW_ro hL (x := K.zero) (by simp [combRo])
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [U₂.wordsVal hzW (by have := hL.lay.le K.zero (by comb_mem); omega), hF.zero]
  refine combEntry_ok hL hA hC hV hpn hs₂ hM₂ (i := j - 1) (by omega) hx₂ m₂ hbits₂ hz₂
    fun s₃ E₃ => ?_
  have U₃ : Unch base (combW K) s₀.mem s₃.mem := (U₂.trans E₃.unch).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact entryW_sub w hw
  have hM₃ : ModOk K.M size C.p s₃.mem base := hM₂.unch E₃.unch
    (fun w hw => hmoW w (entryW_sub w hw)) hn
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by
      have hxs : x ∈ combWs K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> comb_mem
      rw [E₃.unch.wordsVal (fun w hw => by
        have hnd := hL.nodup
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, not_or] at hnd
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact hL.apart₂ hxs (by comb_mem) (by grind)
        · exact hL.apart₂ hxs (by comb_mem) (by grind)
        · exact hL.apart₂ hxs (by comb_mem) (by grind)
        · exact hL.apart₂ hxs (by comb_mem) (by grind)
        · exact hL.lay.tmp x (combWs_slots K x hxs))
        (by have := hL.lay.le x (combWs_slots K x hxs); omega), k₂.mem, k₁.mem]
  have hro : ∀ x ∈ combRo K, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (combW_ro hL hx) (by
      have := hL.lay.le x (combRo_slots x hx); omega)
  have hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo])]; exact hF.ro_lt _ (by simp [combRo])
    · rw [hro _ (by simp [combRo])]; exact hF.ro_lt _ (by simp [combRo])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  refine WP.mono (combSum_ok hL hA hp E₃.scr hM₃ hlt₃) fun s₄ S₄ => ?_
  have tb : tmv C K.M.n base s₃ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [hro _ (by simp [combRo])]; exact hF.b
  have hRA : Rep C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
      (tmv C K.M.n base s₃ K.A.z) (mul (combE k K.J j) (G C)) := by
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ey : tmv C K.M.n base s₃ K.A.y = tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [hAx _ (by simp)]
    rw [ex, ey, ez]; exact hI.rep
  have hS := S₄.val
  rw [tb] at hS
  have hP := hC.onCurve_mul hG (combE k K.J j)
  have hQ : onCurve C (signedPt C k (j - 1)) = true := by
    unfold signedPt combPt
    split
    · exact hC.onCurve_mul hG _
    · exact onCurve_negPt (hC.onCurve_mul hG _)
  have hR := hC.add3 hM3 hP hQ hRA E₃.rep hS.symm
  have hadd := comb_add hC hG (k := k) (J := K.J) (j := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj] at hadd
  have hsp : signedPt C k (j - 1) = (if 8 ≤ nib k (j - 1) then combPt C (j - 1) (nib k (j - 1) - 8)
      else negPt (combPt C (j - 1) (8 - nib k (j - 1)))) := rfl
  rw [hsp, hadd] at hR
  have hx₄ : s₄.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [S₄.keep.gpr _ (x19_not_clob _), E₃.x19, hx₂]
  refine ⟨⟨S₄.scr, hx₄, ?_, (U₃.trans S₄.unch).mono fun w hw => ?_,
    hM₃.unch S₄.unch (combW_mo hL hM₃) hn, S₄.lt, hR⟩, hx₄⟩
  · refine ((((hI.keep.trans ((Keeps.regs k₁).mono ?_)).trans ((Keeps.regs k₂).mono ?_)).trans
      E₃.keep).trans (S₄.keep.mono fun r hr => ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | rfl | rfl | hr
      · exact combClob_mem (by simp)
      · exact combClob_mem (by simp)
      · simp [combClob]
      · exact combClob_mem (by simp)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))
  · rcases List.mem_append.mp hw with hw | hw <;> exact hw

/-- `[k]G` into `A`, for `k < 16^J` whose bits are the table at `K.bits`;
only `combClob` and `combW` change. -/
theorem comb_ok {K : CombCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true)
    (hV : CombVals K C) (hpn : C.p < 2 ^ (64 * K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOk K.M size C.p s.mem base) (hF : CombFixed K C base s k) (hk : k < 16 ^ K.J) :
    WP isa (comb K) s fun s' => KeepRegs (combClob K.M.n) s s' ∧ Unch base (combW K) s.mem s'.mem ∧
      ModOk K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hn := hs.nowrap
  have hJ := hL.J
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  have al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  have b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by grind)
  have axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by grind)
  have hmoW := combW_mo hL hM
  rw [comb]
  refine WP.seq ?_
  rw [init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok hs (n := K.M.n) (o := K.A.x) (x := K.start.1) (le _ (by comb_mem))
    (al _ (by comb_mem)) (Nat.lt_trans hV.start_lt.1 hpn)
  refine WP.mono W1 fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₁ (n := K.M.n) (o := K.A.y) (x := K.start.2) (le _ (by comb_mem))
    (al _ (by comb_mem)) (Nat.lt_trans hV.start_lt.2 hpn)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₂ (n := K.M.n) (o := K.A.z) (x := K.one) (le _ (by comb_mem))
    (al _ (by comb_mem)) (Nat.lt_trans hV.one_lt hpn)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (setCounter_ok s₃ (j := K.J) (by omega)) fun s₄ h₄ => ?_
  obtain ⟨b₄, k₄⟩ := h₄
  have U₄ : Unch base (combW K) s.mem s₄.mem := by
    rw [k₄.mem]
    refine (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => ?_
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have vx : wordsVal s₄.mem base K.A.x K.M.n = K.start.1 := by
    rw [k₄.mem, O₃.wordsVal axz (b64 _ (by comb_mem)), O₂.wordsVal axy (b64 _ (by comb_mem)), e₁]
  have vy : wordsVal s₄.mem base K.A.y K.M.n = K.start.2 := by
    rw [k₄.mem, O₃.wordsVal ayz (b64 _ (by comb_mem)), e₂]
  have vz : wordsVal s₄.mem base K.A.z K.M.n = K.one := by rw [k₄.mem, e₃]
  have I₄ : CombInv K C base size k s s₄ K.J := by
    refine ⟨hs₃.of_keeps k₄ (by decide), b₄, ?_, U₄, hM.unch U₄ hmoW hn, ?_, ?_⟩
    · have c1 : ∀ r ∈ [Reg.x1], r ∈ combClob K.M.n := fun r hr =>
        combClob_mem (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
      exact (((k₁.mono c1).trans (k₂.mono c1)).trans (k₃.mono c1)).trans
        ((Keeps.regs k₄).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                  simp [combClob]))
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hV.start_lt.1
      · rw [vy]; exact hV.start_lt.2
      · rw [vz]; exact hV.one_lt
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, hV.one, combE_top]
      exact hV.start
  exact countLoop_ok (Inv := fun j s' => CombInv K C base size k s s' j) (n := K.J) (by omega)
    (fun j s' h1 h2 hi => combStep_ok hL hA hp hC hM3 hG hV hpn hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, by rw [← combE_zero hk]; exact hi.rep⟩)
    hJ.1 I₄

end VG.Proof.Weierstrass.AArch64
