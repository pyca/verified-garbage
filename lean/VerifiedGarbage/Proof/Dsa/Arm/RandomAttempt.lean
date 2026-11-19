module

public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.Arm.RandomCopy
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! ### `Dsa.Arm.RandomSample`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.RandomDraw`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.RandomInRange`, which only this module used -/

section

/-!
# Whether a candidate is in range (32-bit ARM)

`inRange` compares the `width` candidate bytes at the draw's place in the
nonce with q's significant bytes, from their ends: `r3` is the borrow of
the candidate minus q (`randomBorrow`) and `r6` the OR of the candidate's
bytes. `rangeFinish` leaves `r3 = 1` exactly when the candidate is nonzero
and below q.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_ldrb op2_imm op2_reg op2_lsr eval_eq eval_ne
  ofNat_beq_zero toNat_shr)
open VG.Proof.Dsa (randomBorrow acceptsOf qSigOf toNat_setWidth8 setWidth8_ofNat borrow_bit)

/-- q's significant bytes. -/
abbrev qSig (s₀ : State) : List Byte := qSigOf (rQBytes s₀)

/-- Whether the candidate `cs` is accepted: nonzero and below q. -/
abbrev accepts (s₀ : State) (cs : List Byte) : Bool := acceptsOf (rQBytes s₀) cs

theorem qSig_length (s₀ : State) : (qSig s₀).length = rWidth s₀ := VG.Proof.Dsa.qSigOf_length _

theorem shr31 (y : BitVec 32) : (y >>> 31).toNat = if y.msb then 1 else 0 := by
  rw [toNat_shr, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ 31 ≤ y.toNat
  · simp only [h, decide_true, ↓reduceIte]; omega_using [h]
  · simp only [h, decide_false]; simp; omega_using [h]

/-- The sign bit of `-x ∣ x`: whether `x` is nonzero. -/
theorem nz_bit (x : BitVec 32) (h : x.toNat < 256) :
    ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases hx : x = 0
  · subst hx; rfl
  · have : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    simp only [hx, ↓reduceIte, show (0 : BitVec 32).toNat = 0 from rfl]
    obtain e : decide (2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat + 0) % 2 ^ 32) = true := decide_eq_true (by omega_using [h, this])
    rw [e, Bool.true_or]; rfl

theorem ofNat_add_one_sub {x : BitVec 32} {c : Nat} (hc : c + 1 < 2 ^ 32) :
    x + BitVec.ofNat 32 (c + 1) - 1 = x + BitVec.ofNat 32 c := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub32 _ (by omega_using []) hc]; rfl

abbrev rangeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6]

/-- The comparison after the last `width - k` bytes. -/
structure RangeInv (s₀ t₀ : State) (cs : List Byte) (k : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  mem : t.mem = t₀.mem
  r4 : t.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀ + k)
  r1 : t.gpr .r1 = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k)
  r2 : t.gpr .r2 = BitVec.ofNat 32 k
  r3 : t.gpr .r3 = BitVec.ofNat 32 (randomBorrow (cs.drop k) ((qSig s₀).drop k))
  r6 : (t.gpr .r6).toNat < 256
  r6z : t.gpr .r6 = 0 ↔ ∀ b ∈ cs.drop k, b = 0
  rest : Rest rangeRegs t₀ t

/-- One byte, from the end. -/
theorem rangeByte_ok {s₀ t₀ t : State} (A : RandomABI s₀) {cs : List Byte} {k : Nat}
    (hcs : cs.length = rWidth s₀) (hk : k < rWidth s₀)
    (hnonce : ∀ i < rWidth s₀, t₀.mem (off (rBase s₀) (drawPlace s₀ + i)) = cs.getD i 0)
    (I : RangeInv s₀ t₀ cs (k + 1) t) :
    WP isa (.block rangeByte) t fun u => RangeInv s₀ t₀ cs k u ∧ u.z = decide (k = 0) := by
  have hF : frameBytes = 112 := rfl
  have hon : oNonce = 64 := rfl
  obtain hql := rQBytes_le A
  obtain hfit := rWidth_le s₀
  obtain hdp := drawPlace_le A
  obtain hq := I.ready.q A
  have hqfit := hq.fit
  have hrf := I.ready.rf
  unfold rangeByte borrow
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun t₁ u₁ => wp_dp (op2_imm (by decide)) fun t₂ u₂ => ?_
  obtain e₂ : t₂.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀ + k) := by
    rw [u₂.other _ (by decide), u₁.gpr]
    show t.gpr .r4 - 1 = _
    rw [I.r4, show drawPlace s₀ + (k + 1) = drawPlace s₀ + k + 1 from rfl, ofNat_add_one_sub (by omega_using [hk, hon, hdp])]
  obtain s₂ : t₂.gpr .r1 = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k) := by
    rw [u₂.gpr, u₁.other _ (by decide)]
    show t.gpr .r1 - 1 = _
    rw [I.r1, show (rQBytes s₀).length - rWidth s₀ + (k + 1) = (rQBytes s₀).length - rWidth s₀ + k + 1 from rfl,
      ofNat_add_one_sub (by omega_using [hk, hql, hfit])]
  obtain r11₂ : t₂.gpr .r11 = t.gpr .r11 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain hn := hnonce k hk
  rw [← I.mem] at hn
  refine wp_ldrb (a := off (rBase s₀) (drawPlace s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, e₂]; exact hrf.ea (by omega_using [hk, hF, hon, hdp]))
    (by rw [u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact hrf.read (d := drawPlace s₀ + k) (n := 1) (by omega_using [hk, hF, hon, hdp])) fun t₃ u₃ => ?_
  rw [u₂.mem, u₁.mem, hn] at u₃
  refine wp_dp (op2_reg _ _) fun t₄ u₄ => ?_
  obtain hqi : (rQBytes s₀).length - rWidth s₀ + k < (rQBytes s₀).length := by omega_using [hk, hfit]
  refine wp_ldrb (a := State.addr (rQ s₀) + BitVec.ofNat 64 ((rQBytes s₀).length - rWidth s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, u₄.other _ (by decide), u₃.other _ (by decide), s₂, VG.Arm.addr_add (by omega_using [hk, hfit, hqfit])])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hq.rd _ hqi) fun t₅ u₅ => ?_
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq.val _ hqi] at u₅
  refine wp_dp (op2_reg _ _) fun t₆ u₆ => wp_dp (op2_reg _ _) fun t₇ u₇ => wp_mov (op2_lsr (by decide)) fun t₈ u₈ =>
    wp_mov (op2_reg _ _) fun t₉ u₉ => wp_dec fun t₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  -- The values.
  obtain hc := VG.Proof.Dsa.randomBorrow_le (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
  obtain hcs' : k < cs.length := by omega_using [hcs, hk]
  obtain hqs' : k < (qSig s₀).length := by rw [qSig_length]; omega_using [hk]
  obtain hqk : (qSig s₀)[k] = (rQBytes s₀)[(rQBytes s₀).length - rWidth s₀ + k] := by
    simp only [qSig, qSigOf, List.getElem_drop]
  obtain hdrop : ∀ (l : List Byte) (h : k < l.length), l.drop k = l[k] :: l.drop (k + 1) := fun l h => by
    rw [List.drop_eq_getElem_cons h]
  obtain hb : randomBorrow (cs.drop k) ((qSig s₀).drop k) =
      if (cs[k]).toNat < ((qSig s₀)[k]).toNat + randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
      then 1 else 0 := by
    rw [hdrop cs hcs', hdrop (qSig s₀) hqs', randomBorrow]
  obtain hcg : cs.getD k 0 = cs[k] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcs', Option.getD_some]
  obtain r0₇ : t₇.gpr .r0 = BitVec.ofNat 32 (cs[k]).toNat - BitVec.ofNat 32 (((qSig s₀)[k]).toNat +
      randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))) := by
    rw [u₇.gpr]
    show t₆.gpr .r0 - t₆.gpr .r5 = _
    rw [u₆.gpr, u₆.other .r0 (by decide)]
    show t₅.gpr .r0 - (t₅.gpr .r5 + t₅.gpr .r3) = _
    rw [u₅.gpr, u₅.other .r0 (by decide), u₅.other .r3 (by decide), u₄.other .r0 (by decide),
      u₄.other .r3 (by decide), u₃.gpr, u₃.other .r3 (by decide), u₂.other .r3 (by decide), u₁.other .r3 (by decide),
      I.r3, hcg, hqk, setWidth8_ofNat, setWidth8_ofNat, BitVec.ofNat_add_ofNat]
  obtain R : Rest rangeRegs t t₁₀ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
      ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
      ((u₉.rest (by decide)).trans (u₁₀.rest (by decide))))))))))
  obtain hm : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r6₁₀ : t₁₀.gpr .r6 = t.gpr .r6 ||| cs[k].setWidth 32 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    show t₃.gpr .r6 ||| t₃.gpr .r0 = _
    rw [u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hcg]
  refine ⟨⟨I.ready.congr R (by rw [hm]; exact Frame.refl _ _), hm.trans I.mem, ?_, ?_, ?_, ?_, ?_, ?_,
    I.rest.trans R⟩, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂,
      R.gpr .r11 (by decide)]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), s₂]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, r0₇, borrow_bit (BitVec.isLt _) (by omega_using [hc]), hb]
  · rw [r6₁₀, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 8) I.r6 (by rw [toNat_setWidth8]; exact BitVec.isLt _)
  · have key : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
    rw [r6₁₀, key, hdrop cs hcs', I.r6z, List.forall_mem_cons]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨?_, h₁⟩
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h₂
      rw [toNat_setWidth8] at this; exact this
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₂, by rw [h₁]; rfl⟩
  · rw [z₁₀, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel,
      ofNat_beq_zero (by omega_using [hk, hql, hfit])]

theorem rangeFinish_ok {s₀ t₀ t : State} {cs : List Byte} (hcs : cs.length = rWidth s₀)
    (I : RangeInv s₀ t₀ cs 0 t) :
    WP isa (.block rangeFinish) t fun u => u.gpr .r3 = (if accepts s₀ cs then 1 else 0) ∧
      u.z = !accepts s₀ cs ∧ u.mem = t₀.mem ∧ RReady s₀ u ∧ Rest rangeRegs t₀ u := by
  unfold rangeFinish
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_dp (op2_reg _ _) fun t₂ u₂ => wp_dp (op2_reg _ _) fun t₃ u₃ =>
    wp_mov (op2_lsr (by decide)) fun t₄ u₄ => wp_dp (op2_reg _ _) fun t₅ u₅ => wp_cmp0 fun t₆ f₆ z₆ =>
    WP.block_nil ?_
  obtain hb := VG.Proof.Dsa.randomBorrow_eq cs (qSig s₀) (by rw [hcs, qSig_length])
  obtain hz : (t.gpr .r6 = 0) ↔ Spec.Dsa.decodeBE cs = 0 := by
    rw [VG.Proof.Dsa.decodeBE_eq_zero]; simpa only [List.drop_zero] using I.r6z
  obtain r6 : t₂.gpr .r6 = t.gpr .r6 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain r0₄ : t₄.gpr .r0 = if t.gpr .r6 = 0 then 0 else 1 := by
    rw [u₄.gpr, u₃.gpr]
    show (t₂.gpr .r0 ||| t₂.gpr .r6) >>> 31 = _
    rw [u₂.gpr, r6]
    show ((t₁.gpr .r0 - t₁.gpr .r6) ||| t.gpr .r6) >>> 31 = _
    rw [u₁.gpr, u₁.other _ (by decide), nz_bit _ I.r6]
  obtain r3₅ : t₅.gpr .r3 = (if accepts s₀ cs then 1 else 0) := by
    rw [u₅.gpr]
    show t₄.gpr .r3 &&& t₄.gpr .r0 = _
    rw [r0₄, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), I.r3]
    simp only [List.drop_zero, hb, show (t.gpr .r6 = 0) = (Spec.Dsa.decodeBE cs = 0) from propext hz]
    unfold accepts acceptsOf
    by_cases hp : Spec.Dsa.decodeBE cs = 0 <;> by_cases hl : Spec.Dsa.decodeBE cs < Spec.Dsa.decodeBE (qSig s₀) <;>
      simp [hp, hl] <;> first | decide | omega
  obtain R : Rest rangeRegs t t₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (f₆.rest _)))))
  obtain hm : t₆.mem = t.mem := by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [f₆.gpr]; exact r3₅, ?_, hm.trans I.mem, I.ready.congr R (by rw [hm]; exact Frame.refl _ _),
    I.rest.trans R⟩
  rw [z₆, r3₅]
  cases accepts s₀ cs <;> rfl

/-- The comparison's pointers and count. -/
theorem rangeInit_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {cs : List Byte}
    (hq : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) (hcs : cs.length = rWidth s₀) :
    WP isa (.block rangeInit) t fun u => RangeInv s₀ t cs (rWidth s₀) u ∧ u.mem = t.mem := by
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit := rWidth_le s₀
  unfold rangeInit
  refine wp_dp (op2_imm (by decide)) fun t₁ u₁ => wp_ldArg A (h.upd u₁) (j := 2) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ld (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ u₄ =>
    wp_ld ((((h.upd u₁).upd u₂).upd u₃).upd u₄) (by decide) fun t₅ u₅ => wp_dp (op2_reg _ _) fun t₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun t₇ u₇ => wp_mov (op2_imm (by decide)) fun t₈ u₈ => WP.block_nil ?_
  obtain R : Rest rangeRegs t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    (u₈.rest (by decide))))))))
  obtain m₈ : t₈.mem = t.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hcsd : cs.drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by omega_using [hcs])
  obtain hqd : (qSig s₀).drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by rw [qSig_length])
  refine ⟨⟨h.congr R (by rw [m₈]; exact Frame.refl _ _), m₈, ?_, ?_, ?_, ?_, ?_, ?_, R⟩, m₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, R.gpr .r11 (by decide)]
    show t₂.gpr .r4 + t₂.gpr .r0 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show t.gpr .r11 + BitVec.ofNat 32 oNonce + stackArg s₀ 2 = _
    rw [show stackArg s₀ 2 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      Offset.add_add]
    unfold drawPlace; congr 2; omega_using [hfit]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    show t₅.gpr .r1 + t₅.gpr .r2 = _
    rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq, hw, Offset.add_add]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, hw]
  · rw [u₈.other _ (by decide), u₇.gpr, hcsd, hqd]; rfl
  · rw [u₈.gpr]; decide
  · rw [u₈.gpr, hcsd]; simp

theorem inRange_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {cs : List Byte}
    (hq : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hcs : cs.length = rWidth s₀) (hw1 : 1 ≤ rWidth s₀)
    (hnonce : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) = cs.getD i 0) :
    WP isa inRange t fun u => u.gpr .r3 = (if accepts s₀ cs then 1 else 0) ∧
      u.z = !accepts s₀ cs ∧ u.mem = t.mem ∧ RReady s₀ u ∧ Rest rangeRegs t u := by
  unfold inRange
  refine WP.seq (WP.mono (rangeInit_ok A h hq hw hcs) fun t₈ ⟨I₀, _⟩ => ?_)
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = k ∧ 1 ≤ k ∧ k ≤ rWidth s₀ ∧
      RangeInv s₀ t cs k u) (fun n u hu => ?_) (rWidth s₀) t₈ ⟨_, rfl, hw1, Nat.le_refl _, I₀⟩)
  obtain ⟨k, hn, hk1, hk, J⟩ := hu
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hk1]⟩
  refine WP.mono (rangeByte_ok A hcs (by omega_using [hk]) hnonce J) fun v ⟨J', z⟩ => ?_
  by_cases hj : j = 0
  · left
    subst hj
    exact ⟨by rw [eval_ne, z]; rfl, WP.mono (rangeFinish_ok hcs J') fun u ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false hj]; rfl, j, by omega_using [hn], j, rfl, by omega_using [hj], by omega_using [hk], J'⟩

end VG.Proof.Dsa.Arm

end

end


/-!
# One draw (32-bit ARM)

`draw` checks that the tape has a complete draw left (status 2 if not),
copies it into the nonce, consumes it, and either accepts it (status 1) or
spends a draw of the budget (status 0 once it is spent): the step of
`Spec.Dsa.Random.sample` (`draw_ok`). The sampler's state is `Smp`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

/-! ## The candidate -/

theorem rWidth_eq (s₀ : State) : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ :=
  VG.Proof.Dsa.random_drawBytes_scan _

theorem accepts_candidate {s₀ : State} {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    accepts s₀ (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      decide (0 < Spec.Dsa.Random.candidate (rq s₀) bs ∧ Spec.Dsa.Random.candidate (rq s₀) bs < rq s₀) :=
  VG.Proof.Dsa.accepts_candidate _ hl hpos

/-- The whole nonce, its padding and the candidate's bytes, encodes the candidate. -/
theorem nonce_encodes {s₀ : State} (A : RandomABI s₀) {m : Mem} {bs : List Byte}
    (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀)
    (hpad : ∀ i < (rQBytes s₀).length - rWidth s₀, m (off (rBase s₀) (oNonce + i)) = 0)
    (hc : ∀ i < rWidth s₀, m (off (rBase s₀) (drawPlace s₀ + i)) = copied bs (maskValue (rLead s₀).toNat) i) :
    Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length (Spec.Dsa.Random.candidate (rq s₀) bs) := by
  have hfit := rWidth_le s₀
  have hql := rQBytes_le A
  let cs := copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)
  let pad := (rQBytes s₀).length - rWidth s₀
  let padded := List.replicate pad (0 : Byte) ++ cs
  have hpLen : padded.length = (rQBytes s₀).length := by
    simp only [padded, cs, List.length_append, List.length_replicate, copiedList_length]; omega_arith
  have hpBytes : Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have he : off (rBase s₀) oNonce + BitVec.ofNat 64 i = off (rBase s₀) (oNonce + i) := by
        simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
      rw [he]
      by_cases hip : i < pad
      · rw [hpad i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := cs)
          (i := i) (by simpa only [List.length_replicate] using hip), List.getElem_replicate]
      · have hk : i - pad < rWidth s₀ := by simp only [hpLen] at hj; omega_arith
        rw [show oNonce + i = drawPlace s₀ + (i - pad) by unfold drawPlace; omega_arith, hc _ hk]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := cs) (i := i)
          (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip), List.length_replicate]
        simp only [cs, copiedList, List.getElem_map, List.getElem_range]
  rw [hpBytes, ← hpLen, ← VG.Proof.Dsa.copied_candidate _ hl hpos, ← VG.Proof.Dsa.decode_padding cs pad,
    VG.Proof.Dsa.encodeBE_decodeBE]

/-! ## The sampler's state -/

/-- The sampler's state. -/
structure Smp (s₀ : State) (used draws : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  q : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)
  width : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)
  mask : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used
  drawsW : slot t.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws
  pad : ∀ i < (rQBytes s₀).length - rWidth s₀, t.mem (off (rBase s₀) (oNonce + i)) = 0
  usedBound : used ≤ (rInput s₀).rand.length

/-- Where the sampler writes. -/
def sampleRanges : List (Nat × Nat) := [(oUsed, 4), (oDraws, 4), (oStatus, 4), (oNonce, 32)]

/-- The slots and bytes a draw changes. -/
abbrev drawRanges (s₀ : State) : List (Nat × Nat) :=
  [(oUsed, 4), (oDraws, 4), (oStatus, 4), (drawPlace s₀, rWidth s₀)]

/-- A memory change apart from the rest of the sampler's state. -/
theorem Smp.of {s₀ t u : State} (A : RandomABI s₀) {used draws used' draws' : Nat}
    (S : Smp s₀ used draws t) (hr : RReady s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = BitVec.ofNat 32 used')
    (hdw : slot u.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws')
    (hub : used' ≤ (rInput s₀).rand.length) : Smp s₀ used' draws' u := by
  obtain hfit := rWidth_le s₀
  obtain hql := rQBytes_le A
  obtain hd : ∀ d, oDraws + 4 ≤ d → d + 4 ≤ oStatus → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d :=
    fun d h₁ h₂ => slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold oDraws oStatus at *
      rcases hr with rfl | rfl | rfl | rfl
      · right; unfold oUsed; omega_arith
      · right; omega_arith
      · left; omega_arith
      · left; unfold drawPlace oNonce; omega_arith) (by unfold oStatus at h₂; omega_arith)
  refine ⟨hr, (hd _ (by decide) (by decide)).trans S.q, (hd _ (by decide) (by decide)).trans S.width,
    (hd _ (by decide) (by decide)).trans S.mask, hu, hdw, fun i hi => ?_, hub⟩
  rw [hm _ fun r hr => ?_]
  · exact S.pad i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [ofs_off0 _ (by unfold oNonce; omega_arith)]
  rcases hr with rfl | rfl | rfl | rfl
  · right; unfold oUsed oNonce; omega_arith
  · right; unfold oDraws oNonce; omega_arith
  · right; unfold oStatus oNonce; omega_arith
  · left; unfold drawPlace; omega_arith

theorem Smp.congr {s₀ t u : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : RReady s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = slot t.mem (rBase s₀) oUsed)
    (hdw : slot u.mem (rBase s₀) oDraws = slot t.mem (rBase s₀) oDraws) : Smp s₀ used draws u :=
  S.of A hr hm (hu.trans S.usedW) (hdw.trans S.drawsW) S.usedBound

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- Spend a draw of the budget. -/
theorem drawDec_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) :
    WP isa (.block [ld .r0 oDraws, .subs .r0 .r0 (.imm 1), st .r0 oDraws]) t fun u =>
      Rest [.r0] t u ∧ u.gpr .r0 = BitVec.ofNat 32 (draws - 1) ∧
      u.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) ∧ RReady s₀ u ∧
      u.z = decide (draws - 1 = 0) ∧ Smp s₀ used (draws - 1) u := by
  have h := S.ready
  refine wp_ld h (by decide) fun t₁ u₁ => wp_dec fun t₂ u₂ z₂ =>
    wp_stF ((h.upd u₁).upd u₂) (by decide) fun t₃ m₃ h₃ zz₃ _ => WP.block_nil ?_
  obtain v₂ : t₂.gpr .r0 = BitVec.ofNat 32 (draws - 1) := by rw [u₂.gpr, u₁.gpr, S.drawsW, ofNat_sub_one hd]
  obtain hm₃ : t₃.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) := by
    rw [m₃.mem, v₂, u₂.mem, u₁.mem]
  obtain S₃ : Smp s₀ used (draws - 1) t₃ :=
    S.of A h₃ (by rw [hm₃]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
      (by rw [hm₃, slot_write_self]) S.usedBound
  exact ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (m₃.rest _)), by rw [m₃.gpr, v₂], hm₃, h₃,
    by rw [zz₃, z₂, u₁.gpr, S.drawsW, ofNat_sub_one hd, ofNat_beq_zero (by omega_arith)], S₃⟩

/-- Accept, or spend a draw. -/
theorem drawFinish_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) {acc : Bool} (hz : t.z = !acc) :
    WP isa drawFinish t fun u => Rest [.r0] t u ∧ RReady s₀ u ∧
      Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧
      (acc → Smp s₀ used draws u ∧ slot u.mem (rBase s₀) oStatus = 1) ∧
      (acc = false → Smp s₀ used (draws - 1) u ∧
        slot u.mem (rBase s₀) oStatus = (if draws - 1 = 0 then 0 else slot t.mem (rBase s₀) oStatus)) := by
  have h := S.ready
  unfold drawFinish
  cases acc with
  | true =>
    refine WP.ite true (by rw [eval_ne, hz]; rfl)
      (fun _ => wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_) (fun e => Bool.noConfusion e)
    refine wp_st (h.upd u₁) (by decide) fun t₂ m₂ h₂ => WP.block_nil ?_
    obtain hm : t₂.mem = t.mem.writeW (off (rBase s₀) oStatus) (1 : BitVec 32) := by rw [m₂.mem, u₁.gpr, u₁.mem]
    refine ⟨(u₁.rest (by decide)).trans (m₂.rest _), h₂, by rw [hm]; exact store_outs _ _ _ (by decide),
      fun _ => ⟨S.congr A h₂ ?_ ?_ ?_, ?_⟩, fun e => Bool.noConfusion e⟩
    · rw [hm]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_self]
  | false =>
    refine WP.ite false (by rw [eval_ne, hz]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.seq (WP.mono (drawDec_ok A S hd hdb) fun t₃ ⟨k₃, v₃, hm₃, h₃, z₃, S₃⟩ => ?_)
    by_cases h0 : draws - 1 = 0
    · refine WP.ite true (by rw [eval_eq, z₃, decide_eq_true h0]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine wp_st h₃ (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
      obtain hm₄ : t₄.mem = t₃.mem.writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := by
        rw [m₄.mem, v₃, h0]; rfl
      refine ⟨k₃.trans (m₄.rest _), h₄, ?_, fun e => Bool.noConfusion e, fun _ => ⟨S₃.congr A h₄ ?_ ?_ ?_, ?_⟩⟩
      · rw [hm₄, hm₃]
        exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
      · rw [hm₄]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_self, h0]; rfl
    · refine WP.ite false (by rw [eval_eq, z₃, decide_eq_false h0]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨k₃, h₃, by rw [hm₃]; exact store_outs _ _ _ (by decide), fun e => Bool.noConfusion e,
        fun _ => ⟨S₃, ?_⟩⟩
      rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      simp only [h0, ↓reduceIte]

/-! ## The draw -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs d, n, op2`, and its carry: no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [reduceExec, ho, Option.map_some]) (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov d, op2`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [reduceExec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `adc d, n, op2`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [reduceExec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-- The specification's sampling from `used` on, with `draws` draws. -/
abbrev spl (s₀ : State) (draws used : Nat) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (rq s₀) draws ((rInput s₀).rand.drop used)

/-- A sampling `S` that started at `base` is the one from `used` on. -/
structure SampleRel (s₀ : State) (S : Spec.Dsa.Random.Sample) (base used draws : Nat) : Prop where
  scalarEq : S.scalar = (spl s₀ draws used).scalar
  usedEq : base + S.used = used + (spl s₀ draws used).used
  statusEq : VG.Proof.Dsa.Random.sampleStatus S = VG.Proof.Dsa.Random.sampleStatus (spl s₀ draws used)

/-- What a sampling `S` that started at `base` leaves. -/
structure SampleOut (s₀ : State) (base : Nat) (S : Spec.Dsa.Random.Sample) (u : State) : Prop where
  smp : ∃ d, Smp s₀ (base + S.used) d u
  status : slot u.mem (rBase s₀) oStatus = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus S)
  nonce : ∀ k, S.scalar = some k → Spec.Rsa.bytesAt u.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
    Spec.Dsa.encodeBE (rQBytes s₀).length k

theorem sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

abbrev sampleRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7]

/-- The tape's remaining bytes against the width. -/
theorem drawHead_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t) :
    WP isa (.block drawHead) t fun u => Smp s₀ used draws u ∧ u.mem = t.mem ∧
      Rest sampleRegs t u ∧ u.z = decide ((rInput s₀).rand.length - used < rWidth s₀) := by
  have h := S.ready
  have hub := S.usedBound
  obtain hfit := rWidth_le s₀
  obtain hql := rQBytes_le A
  obtain hrl : (rInput s₀).rand.length = (stackArg s₀ 6).toNat := by simp only [rInput, rBytes_length]
  obtain e6 : stackArg s₀ 6 = BitVec.ofNat 32 (rInput s₀).rand.length := by
    rw [hrl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold drawHead
  refine wp_ldArg A h (j := 6) (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ld (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ u₄ =>
    wp_subsC (op2_reg _ _) fun t₅ u₅ c₅ => wp_movC (op2_imm (by decide)) fun t₆ u₆ c₆ =>
    wp_adc (op2_imm (by decide)) fun t₇ u₇ => wp_cmp0 fun t₈ f₈ z₈ => WP.block_nil ?_
  obtain h₈ := ((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).fupd f₈)
  obtain R : Rest sampleRegs t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    (f₈.rest _)))))))
  obtain m₈ : t₈.mem = t.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r0₄ : t₄.gpr .r0 = BitVec.ofNat 32 ((rInput s₀).rand.length - used) := by
    rw [u₄.other _ (by decide), u₃.gpr]
    show t₂.gpr .r0 - t₂.gpr .r7 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, S.usedW, e6, sub_ofNat32 hub (by omega_arith)]
  obtain r7₄ : t₄.gpr .r7 = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, S.width]
  rw [r0₄, r7₄, toNat_imm (by omega_arith), toNat_imm (by omega_arith)] at c₅
  obtain r0₇ : t₇.gpr .r0 = if decide (rWidth s₀ ≤ (rInput s₀).rand.length - used) then 1 else 0 := by
    rw [u₇.gpr, u₆.gpr, c₆, c₅]
    split <;> rfl
  refine ⟨S.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈]), m₈, R, ?_⟩
  rw [z₈, r0₇]
  by_cases hs : (rInput s₀).rand.length - used < rWidth s₀
  · rw [decide_eq_false (by omega_arith), decide_eq_true hs]; rfl
  · rw [decide_eq_true (by omega_arith), decide_eq_false hs]; rfl

/-- Consume a complete draw. -/
theorem drawUsed_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) :
    WP isa (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed]) t
      fun u => Smp s₀ (used + rWidth s₀) draws u ∧
        u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) ∧
        Rest sampleRegs t u := by
  have h := S.ready
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_st (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  obtain v₃ : t₃.gpr .r0 = BitVec.ofNat 32 (used + rWidth s₀) := by
    rw [u₃.gpr]
    show t₂.gpr .r0 + t₂.gpr .r7 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, S.usedW, S.width, BitVec.ofNat_add]
  obtain hm₄ : t₄.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) := by
    rw [m₄.mem, v₃, u₃.mem, u₂.mem, u₁.mem]
  obtain o₄ : Outs (rBase s₀) [(oUsed, 4)] t.mem t₄.mem := by rw [hm₄]; exact store_outs _ _ _ (by decide)
  exact ⟨S.of A h₄ (o₄.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [drawRanges])
    (by rw [hm₄, slot_write_self]) (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.drawsW)
    hfull, hm₄, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans (m₄.rest _)))⟩

/-- The copy, apart from the rest of the sampler's state. -/
theorem drawCopy_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => Smp s₀ used draws u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Rest sampleRegs t u := by
  obtain hql := rQBytes_le A
  obtain hfit := rWidth_le s₀
  refine WP.mono (copy_ok A S.ready S.usedW S.width S.mask hfull hw1) fun t₄ ⟨h₄, hc₄, ho₄, k₄⟩ => ?_
  obtain o₄ : Outs (rBase s₀) (drawRanges s₀) t.mem t₄.mem :=
    Outs.of_outside ho₄ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
  obtain sl₄ : ∀ d, d + 4 ≤ oNonce → slot t₄.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd' =>
    slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace; omega_arith) (by unfold oNonce at hd'; omega_arith)
  exact ⟨S.congr A h₄ o₄ (sl₄ _ (by decide)) (sl₄ _ (by decide)), hc₄, ho₄, k₄.mono (by decide)⟩

/-- The nonce's bytes survive the store of `used`. -/
theorem drawUsed_bytes {s₀ : State} (A : RandomABI s₀) {t u : State} {used v : Nat}
    (hm : u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 v))
    (hc : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) :
    ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
  obtain hql := rQBytes_le A
  obtain hfit := rWidth_le s₀
  obtain o₇ : Outs (rBase s₀) [(oUsed, 4)] t.mem u.mem := by rw [hm]; exact store_outs _ _ _ (by decide)
  rw [o₇ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold drawPlace oNonce; omega_arith)]; right; unfold drawPlace oNonce oUsed; omega_arith]
  exact hc i hi

end VG.Proof.Dsa.Arm

end

end

/-!
# Sampling a nonce (32-bit ARM)

`draw_ok`: one draw is a step of `Spec.Dsa.Random.sample`, either the last
(a status other than 4, with what the sampling leaves, `SampleOut`) or a
rejection, after which the sampling continues from the next draw.
`sample_ok`: a budget of 128 draws is the specification's sampling.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

theorem draw_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) (hq : 1 < rq s₀)
    (hst : slot t.mem (rBase s₀) oStatus = 4) :
    WP isa draw t fun u => RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u ∧
      ((slot u.mem (rBase s₀) oStatus = 4 ∧ 2 ≤ draws ∧ Smp s₀ (used + rWidth s₀) (draws - 1) u ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleRel s₀ S' base (used + rWidth s₀) (draws - 1)) ∧
          (spl s₀ draws used).trace = 0 :: (spl s₀ (draws - 1) (used + rWidth s₀)).trace) ∨
        (slot u.mem (rBase s₀) oStatus ≠ 4 ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleOut s₀ base S' u) ∧
          ((spl s₀ draws used).trace.head? ≠ some 0 ∨ draws = 1))) := by
  have hF : frameBytes = 112 := rfl
  have hon : oNonce = 64 := rfl
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hw1 : 1 ≤ rWidth s₀ := Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1
  have h := S.ready
  have hub := S.usedBound
  obtain ⟨d', rfl⟩ : ∃ d', draws = d' + 1 := ⟨draws - 1, by omega_using [hd]⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hrlen : ((rInput s₀).rand.drop used).length = (rInput s₀).rand.length - used := List.length_drop
  unfold draw
  refine WP.seq (WP.mono (drawHead_ok A S) fun t₃ ⟨S₃, m₃, k₃, c₃⟩ => ?_)
  have h₃ := S₃.ready
  by_cases hshort : (rInput s₀).rand.length - used < rWidth s₀
  · -- The tape is short.
    refine WP.ite true (by rw [eval_eq, c₃, decide_eq_true hshort]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_mov (op2_imm (by decide)) fun t₄ u₄ => wp_st (h₃.upd u₄) (by decide) fun t₅ m₅ h₅ => WP.block_nil ?_
    have k₅ : Rest sampleRegs t t₅ := k₃.trans ((u₄.rest (by decide)).trans (m₅.rest _))
    have hm₅ : t₅.mem = t.mem.writeW (off (rBase s₀) oStatus) (2 : BitVec 32) := by rw [m₅.mem, u₄.gpr, u₄.mem, m₃]
    have S₅ : Smp s₀ used (d' + 1) t₅ := S.congr A h₅
      (by rw [hm₅]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
    have hspl : spl s₀ (d' + 1) used = ⟨none, 0, [2]⟩ :=
      VG.Proof.Dsa.Random.sample_short _ _ _ hq (by rw [hdw, hrlen]; exact hshort)
    refine ⟨h₅, by rw [hm₅]; exact store_outs _ _ _ (by decide), k₅, .inr ⟨?_, fun S' base R => ⟨?_, ?_, ?_⟩,
      .inl (by rw [hspl]; simp)⟩⟩
    · rw [hm₅, slot_write_self]; decide
    · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₅⟩
    · rw [hm₅, slot_write_self, R.statusEq, hspl]; rfl
    · intro k hk; rw [R.scalarEq, hspl] at hk; simp at hk
  · -- A complete draw.
    refine WP.ite false (by rw [eval_eq, c₃, decide_eq_false hshort]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    have hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length := by omega_using [hw1, hshort]
    have hdl := drawBytes_length hfull
    -- The copy.
    refine WP.seq (WP.mono (drawCopy_ok A S₃ hfull hw1) fun t₄ ⟨S₄, hc₄, ho₄, k₄⟩ => ?_)
    -- The consumption.
    refine WP.seq (WP.mono (drawUsed_ok A S₄ hfull) fun t₇ ⟨S₇, hm₇, k₇⟩ => ?_)
    have h₇ := S₇.ready
    have o₇ : Outs (rBase s₀) [(oUsed, 4)] t₄.mem t₇.mem := by rw [hm₇]; exact store_outs _ _ _ (by decide)
    have hc₇ := drawUsed_bytes A hm₇ hc₄
    -- The comparison.
    let cs := copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)
    refine WP.seq (WP.mono (inRange_ok A h₇ (cs := cs) S₇.q S₇.width (copiedList_length _ _ _) hw1
      fun i hi => by rw [copiedList_getD _ _ hi]; exact hc₇ i hi) fun t₈ ⟨_, z₈, m₈, h₈, k₈⟩ => ?_)
    have S₈ : Smp s₀ (used + rWidth s₀) (d' + 1) t₈ :=
      S₇.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈])
    have hacc : accepts s₀ cs = decide (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
        Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := accepts_candidate hdl hw1
    have htake : ((rInput s₀).rand.drop used).take (Spec.Dsa.Random.drawBytes (rq s₀)) = drawBytes s₀ used := by
      rw [hdw]
    refine WP.mono (drawFinish_ok A S₈ (by omega_using []) hdb z₈) fun u ⟨k₉, h₉, o₉, hT, hF'⟩ => ?_
    have outs : Outs (rBase s₀) sampleRanges t.mem u.mem := by
      have e₁ : Outs (rBase s₀) sampleRanges t.mem t₃.mem := by rw [m₃]; exact Outs.refl _ _ _
      have e₂ : Outs (rBase s₀) sampleRanges t₃.mem t₄.mem := fun x hx => ho₄ x (by
        have := hx (oNonce, 32) (by decide)
        unfold drawPlace at *; omega_using [hql, hfit, this])
      have e₃ : Outs (rBase s₀) sampleRanges t₄.mem t₇.mem := o₇.mono (by decide)
      have e₄ : Outs (rBase s₀) sampleRanges t₇.mem t₈.mem := by rw [m₈]; exact Outs.refl _ _ _
      exact (((e₁.trans e₂).trans e₃).trans e₄).trans (o₉.mono (by decide))
    have keeps : Rest sampleRegs t u :=
      (((k₃.trans k₄).trans k₇).trans (k₈.mono (by decide))).trans (k₉.mono (by decide))
    -- The nonce's bytes survive the stores of the slots.
    have hc₉ : ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
      have hle : ∀ r ∈ ([(oDraws, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
      rw [o₉ _ fun r hr => by
        have := hle r hr
        rw [ofs_off0 _ (by unfold drawPlace; omega_using [hon, hql, hfit, hi])]
        right; unfold drawPlace at *; omega_using [this], m₈]
      exact hc₇ i hi
    have st₈ : slot t₈.mem (rBase s₀) oStatus = 4 := by
      rw [m₈, hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
        slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace oStatus; omega) (by decide),
        m₃, hst]
    cases ha : accepts s₀ cs with
    | true =>
      obtain ⟨S₉, st₉⟩ := hT ha
      have hk : 0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀ := by
        rw [hacc] at ha; exact of_decide_eq_true ha
      have hspl : spl s₀ (d' + 1) used =
          ⟨some (Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used)), rWidth s₀, [1]⟩ := by
        rw [spl, VG.Proof.Dsa.Random.sample_accept _ _ _ hq (by rw [hdw, hrlen]; omega_using [hshort]) (by rw [htake]; exact hk),
          htake, hdw]
      refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; decide, fun S' base R => ⟨?_, ?_, ?_⟩,
        .inl (by rw [hspl]; simp)⟩⟩
      · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₉⟩
      · rw [st₉, R.statusEq, hspl]; rfl
      · intro k hk'
        rw [R.scalarEq, hspl] at hk'
        cases hk'
        exact nonce_encodes A hdl hw1 S₉.pad hc₉
    | false =>
      obtain ⟨S₉, st₉⟩ := hF' ha
      have hk : ¬ (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := by
        rw [hacc] at ha; exact of_decide_eq_false ha
      have hnext : ((rInput s₀).rand.drop used).drop (Spec.Dsa.Random.drawBytes (rq s₀)) =
          (rInput s₀).rand.drop (used + rWidth s₀) := by
        rw [List.drop_drop, hdw]
      have hspl : spl s₀ (d' + 1) used =
          { spl s₀ d' (used + rWidth s₀) with
            used := rWidth s₀ + (spl s₀ d' (used + rWidth s₀)).used,
            trace := 0 :: (spl s₀ d' (used + rWidth s₀)).trace } := by
        rw [spl, VG.Proof.Dsa.Random.sample_reject _ _ _ hq (by rw [hdw, hrlen]; omega_using [hshort]) (by rw [htake]; exact hk),
          hnext, hdw]
      have hstatus : VG.Proof.Dsa.Random.sampleStatus (spl s₀ (d' + 1) used) =
          VG.Proof.Dsa.Random.sampleStatus (spl s₀ d' (used + rWidth s₀)) := by
        rw [hspl]; exact VG.Proof.Dsa.Random.sampleStatus_reject _ _ _ _
      have rel : ∀ S' base, SampleRel s₀ S' base used (d' + 1) → SampleRel s₀ S' base (used + rWidth s₀) d' :=
        fun S' base R => ⟨by rw [R.scalarEq, hspl], by rw [R.usedEq, hspl]; dsimp only; omega_using [],
          R.statusEq.trans hstatus⟩
      by_cases h0 : d' = 0
      · subst h0
        refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; simp only [Nat.add_sub_cancel, ↓reduceIte]; decide,
          fun S' base R => ?_, .inr rfl⟩⟩
        have R' := rel S' base R
        have h0s : spl s₀ 0 (used + rWidth s₀) = ⟨none, 0, [3]⟩ := rfl
        refine ⟨⟨0, by rw [R'.usedEq, h0s]; exact S₉⟩, ?_, ?_⟩
        · rw [st₉, R'.statusEq, h0s]; simp only [Nat.add_sub_cancel, ↓reduceIte]; rfl
        · intro k hk'; rw [R'.scalarEq, h0s] at hk'; simp at hk'
      · refine ⟨h₉, outs, keeps, .inl ⟨?_, by omega_using [h0], by simpa using S₉, fun S' base R => by simpa using rel S' base R,
          by rw [hspl, Nat.add_sub_cancel]⟩⟩
        rw [st₉]; simp only [Nat.add_sub_cancel, h0, ↓reduceIte]; exact st₈

theorem Smp.mem {s₀ t u : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : RReady s₀ u) (hm : u.mem = t.mem) : Smp s₀ used draws u :=
  S.congr A hr (by rw [hm]; exact Outs.refl _ _ _) (by rw [hm]) (by rw [hm])

theorem SampleOut.mem {s₀ v u : State} (A : RandomABI s₀) {base : Nat} {S : Spec.Dsa.Random.Sample}
    (O : SampleOut s₀ base S v) (hr : RReady s₀ u) (hm : u.mem = v.mem) : SampleOut s₀ base S u :=
  ⟨let ⟨d, Sd⟩ := O.smp; ⟨d, Sd.mem A hr hm⟩, by rw [hm]; exact O.status, by rw [hm]; exact O.nonce⟩

/-- A new budget of 128 draws. -/
theorem sampleInit_ok {s₀ t : State} (A : RandomABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t) :
    WP isa (.block [.mov .r0 (.imm 128), st .r0 oDraws, .mov .r0 (.imm 4), st .r0 oStatus]) t
      fun u => Smp s₀ used 128 u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧
        Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧ Rest sampleRegs t u := by
  have h := S.ready
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_st (h.upd u₁) (by decide) fun t₂ m₂ h₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => wp_st (h₂.upd u₃) (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  have hm₄ : t₄.mem = (t.mem.writeW (off (rBase s₀) oDraws) (128 : BitVec 32)).writeW
      (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₄.mem, u₃.gpr, u₃.mem, m₂.mem, u₁.gpr, u₁.mem]
  have k₄ : Rest sampleRegs t t₄ :=
    (u₁.rest (by decide)).trans ((m₂.rest _).trans ((u₃.rest (by decide)).trans (m₄.rest _)))
  have o₄ : Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem t₄.mem := by
    rw [hm₄]; exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
  have S₄ : Smp s₀ used 128 t₄ := S.of A h₄ (o₄.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [drawRanges])
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
      slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]; rfl) S.usedBound
  have st₄ : slot t₄.mem (rBase s₀) oStatus = 4 := by rw [hm₄, slot_write_self]
  exact ⟨S₄, st₄, o₄, k₄⟩

theorem status_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 4 == 0) = decide (k = 4) := by
  by_cases h : k = 4
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega_using [hk, h, this]

theorem sample_ok {s₀ t : State} (A : RandomABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t)
    (hq : 1 < rq s₀) :
    WP isa sample t fun u => SampleOut s₀ used (spl s₀ 128 used) u ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used)) ∧
      RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u := by
  unfold sample
  refine WP.seq (WP.mono (sampleInit_ok A S) fun t₄ ⟨S₄, st₄, o₄, k₄⟩ => ?_)
  let S₀ := spl s₀ 128 used
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used', 1 ≤ n ∧ n ≤ 128 ∧
      Smp s₀ used' n u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧ SampleRel s₀ S₀ used used' n ∧
      Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u) (fun n u hu => ?_) 128 t₄
    ⟨used, by decide, by decide, S₄, st₄, ⟨rfl, rfl, rfl⟩, o₄.mono (by decide), k₄⟩)
  obtain ⟨used', hn1, hn, Sm, st, R, ou, ku⟩ := hu
  refine WP.seq (WP.mono (draw_ok A Sm hn1 hn hq st) fun v ⟨hv, ov, kv, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have kv₂ : Rest sampleRegs t v₂ := ((ku.trans kv).trans (uv₁.rest (by decide))).trans (fv₂.rest _)
  have ov₂ : Outs (rBase s₀) sampleRanges t.mem v₂.mem := by rw [mv₂]; exact ou.trans ov
  rcases hcase with ⟨stv, h2, Sv, rel, _⟩ | ⟨stv, out, _⟩
  · right
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, stv]; rfl, n - 1, by omega_using [hn1], used' + rWidth s₀, by omega_using [h2], by omega_using [hn],
      Sv.mem A hv₂ mv₂, by rw [mv₂]; exact stv, rel S₀ used R, ov₂, kv₂⟩
  · have O := out S₀ used R
    have hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
      have := sampleStatus_le S₀
      rw [O.status, status_beq (by omega_using [this]), decide_eq_false (by omega_using [this])]
    left
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, hz], ?_⟩
    refine wp_ld hv₂ (by decide) fun u uu => WP.block_nil ?_
    have hu : RReady s₀ u := hv₂.upd uu
    have mu : u.mem = v.mem := by rw [uu.mem, mv₂]
    refine ⟨O.mem A hu mu, by rw [uu.gpr, mv₂, O.status], hu, by rw [uu.mem]; exact ov₂,
      kv₂.trans (uu.rest (by decide))⟩

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomCall`, which this module and modules that import it used -/

section

/-!
# Calling the supplied-nonce signer (32-bit ARM)

`callArgs` loads the signer's register arguments and the seven words of its
stack arguments into `r0`–`r10` (`CallRegs`), and `callSigner` pushes those
words, as a frame of `r4`–`r11` below ours, and calls `vg_dsa_sign`
(a `Signer`, such as `Entry.operation true`) under its contract (`signArmWith`): it returns its
status in `r0` and writes `out` (`callSigner_ok`), changing only `out`,
`scratch` and the pushed words (`callWrites`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Arm.FrameStack (armStack belowA)

variable {umaal : Bool}

/-! ## The frame's saved words -/

/-- The callee-saved registers and the register arguments, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 9, slot m (rBase s₀) (4 * i) = s₀.gpr (savedRegs.getD i .r0)) ∧
    slot m (rBase s₀) oOut = s₀.gpr .r0 ∧ slot m (rBase s₀) oOutLen = s₀.gpr .r1 ∧
    slot m (rBase s₀) oUsedPtr = s₀.gpr .r2 ∧ slot m (rBase s₀) oKey = s₀.gpr .r3

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, d + 4 ≤ 36 ∨ 96 ≤ d → d + 4 ≤ 112 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨fun i hi => (he _ (.inl (by omega_using [hi])) (by omega_using [hi])).trans (h.1 i hi), (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.2.2⟩

/-- Memory changed only in ranges of `[36, 96)` keeps the saved words. -/
theorem Saved.of_outs {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)} (h : Saved s₀ m)
    (ho : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, 36 ≤ r.1 ∧ r.1 + r.2 ≤ 96) : Saved s₀ m' :=
  h.of_slots fun d hd hd' => slot_outs ho (fun r hr => by have := hrs r hr; omega_using [hd, this]) (by omega_using [hd'])

/-! ## The arguments -/

/-- The signer's arguments: `out`, `out_len`, `key`, `key_len` in `r0`–`r3`,
and `p_len`, `nonce`, `q_len`, `digest`, `digest_len`, `scratch`,
`scratch_len` in `r4`–`r10`. -/
structure CallRegs (s₀ u : State) : Prop where
  r0 : u.gpr .r0 = s₀.gpr .r0
  r1 : u.gpr .r1 = s₀.gpr .r1
  r2 : u.gpr .r2 = s₀.gpr .r3
  r3 : u.gpr .r3 = stackArg s₀ 0
  r4 : u.gpr .r4 = stackArg s₀ 1
  r5 : u.gpr .r5 = u.gpr .r11 + BitVec.ofNat 32 oNonce
  r6 : u.gpr .r6 = stackArg s₀ 2
  r7 : u.gpr .r7 = stackArg s₀ 3
  r8 : u.gpr .r8 = stackArg s₀ 4
  r9 : u.gpr .r9 = stackArg s₀ 7
  r10 : u.gpr .r10 = stackArg s₀ 8

abbrev callRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem callArgs_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block callArgs) t fun u => RReady s₀ u ∧ u.mem = t.mem ∧ CallRegs s₀ u ∧ Rest callRegs t u := by
  obtain ⟨-, s0, s1, -, s3⟩ := sv
  unfold callArgs
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_ld ((h.upd u₁).upd u₂) (by decide) fun t₃ u₃ =>
    wp_ldArg A (((h.upd u₁).upd u₂).upd u₃) (j := 0) (by decide) fun t₄ u₄ =>
    wp_ldArg A ((((h.upd u₁).upd u₂).upd u₃).upd u₄) (j := 1) (by decide) fun t₅ u₅ =>
    wp_dp (op2_imm (by decide)) fun t₆ u₆ =>
    wp_ldArg A ((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆) (j := 2) (by decide) fun t₇ u₇ =>
    wp_ldArg A (((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇) (j := 3) (by decide) fun t₈ u₈ =>
    wp_ldArg A ((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈) (j := 4) (by decide)
      fun t₉ u₉ =>
    wp_ldArg A (((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉) (j := 7)
      (by decide) fun t₁₀ u₁₀ =>
    wp_ldArg A ((((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀)
      (j := 8) (by decide) fun t₁₁ u₁₁ => WP.block_nil ?_
  have h₁₁ := (((((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀).upd u₁₁)
  have R : Rest callRegs t t₁₁ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
    (u₁₁.rest (by decide)))))))))))
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨h₁₁, by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, R⟩
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq,
      ↓reduceIte, u₁.gpr, s0]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, reduceCtorEq,
      ↓reduceIte, u₂.gpr, u₁.mem, s1]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq,
      ↓reduceIte, u₃.gpr, m₂, s3]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, reduceCtorEq, ↓reduceIte, u₄.gpr]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, reduceCtorEq, ↓reduceIte, u₅.gpr]
  · rw [R.gpr .r11 (by decide)]
    simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, reduceCtorEq, ↓reduceIte, u₆.gpr]
    show t₅.gpr .r11 + _ = _
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, reduceCtorEq, ↓reduceIte, u₇.gpr]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, reduceCtorEq, ↓reduceIte, u₈.gpr]
  · simp only [u₁₁.get, u₁₀.get, reduceCtorEq, ↓reduceIte, u₉.gpr]
  · simp only [u₁₁.get, reduceCtorEq, ↓reduceIte, u₁₀.gpr]
  · exact u₁₁.gpr

/-! ## The call -/

/-- The words the call pushes, as the signer's stack arguments. -/
abbrev callPush : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The nonce, in the frame. -/
abbrev nonceR (s₀ : State) : Region := ⟨off (rBase s₀) oNonce, (stackArg s₀ 2).toNat⟩

/-- The regions the signer is given, and where the call may write. -/
def callRd (s₀ : State) : List Region := [rKeyR s₀, nonceR s₀, rDigestR s₀, ⟨rLow s₀, 28⟩]
def callWr (s₀ : State) : List Region := [rOut s₀, rScratch s₀]
def callWrites (s₀ : State) : List Region := [rOut s₀, rScratch s₀, ⟨rLow s₀, 32⟩]

/-- The signer's entry state, from the state `u` before the push. -/
abbrev callEntryOf (s₀ u : State) : State := (pushed callPush u).callEntry.withRegions (callRd s₀) (callWr s₀)

/-- What the signer returns, from the bytes of the state `t` it is called in. -/
def callResult (s₀ t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (stackArg s₀ 1).toNat (stackArg s₀ 2).toNat
    (Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat)
    (Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat)
    (Spec.Rsa.bytesAt t.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat)

theorem rBytes_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

/-- Word `i` a push stored. -/
theorem storeWords_read : ∀ (vs : List (BitVec 32)) (m : Mem) (a : BitVec 32), a.toNat + 4 * vs.length ≤ 2 ^ 32 →
    ∀ i (hi : i < vs.length), (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i]
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | v :: vs, m, a, h, 0, _ => by
    simp only [List.length_cons] at h
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 ∨ vs.length = 0 := by omega_using [h]
    have hd : ∀ r ∈ [(⟨State.addr (a + 4), 4 * vs.length⟩ : Region)], Region.Disjoint ⟨State.addr a, 4⟩ r := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      rcases h4 with h4 | h4
      · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add h4]
        exact (Offset.disjoint_base _ (Nat.le_refl 4) (by have := VG.Proof.X25519.Arm.addr_toNat a; omega_using [h])).symm
      · rw [h4]; intro x _ h2; simp only [Region.Contains] at h2; omega_using [h2]
    rw [show 4 * 0 = 0 from rfl, BitVec.add_zero,
      (FrameStack.storeWords_frame vs (m.writeW (State.addr a) v) (a + 4) (by
        rcases h4 with h4 | h4
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]; omega_using [h]
        · rw [h4]; exact Nat.le_of_lt (BitVec.isLt _))).readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) hd (by decide), Mem.readW_writeW_self32]
    rfl
  | v :: vs, m, a, h, j + 1, hi => by
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 := by omega_using [h, hi]
    have ha : (a + 4).toNat = a.toNat + 4 := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]
    rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact storeWords_read vs _ (a + 4) (by omega_using [h, ha]) j (by omega_using [hi])

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u)
include A h

theorem call_sp_toNat : (u.sp - BitVec.ofNat 32 32).toNat = s₀.sp.toNat - 144 := by
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := s₀.sp.isLt
  unfold frameBytes; omega_arith

theorem call_sp : State.addr (u.sp - BitVec.ofNat 32 32) = rLow s₀ := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.addr_toNat, call_sp_toNat A h, rLow_toNat A]

/-- The signer's stack argument `i`: the pushed register. -/
theorem callEntry_arg {i : Nat} (hi : i < 8) : stackArg (callEntryOf s₀ u) i = u.gpr callPush[i] := by
  have hs := call_sp_toNat A h
  have hb := A.stackBound
  have := storeWords_read (callPush.map u.gpr) u.mem (u.sp - BitVec.ofNat 32 32)
    (by rw [List.length_map]; show (u.sp - BitVec.ofNat 32 32).toNat + 4 * 8 ≤ 2 ^ 32; omega_using [hs]) i
    (by rw [List.length_map]; exact hi)
  simpa only [List.getElem_map, stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp, pushed, List.length_cons, List.length_nil] using this

/-- The push changes memory only in its words. -/
theorem call_sp_le : 4 * callPush.length ≤ u.sp.toNat := by
  have := s₀.sp.isLt
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [callPush, List.length_cons, List.length_nil]
  unfold frameBytes; omega_using [this]

theorem call_push_frame : Frame [⟨rLow s₀, 32⟩] u.mem (pushed callPush u).mem := by
  have := FrameStack.pushed_frameA (rs := callPush) (s := u) (call_sp_le A h)
  rw [show 4 * callPush.length = 32 from rfl] at this
  simpa only [belowA, call_sp A h] using this

end

/-! ## The signer's precondition -/

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
include A h C

omit A h in
theorem ce_r0 : (callEntryOf s₀ u).gpr .r0 = s₀.gpr .r0 := (State.callEntry_gpr _ (by decide)).trans C.r0
omit A h in
theorem ce_r1 : (callEntryOf s₀ u).gpr .r1 = s₀.gpr .r1 := (State.callEntry_gpr _ (by decide)).trans C.r1
omit A h in
theorem ce_r2 : (callEntryOf s₀ u).gpr .r2 = s₀.gpr .r3 := (State.callEntry_gpr _ (by decide)).trans C.r2
omit A h in
theorem ce_r3 : (callEntryOf s₀ u).gpr .r3 = stackArg s₀ 0 := (State.callEntry_gpr _ (by decide)).trans C.r3
theorem ce_a0 : stackArg (callEntryOf s₀ u) 0 = stackArg s₀ 1 := (callEntry_arg A h (by decide)).trans C.r4
theorem ce_a1 : State.addr (stackArg (callEntryOf s₀ u) 1) = off (rBase s₀) oNonce := by
  rw [callEntry_arg A h (by decide)]
  show State.addr (u.gpr .r5) = _
  rw [C.r5]; exact h.rf.ea (by decide)
theorem ce_a2 : stackArg (callEntryOf s₀ u) 2 = stackArg s₀ 2 := (callEntry_arg A h (by decide)).trans C.r6
theorem ce_a3 : stackArg (callEntryOf s₀ u) 3 = stackArg s₀ 3 := (callEntry_arg A h (by decide)).trans C.r7
theorem ce_a4 : stackArg (callEntryOf s₀ u) 4 = stackArg s₀ 4 := (callEntry_arg A h (by decide)).trans C.r8
theorem ce_a5 : stackArg (callEntryOf s₀ u) 5 = stackArg s₀ 7 := (callEntry_arg A h (by decide)).trans C.r9
theorem ce_a6 : stackArg (callEntryOf s₀ u) 6 = stackArg s₀ 8 := (callEntry_arg A h (by decide)).trans C.r10

end

theorem nonce_sub {s₀ : State} (A : RandomABI s₀) : Region.Sub (nonceR s₀) (rStack s₀) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  rw [nonceR, rBase_off]; exact Offset.sub_base _ (by unfold oNonce; omega)

theorem low_sub (s₀ : State) {n : Nat} (hn : n ≤ 144) : Region.Sub (⟨rLow s₀, n⟩ : Region) (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 0) (n := n) (k := 144) (by omega_using [hn])
  rwa [BitVec.add_zero] at this

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
include A h C

theorem call_pre : signPre (callEntryOf s₀ u) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hsp : State.addr (callEntryOf s₀ u).sp = rLow s₀ := call_sp A h
  have hspn : (callEntryOf s₀ u).sp.toNat = s₀.sp.toNat - 144 := call_sp_toNat A h
  unfold signPre
  simp only [State.withRegions_rd, State.withRegions_wr, ce_r0 C, ce_r1 C, ce_r2 C, ce_r3 C,
    ce_a0 A h C, ce_a1 A h C, ce_a2 A h C, ce_a3 A h C, ce_a4 A h C, ce_a5 A h C, ce_a6 A h C, hsp, hspn]
  refine ⟨by have := A.stackLow; omega_using [], rfl, rfl, A.outKey, A.stackOut.symm.sub_right (nonce_sub A),
    A.outDigest, A.outScratch, A.stackOut.symm.sub_right (low_sub s₀ (by decide)), A.keyScratch,
    A.stackScratch.sub_left (nonce_sub A), A.digestScratch, A.stackScratch.symm.sub_right (low_sub s₀ (by decide)),
    A.outBound, A.keyBound, ?_, A.digestBound, A.scratchBound, A.lengths, A.outLength, A.keyLength, ?_⟩
  · show (stackArg (callEntryOf s₀ u) 1).toNat + _ ≤ _
    rw [← VG.Proof.X25519.Arm.addr_toNat, ce_a1 A h C, rBase_off, off_rLow_toNat A (by unfold oNonce; omega_using []),
      rLow_toNat A]
    have := A.stackLow; have := A.stackBound; unfold oNonce; omega
  · have := A.scratchLength; unfold Spec.Dsa.randomSignScratchWords at this; omega_using [this]

/-- The bytes the signer reads are those of `u`, which the push leaves. -/
theorem signRes_call : signRes (callEntryOf s₀ u) = callResult s₀ u := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hf := call_push_frame A h
  have e : ∀ {p : Addr} {n : Nat}, (rStack s₀).Disjoint ⟨p, n⟩ → n ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt (pushed callPush u).mem p n = Spec.Rsa.bytesAt u.mem p n := fun hd hn =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left (low_sub s₀ (by decide))).symm) hn
  unfold signRes callResult
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C, ce_a0 A h C, ce_a1 A h C,
    ce_a2 A h C, ce_a3 A h C, ce_a4 A h C]
  have en : Spec.Rsa.bytesAt (pushed callPush u).mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat =
      Spec.Rsa.bytesAt u.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat := by
    refine rBytes_frame hf (fun r hr => ?_) (by have := (stackArg s₀ 2).isLt; omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    rw [rBase_off]
    exact Offset.disjoint_base _ (by unfold oNonce; omega_using []) (by unfold oNonce; omega_using [])
  rw [e A.stackKey (by have := (stackArg s₀ 0).isLt; omega_using []), e A.stackDigest (by have := (stackArg s₀ 4).isLt; omega_using []),
    en]

omit C in
theorem call_covers :
    Covers (callRd s₀ ++ callWr s₀) ((pushed callPush u).rd ++ (pushed callPush u).wr) ∧
      Covers (callWr s₀) (pushed callPush u).wr := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hpw : (pushed callPush u).wr = ⟨rLow s₀, 32⟩ :: ⟨rBase s₀, frameBytes⟩ :: s₀.wr := by
    rw [pushed_wr, h.wr, show 4 * callPush.length = 32 from rfl, call_sp A h]
  have hpr : (pushed callPush u).rd = s₀.rd := by rw [pushed_rd, h.rd]
  have hw : Covers (callWr s₀) (pushed callPush u).wr := by
    rw [hpw, A.wr]; exact Covers.of_mem fun r hr => by
      simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) hw.right, hw⟩
  rw [hpr, hpw, A.rd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · refine ⟨⟨rBase s₀, frameBytes⟩, by simp, oNonce, rfl, ?_⟩
    show oNonce + (stackArg s₀ 2).toNat ≤ frameBytes
    unfold oNonce frameBytes; omega
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨rLow s₀, 32⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end

/-- The key's bytes, while the frame is allocated. -/
theorem callKey {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-- `vg_dsa_sign` uses no stack of its own. -/
theorem sign_armStack : armStack (Entry.operation umaal true) = 0 := by cases umaal <;> decide +kernel

open VG.Spec.Rsa (bytesAt) in
/-- `signArm` under an extra precondition `valid` on the exact packed key
bytes: with `fun _ _ _ => true` it is `signArm`, with
`validatePrivateKeyBytes` the contract of a signing attempt for a validated
private key. -/
def signArmWith (valid : Nat → Nat → List Byte → Bool) : Contract isa where
  pre s := signPre s ∧
    valid (arg s 0).toNat (arg s 2).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = true
  post := signArm.post
  pub := signArm.pub

/-- A supplied-nonce signer the randomized wrapper calls: the fully checked
signer (`valid` always true), or the signer for a validated private key
(`valid` is `validatePrivateKeyBytes`). -/
structure Signer where
  code : Prog isa
  valid : Nat → Nat → List Byte → Bool
  correct : ∀ s, (signArmWith valid).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ signArm.post s s'
  constantTime : ConstantTime isa (signArmWith valid).pre signArm.pub code
  stack : armStack code = 0

/-- The signer's validity of the wrapper's key. -/
def RValid (S : Signer) (s₀ : State) : Prop :=
  S.valid (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key = true

/-- The key the signer reads at its entry is the wrapper's. -/
theorem entry_key {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u) :
    Spec.Rsa.bytesAt (callEntryOf s₀ u).mem (State.addr ((callEntryOf s₀ u).gpr .r2))
      ((callEntryOf s₀ u).gpr .r3).toNat = (rInput s₀).key := by
  have hql := rQBytes_le A
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C]
  rw [rBytes_frame (call_push_frame A h) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
      (by have := (stackArg s₀ 0).isLt; omega_using []), callKey A h]

/-- The signer's contract at the wrapper's call, for a key it accepts. -/
theorem call_pre_with (S : Signer) {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
    (V : RValid S s₀) : (signArmWith S.valid).pre (callEntryOf s₀ u) := by
  refine ⟨call_pre A h C, ?_⟩
  show S.valid (stackArg (callEntryOf s₀ u) 0).toNat (stackArg (callEntryOf s₀ u) 2).toNat _ = true
  rw [entry_key A h C, ce_a0 A h C, ce_a2 A h C]
  exact V

theorem status_lt (r : Option (List Byte)) : Spec.Dsa.signStatus r < 2 := by
  unfold Spec.Dsa.signStatus; split <;> decide

/-- The call of the signer, its stack arguments pushed. -/
theorem callSigner_ok (S : Signer) {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
    (V : RValid S s₀) (name : String) :
    WP isa (callSigner name S.code) u fun v => RReady s₀ v ∧ Frame (callWrites s₀) u.mem v.mem ∧
      (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], v.gpr r = u.gpr r) ∧
      v.gpr .r0 = BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ u)) ∧
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (callResult s₀ u).getD (List.replicate (s₀.gpr .r1).toNat 0) := by
  obtain ⟨hc, hcw⟩ := call_covers A h
  unfold callSigner
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (call_sp_le A h) (by decide) ?_
  refine FrameStack.WP.callF (k := signArmWith S.valid) (fun s hs => S.correct s hs) (call_pre_with S A h C V)
    hc hcw (by rw [S.stack]; exact Nat.zero_le _) fun s' hrd hwr hsp hf hpres hpost => ?_
  rw [S.stack] at hf
  intro lm lu hfl
  have hpu : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = u.gpr r := fun r hr hl => by rw [hpres r hr hl, pushed_gpr]
  -- Where the call wrote.
  have Fc : Frame (callWrites s₀) u.mem s'.mem := by
    refine ((call_push_frame A h).mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; simp [callWrites]
    · simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp [callWrites], fun _ h => h⟩
      · exact ⟨_, by simp [callWrites], fun _ h => h⟩
      · exact ⟨⟨rLow s₀, 32⟩, by simp [callWrites], fun _ hc => absurd hc (by simp [Region.Contains])⟩
  have hfl' : Frame [⟨rLow s₀, 32⟩] s'.mem lm := by
    rw [show 4 * callPush.length = 32 from rfl, call_sp A h] at hfl; exact hfl
  have FcL : Frame (callWrites s₀) u.mem lm :=
    Fc.trans (hfl'.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [callWrites])
  have hspv : s'.sp + BitVec.ofNat 32 (4 * callPush.length) = u.sp := by
    rw [hsp, pushed_sp, BitVec.sub_add_cancel]
  have hv : RReady s₀ { popped .r4 (4 * callPush.length) s' with mem := lm, unknowns := lu } := by
    refine ⟨⟨?_, ?_, ?_, h.rf.nowrap⟩, ?_, ?_, ?_, ?_⟩
    · dsimp only; rw [popped_gpr (by decide), hpu .r11 (by decide) (by decide)]; exact h.rf.base
    · dsimp only; rw [popped_wr, hwr, pushed_wr, List.tail_cons]; exact h.rf.wr
    · dsimp only; rw [popped_rd, hrd, pushed_rd]; exact h.rf.args
    · dsimp only; rw [popped_sp, hspv]; exact h.sp
    · dsimp only; rw [popped_rd, hrd, pushed_rd]; exact h.rd
    · dsimp only; rw [popped_wr, hwr, pushed_wr, List.tail_cons]; exact h.wr
    · dsimp only
      refine h.frame.trans (FcL.sub fun r hr => ?_)
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp [rWrites], fun _ h => h⟩
      · exact ⟨_, by simp [rWrites], fun _ h => h⟩
      · exact ⟨rStack s₀, by simp [rWrites], low_sub s₀ (by decide)⟩
  obtain ⟨hr, hb⟩ := hpost
  rw [State.withRegions_gpr, BitVec.setWidth_append_eq_right, signRes_call A h C] at hr
  rw [State.withRegions_mem, ce_r0 C, ce_r1 C, signRes_call A h C] at hb
  refine ⟨hv, by dsimp only; exact FcL, fun r hr' => ?_, ?_, by
    dsimp only
    rw [rBytes_frame hfl' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm.sub_right (low_sub s₀ (by decide)))
      (by have := (s₀.gpr .r1).isLt; omega_using [])]
    exact hb⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> exact (popped_gpr (by decide) _ _).trans (hpu _ (by decide) (by decide))
  · dsimp only; rw [popped_gpr (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [hr, toNat_imm (by have := status_lt (callResult s₀ u); omega_using [hr])]

end VG.Proof.Dsa.Arm

end

end

/-!
# One signing attempt (32-bit ARM)

`attempt` samples a nonce and, if one is accepted, calls the signer with it
and records its status, spending an attempt on a zero result: a step of
`Spec.Dsa.randomSignLoop` (`attempt_ok`). Between attempts the state is
`Att`, after them `Done`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-! ## Between and after the attempts -/

/-- The spec's signing from `used` on, with `fuel` attempts left, gives the
overall result. -/
abbrev RRel (s₀ : State) (used fuel : Nat) : Prop :=
  VG.Proof.Dsa.RandomSignResultRel (rInput s₀) 0 (rResult s₀) used fuel

/-- Between attempts. -/
structure Att (s₀ : State) (used fuel : Nat) (t : State) : Prop where
  smp : ∃ d, Smp s₀ used d t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 fuel
  saved : Saved s₀ t.mem
  rel : RRel s₀ used fuel

/-- After the attempts. -/
structure Done (s₀ : State) (t : State) : Prop where
  smp : ∃ d, Smp s₀ (rResult s₀).used d t
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).signature.getD (List.replicate (s₀.gpr .r1).toNat 0)
  saved : Saved s₀ t.mem

/-! ## What the call keeps -/

/-- The frame is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₂ : d < frameBytes) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  have hF : frameBytes = 112 := rfl
  rw [rBase_off]
  have hs : (rStack s₀).Contains (off (rLow s₀) (32 + d)) 1 := Offset.contains_base _ (by omega_using [h₂, hF]) (by omega_using [h₂, hF])
  refine hf _ fun r hr => ?_
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut _ hs
  · exact A.stackScratch _ hs
  · exact (Offset.disjoint_base (rLow s₀) (d := 32 + d) (n := 1) (k := 32) (by omega_using []) (by omega_using [h₂, hF])) _
      (Region.contains_self _ _)

theorem call_frame_slot {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₂ : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega_using [h₂, hi])

/-- The call keeps the sampler's state. -/
theorem Smp.after_call {s₀ t u : State} (A : RandomABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : RReady s₀ u) (hf : Frame (callWrites s₀) t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, S.usedBound⟩
  · rw [call_frame_slot A hf (by decide)]; exact S.q
  · rw [call_frame_slot A hf (by decide)]; exact S.width
  · rw [call_frame_slot A hf (by decide)]; exact S.mask
  · rw [call_frame_slot A hf (by decide)]; exact S.usedW
  · rw [call_frame_slot A hf (by decide)]; exact S.drawsW
  · rw [call_frame_byte A hf (by unfold oNonce frameBytes; omega_using [hql, hi])]; exact S.pad i hi

theorem Saved.after_call {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (sv : Saved s₀ m)
    (hf : Frame (callWrites s₀) m m') : Saved s₀ m' :=
  sv.of_slots fun _ _ hd => call_frame_slot A hf hd

/-! ## The status -/

/-- Record the signer's status `st`, and test it. -/
theorem finHead_ok {s₀ u : State} (h : RReady s₀ u) {k : Nat} (hst : k ≤ 1)
    (he : u.gpr .r0 = BitVec.ofNat 32 k) :
    WP isa (.block [st .r0 oStatus, .cmp .r0 (.imm 0)]) u fun v => RReady s₀ v ∧
      Rest [] u v ∧ v.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 k) ∧
      v.z = decide (k = 0) := by
  refine wp_st h (by decide) fun v₁ m₁ h₁ => wp_cmp0 fun v₂ f₂ z₂ => WP.block_nil ?_
  refine ⟨h₁.fupd f₂, (m₁.rest _).trans (f₂.rest _), by rw [f₂.mem, m₁.mem, he], ?_⟩
  rw [z₂, m₁.gpr, he, ofNat_beq_zero (by omega_using [hst])]

/-- Spend an attempt. -/
theorem finDec_ok {s₀ v₂ : State} (h₂ : RReady s₀ v₂) {f : Nat}
    (ha : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) (hf : f + 1 ≤ 8) :
    WP isa (.block [ld .r0 oAttempts, .subs .r0 .r0 (.imm 1), st .r0 oAttempts]) v₂
      fun v₅ => RReady s₀ v₅ ∧ Rest [.r0] v₂ v₅ ∧
        v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) ∧ v₅.z = decide (f = 0) := by
  refine wp_ld h₂ (by decide) fun v₃ u₃ => wp_dec fun v₄ u₄ z₄ =>
    wp_stF ((h₂.upd u₃).upd u₄) (by decide) fun v₅ m₅ h₅ zz₅ _ => WP.block_nil ?_
  have e₄ : v₄.gpr .r0 = BitVec.ofNat 32 f := by rw [u₄.gpr, u₃.gpr, ha, ofNat_sub_one (by omega_using [])]; rfl
  refine ⟨h₅, (u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (m₅.rest _)), by
    rw [m₅.mem, e₄, u₄.mem, u₃.mem], ?_⟩
  rw [zz₅, z₄, u₃.gpr, ha, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel, ofNat_beq_zero (by omega_using [hf])]

/-- Record the signer's status `st`, and spend an attempt on a failure. -/
theorem callFinish_ok {s₀ u : State} (h : RReady s₀ u) {k f : Nat} (hst : k ≤ 1)
    (he : u.gpr .r0 = BitVec.ofNat 32 k) (ha : slot u.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1))
    (hf : f + 1 ≤ 8) :
    WP isa callFinish u fun v => RReady s₀ v ∧ Rest [.r0] u v ∧
      Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v.mem ∧
      (k = 1 → slot v.mem (rBase s₀) oStatus = 1 ∧ slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) ∧
      (k = 0 → slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 f ∧
        slot v.mem (rBase s₀) oStatus = (if f = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (finHead_ok h hst he) fun v₂ ⟨h₂, k₂, m₂, z₂⟩ => ?_)
  have o₂ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₂.mem := by
    rw [m₂]; exact store_outs _ _ _ (by decide)
  by_cases h0 : k = 0
  · subst h0
    refine WP.ite true (by rw [eval_eq, z₂]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e)
    have ha₂ : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha
    refine WP.seq (WP.mono (finDec_ok h₂ ha₂ hf) fun v₅ ⟨h₅, k₅', hm₅, z₅⟩ => ?_)
    have k₅ : Rest [.r0] u v₅ := (k₂.mono (by decide)).trans k₅'
    have o₅ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₅.mem := by
      rw [hm₅]; exact o₂.trans (store_outs _ _ _ (by decide))
    by_cases hf0 : f = 0
    · refine WP.ite false (by rw [eval_ne, z₅, decide_eq_true hf0]; rfl)
        (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨h₅, k₅, o₅, fun e => absurd e (by decide), fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₅, slot_write_self]
      · rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide), m₂, slot_write_self, hf0]; rfl
    · refine WP.ite true (by rw [eval_ne, z₅, decide_eq_false hf0]; rfl)
        (fun _ => wp_mov (op2_imm (by decide)) fun v₆ u₆ => wp_st (h₅.upd u₆) (by decide)
          fun v₇ m₇ h₇ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      have hm₇ : v₇.mem = v₅.mem.writeW (off (rBase s₀) oStatus) (4 : BitVec 32) := by
        rw [m₇.mem, u₆.gpr, u₆.mem]
      refine ⟨h₇, k₅.trans ((u₆.rest (by decide)).trans (m₇.rest _)),
        by rw [hm₇]; exact o₅.trans (store_outs _ _ _ (by decide)), fun e => absurd e (by decide),
        fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide), hm₅, slot_write_self]
      · rw [hm₇, slot_write_self]; simp only [hf0, ↓reduceIte]
  · have h1 : k = 1 := by omega_using [hst, h0]
    subst h1
    refine WP.ite false (by rw [eval_eq, z₂]; rfl) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
    refine ⟨h₂, k₂.mono (by decide), o₂, fun _ => ⟨?_, ?_⟩, fun e => absurd e (by decide)⟩
    · rw [m₂, slot_write_self]; rfl
    · rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha

/-- Slot stores keep the sampler's state. -/
theorem Smp.after_finish {s₀ t u : State} (A : RandomABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : RReady s₀ u) (hm : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hs : ∀ d, d ≤ 112 → (d + 4 ≤ oAttempts ∨ oAttempts + 4 ≤ d) → (d + 4 ≤ oStatus ∨ oStatus + 4 ≤ d) →
      slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₀ h₁ h₂ =>
    slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂) (by omega_using [h₀])
  refine ⟨hr, (hs _ (by decide) (by decide) (by decide)).trans S.q,
    (hs _ (by decide) (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  have hle : ∀ r ∈ ([(oAttempts, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
  rw [hm _ fun r hr => by
    have := hle r hr
    rw [ofs_off0 _ (by unfold oNonce; omega_using [hql, hi])]
    right; omega_using [this]]
  exact S.pad i hi

/-- Stores to the frame keep bytes apart from the stack. -/
theorem frameOuts_bytes {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (hm : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ frameBytes) {p : Addr} {n : Nat}
    (hd : (rStack s₀).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  refine hm _ fun r hr => ?_
  have hb := hrs r hr
  unfold frameBytes at hb
  by_cases hx : ofs (rBase s₀) (p + BitVec.ofNat 64 i) < 112
  · exfalso
    refine hd _ ?_ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_using [hi]) (by omega_using [hn, hi]))
    have he : p + BitVec.ofNat 64 i = off (rBase s₀) (ofs (rBase s₀) (p + BitVec.ofNat 64 i)) := by
      simp only [ofs, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm (rBase s₀), BitVec.sub_add_cancel]
    rw [he, rBase_off]
    exact Offset.contains_base _ (by omega_using [hx]) (by omega_using [hx])
  · right; omega_using [hb, hx]

/-- The signer's input is the specification's, with the sampled nonce. -/
theorem callResult_eq {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length k) :
    callResult s₀ t = Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest := by
  have hqn := rQBytes_length A
  have hkey := callKey A h
  have hdig : Spec.Rsa.bytesAt t.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat = (rInput s₀).digest := by
    refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.stackDigest.symm
    · exact A.outDigest.symm
    · exact A.digestScratch
    · exact A.usedDigest.symm
  have hnon : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat =
      Spec.Dsa.encodeBE (rInput s₀).qLen k := by
    rw [← hqn, hn, hqn]; rfl
  unfold callResult
  rw [hkey, hdig, hnon]; rfl

/-- Slots below the ranges that changed. -/
theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

theorem one_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 1 == 0) = decide (k = 1) := by
  by_cases h : k = 1
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega_using [hk, h, this]

/-- What an attempt from `used` with `f + 1` attempts left leaves: another
attempt to make after a retry, which its signing trace records, or the result. -/
def AttemptOut (s₀ : State) (used f : Nat) (u : State) : Prop :=
  (slot u.mem (rBase s₀) oStatus = 4 ∧ 1 ≤ f ∧ Att s₀ (used + (spl s₀ 128 used).used) f u ∧
    VG.Proof.Dsa.randomSigningTrace (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace =
      6 :: (VG.Proof.Dsa.randomSignRemaining (rInput s₀) (used + (spl s₀ 128 used).used) f).trace) ∨
    (slot u.mem (rBase s₀) oStatus ≠ 4 ∧ Done s₀ u ∧
      ¬ ((VG.Proof.Dsa.randomSigningTrace
        (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace).head? = some 6 ∧ 1 ≤ f))

theorem attempt_ok (S : Signer) (name : String) {s₀ t : State} (A : RandomABI s₀) {used f : Nat}
    (T : Att s₀ used (f + 1) t) (hf : f + 1 ≤ 8) (hq : 1 < rq s₀) (V : RValid S s₀) :
    WP isa (attempt name S.code) t fun u => AttemptOut s₀ used f u := by
  have hql := rQBytes_le A
  obtain ⟨d₀, Sm⟩ := T.smp
  unfold attempt
  refine WP.seq (WP.mono (sample_ok A Sm hq) fun u₁ ⟨O, r0₁, h₁, o₁, _⟩ => ?_)
  have sv₁ : Saved s₀ u₁.mem := T.saved.of_outs o₁ (by decide)
  have at₁ : slot u₁.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) :=
    (slot_outs o₁ (by decide) (by decide)).trans T.attempts
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u₂ fv₂ z₂ => WP.block_nil ?_)
  have h₂ := h₁.fupd fv₂
  have m₂ : u₂.mem = u₁.mem := fv₂.mem
  have hle := sampleStatus_le (spl s₀ 128 used)
  rw [r0₁, one_beq (by omega_using [hle])] at z₂
  cases hsc : (spl s₀ 128 used).scalar with
  | none =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]; split <;> simp
    refine WP.ite false (by rw [eval_eq, z₂, decide_eq_false hst]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    obtain ⟨-, hstat, hused⟩ := T.rel.sample_none hsc
    obtain ⟨d', S'⟩ := O.smp
    refine .inr ⟨?_, ⟨⟨d', ?_⟩, ?_, fun e => absurd (hstat ▸ e) hst, (by rw [m₂]; exact sv₁)⟩,
      by rw [VG.Proof.Dsa.random_sign_trace_none _ _ _ hsc]; simp⟩
    · rw [m₂, O.status]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_imm (by omega_using [hle])] at this
      exact absurd this (by show _ ≠ 4; omega_using [hle])
    · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
      rw [e]; exact S'.mem A h₂ m₂
    · rw [m₂, O.status]; exact congrArg (BitVec.ofNat 32) hstat.symm
  | some k =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]
    refine WP.ite true (by rw [eval_eq, z₂, decide_eq_true hst]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    obtain ⟨d', S'⟩ := O.smp
    have S₂ := S'.mem A h₂ m₂
    refine WP.seq (WP.mono (callArgs_ok A h₂ (by rw [m₂]; exact sv₁)) fun u₃ ⟨h₃, m₃, C₃, _⟩ => ?_)
    have hk : Spec.Rsa.bytesAt u₃.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
        Spec.Dsa.encodeBE (rQBytes s₀).length k := by
      rw [m₃, m₂]; exact O.nonce k hsc
    have hres := callResult_eq A h₃ hk
    refine WP.seq (WP.mono (callSigner_ok S A h₃ C₃ V name) fun u₄ ⟨h₄, f₄, _, r0₄, out₄⟩ => ?_)
    have at₄ : slot u₄.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [call_frame_slot A f₄ (by decide), m₃, m₂]; exact at₁
    have S₄ := (S₂.mem A h₃ m₃).after_call A h₄ f₄
    have sv₄ : Saved s₀ u₄.mem := Saved.after_call A (by rw [m₃, m₂]; exact sv₁) f₄
    rw [hres] at r0₄ out₄
    refine WP.mono (callFinish_ok h₄ (Nat.le_of_lt_succ (status_lt _)) r0₄ at₄ hf)
      fun u₅ ⟨h₅, _, o₅, hT1, hT0⟩ => ?_
    have S₅ := S₄.after_finish A h₅ o₅
    have sv₅ : Saved s₀ u₅.mem := sv₄.of_outs o₅ (by decide)
    cases hsb : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
    | some sig =>
      obtain ⟨st₅, -⟩ := hT1 (by rw [hsb]; rfl)
      obtain ⟨hsig, hstat, hused⟩ := T.rel.success hsc hsb
      refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun _ => ?_, sv₅⟩,
        by rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hsc hsb]; simp⟩
      · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · rw [frameOuts_bytes o₅ (by decide) A.stackOut (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
          (by decide))), out₄, hsb, hsig]
    | none =>
      obtain ⟨at₅, st₅⟩ := hT0 (by rw [hsb]; rfl)
      have R' := T.rel.retry hsc hsb
      by_cases hf0 : f = 0
      · subst hf0
        obtain ⟨-, hstat, hused⟩ := R'.exhausted
        refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun e => absurd e (by omega_using [hstat]), sv₅⟩,
          fun h => absurd h.2 (by decide)⟩
        have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · refine .inl ⟨by rw [st₅]; simp only [hf0, ↓reduceIte], by omega_using [hf0], ⟨⟨d', S₅⟩, at₅, sv₅, R'⟩,
          ?_⟩
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega_using [hf0]⟩
        exact VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hsc hsb

end VG.Proof.Dsa.Arm
