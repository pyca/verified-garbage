module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Copy
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! ### `Dsa.Arm.Key.Sample`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Key.Draw`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Key.InRange`, which only this module used -/

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

namespace VG.Proof.Dsa.Arm.Key

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
  · simp only [h, decide_true, ↓reduceIte]; omega_arith
  · simp only [h, decide_false]; simp; omega_arith

/-- The sign bit of `-x ∣ x`: whether `x` is nonzero. -/
theorem nz_bit (x : BitVec 32) (h : x.toNat < 256) :
    ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases hx : x = 0
  · subst hx; rfl
  · have : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    simp only [hx, ↓reduceIte, show (0 : BitVec 32).toNat = 0 from rfl]
    obtain e : decide (2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat + 0) % 2 ^ 32) = true := decide_eq_true (by omega_arith)
    rw [e, Bool.true_or]; rfl

theorem ofNat_add_one_sub {x : BitVec 32} {c : Nat} (hc : c + 1 < 2 ^ 32) :
    x + BitVec.ofNat 32 (c + 1) - 1 = x + BitVec.ofNat 32 c := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub32 _ (by omega_arith) hc]; rfl

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
theorem rangeByte_ok {s₀ t₀ t : State} (A : KeyABI s₀) {cs : List Byte} {k : Nat}
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
    rw [I.r4, show drawPlace s₀ + (k + 1) = drawPlace s₀ + k + 1 from rfl, ofNat_add_one_sub (by omega_arith)]
  obtain s₂ : t₂.gpr .r1 = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k) := by
    rw [u₂.gpr, u₁.other _ (by decide)]
    show t.gpr .r1 - 1 = _
    rw [I.r1, show (rQBytes s₀).length - rWidth s₀ + (k + 1) = (rQBytes s₀).length - rWidth s₀ + k + 1 from rfl,
      ofNat_add_one_sub (by omega_arith)]
  obtain r11₂ : t₂.gpr .r11 = t.gpr .r11 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain hn := hnonce k hk
  rw [← I.mem] at hn
  refine wp_ldrb (a := off (rBase s₀) (drawPlace s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, e₂]; exact hrf.ea (by omega_arith))
    (by rw [u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact hrf.read (d := drawPlace s₀ + k) (n := 1) (by omega_arith)) fun t₃ u₃ => ?_
  rw [u₂.mem, u₁.mem, hn] at u₃
  refine wp_dp (op2_reg _ _) fun t₄ u₄ => ?_
  obtain hqi : (rQBytes s₀).length - rWidth s₀ + k < (rQBytes s₀).length := by omega_arith
  refine wp_ldrb (a := State.addr (rQ s₀) + BitVec.ofNat 64 ((rQBytes s₀).length - rWidth s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, u₄.other _ (by decide), u₃.other _ (by decide), s₂, VG.Arm.addr_add (by omega_arith)])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hq.rd _ hqi) fun t₅ u₅ => ?_
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq.val _ hqi] at u₅
  refine wp_dp (op2_reg _ _) fun t₆ u₆ => wp_dp (op2_reg _ _) fun t₇ u₇ => wp_mov (op2_lsr (by decide)) fun t₈ u₈ =>
    wp_mov (op2_reg _ _) fun t₉ u₉ => wp_dec fun t₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  -- The values.
  obtain hc := VG.Proof.Dsa.randomBorrow_le (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
  obtain hcs' : k < cs.length := by omega_arith
  obtain hqs' : k < (qSig s₀).length := by rw [qSig_length]; omega_arith
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
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega_arith), Nat.add_sub_cancel]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, r0₇, borrow_bit (BitVec.isLt _) (by omega_arith), hb]
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
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega_arith), Nat.add_sub_cancel,
      ofNat_beq_zero (by omega_arith)]

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
      simp [hp, hl] <;> first | decide | omega_arith
  obtain R : Rest rangeRegs t t₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (f₆.rest _)))))
  obtain hm : t₆.mem = t.mem := by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [f₆.gpr]; exact r3₅, ?_, hm.trans I.mem, I.ready.congr R (by rw [hm]; exact Frame.refl _ _),
    I.rest.trans R⟩
  rw [z₆, r3₅]
  cases accepts s₀ cs <;> rfl

/-- The comparison's pointers and count. -/
theorem rangeInit_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) {cs : List Byte}
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
  obtain hcsd : cs.drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by omega_arith)
  obtain hqd : (qSig s₀).drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by rw [qSig_length])
  refine ⟨⟨h.congr R (by rw [m₈]; exact Frame.refl _ _), m₈, ?_, ?_, ?_, ?_, ?_, ?_, R⟩, m₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, R.gpr .r11 (by decide)]
    show t₂.gpr .r4 + t₂.gpr .r0 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show t.gpr .r11 + BitVec.ofNat 32 oNonce + stackArg s₀ 2 = _
    rw [show stackArg s₀ 2 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      Offset.add_add]
    unfold drawPlace; congr 2; omega_arith
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    show t₅.gpr .r1 + t₅.gpr .r2 = _
    rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq, hw, Offset.add_add]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, hw]
  · rw [u₈.other _ (by decide), u₇.gpr, hcsd, hqd]; rfl
  · rw [u₈.gpr]; decide
  · rw [u₈.gpr, hcsd]; simp

theorem inRange_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) {cs : List Byte}
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
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  refine WP.mono (rangeByte_ok A hcs (by omega_arith) hnonce J) fun v ⟨J', z⟩ => ?_
  by_cases hj : j = 0
  · left
    subst hj
    exact ⟨by rw [eval_ne, z]; rfl, WP.mono (rangeFinish_ok hcs J') fun u ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false hj]; rfl, j, by omega_arith, j, rfl, by omega_arith, by omega_arith, J'⟩

end VG.Proof.Dsa.Arm.Key

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

namespace VG.Proof.Dsa.Arm.Key

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
theorem nonce_encodes {s₀ : State} (A : KeyABI s₀) {m : Mem} {bs : List Byte}
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
theorem Smp.of {s₀ t u : State} (A : KeyABI s₀) {used draws used' draws' : Nat}
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

theorem Smp.congr {s₀ t u : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
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
theorem drawDec_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
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
theorem drawFinish_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
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
theorem drawHead_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t) :
    WP isa (.block KeyRandom.drawHead) t fun u => Smp s₀ used draws u ∧ u.mem = t.mem ∧
      Rest sampleRegs t u ∧ u.z = decide ((rInput s₀).rand.length - used < rWidth s₀) := by
  have h := S.ready
  have hub := S.usedBound
  obtain hfit := rWidth_le s₀
  obtain hql := rQBytes_le A
  obtain hrl : (rInput s₀).rand.length = (stackArg s₀ 4).toNat := by simp only [rInput, rBytes_length]
  obtain e6 : stackArg s₀ 4 = BitVec.ofNat 32 (rInput s₀).rand.length := by
    rw [hrl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold KeyRandom.drawHead
  refine wp_ldArg A h (j := 4) (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
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
theorem drawUsed_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
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
theorem drawCopy_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa KeyRandom.copy t fun u => Smp s₀ used draws u ∧
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
theorem drawUsed_bytes {s₀ : State} (A : KeyABI s₀) {t u : State} {used v : Nat}
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

end VG.Proof.Dsa.Arm.Key

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

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

theorem draw_ok {s₀ t : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) (hq : 1 < rq s₀)
    (hst : slot t.mem (rBase s₀) oStatus = 4) :
    WP isa KeyRandom.draw t fun u => RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u ∧
      ((slot u.mem (rBase s₀) oStatus = 4 ∧ 2 ≤ draws ∧ Smp s₀ (used + rWidth s₀) (draws - 1) u ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleRel s₀ S' base (used + rWidth s₀) (draws - 1)) ∧
          (spl s₀ draws used).trace = 0 :: (spl s₀ (draws - 1) (used + rWidth s₀)).trace) ∨
        (slot u.mem (rBase s₀) oStatus ≠ 4 ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleOut s₀ base S' u) ∧
          ((spl s₀ draws used).trace.head? ≠ some 0 ∨ draws = 1))) := by
  have hF : frameBytes = 112 := rfl
  have hon : oNonce = 64 := rfl
  obtain hql := rQBytes_le A
  obtain hfit := rWidth_le s₀
  obtain hw1 : 1 ≤ rWidth s₀ := Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1
  have h := S.ready
  have hub := S.usedBound
  obtain ⟨d', rfl⟩ : ∃ d', draws = d' + 1 := ⟨draws - 1, by omega_using [hd]⟩
  obtain hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hrlen : ((rInput s₀).rand.drop used).length = (rInput s₀).rand.length - used := List.length_drop
  unfold KeyRandom.draw
  refine WP.seq (WP.mono (drawHead_ok A S) fun t₃ ⟨S₃, m₃, k₃, c₃⟩ => ?_)
  have h₃ := S₃.ready
  by_cases hshort : (rInput s₀).rand.length - used < rWidth s₀
  · -- The tape is short.
    refine WP.ite true (by rw [eval_eq, c₃, decide_eq_true hshort]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_mov (op2_imm (by decide)) fun t₄ u₄ => wp_st (h₃.upd u₄) (by decide) fun t₅ m₅ h₅ => WP.block_nil ?_
    obtain k₅ : Rest sampleRegs t t₅ := k₃.trans ((u₄.rest (by decide)).trans (m₅.rest _))
    obtain hm₅ : t₅.mem = t.mem.writeW (off (rBase s₀) oStatus) (2 : BitVec 32) := by rw [m₅.mem, u₄.gpr, u₄.mem, m₃]
    obtain S₅ : Smp s₀ used (d' + 1) t₅ := S.congr A h₅
      (by rw [hm₅]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
    obtain hspl : spl s₀ (d' + 1) used = ⟨none, 0, [2]⟩ :=
      VG.Proof.Dsa.Random.sample_short _ _ _ hq (by rw [hdw, hrlen]; exact hshort)
    refine ⟨h₅, by rw [hm₅]; exact store_outs _ _ _ (by decide), k₅, .inr ⟨?_, fun S' base R => ⟨?_, ?_, ?_⟩,
      .inl (by rw [hspl]; simp)⟩⟩
    · rw [hm₅, slot_write_self]; decide
    · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₅⟩
    · rw [hm₅, slot_write_self, R.statusEq, hspl]; rfl
    · intro k hk; rw [R.scalarEq, hspl] at hk; simp at hk
  · -- A complete KeyRandom.draw.
    refine WP.ite false (by rw [eval_eq, c₃, decide_eq_false hshort]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    obtain hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length := by omega_using [hw1, hshort]
    obtain hdl := drawBytes_length hfull
    -- The copy.
    refine WP.seq (WP.mono (drawCopy_ok A S₃ hfull hw1) fun t₄ ⟨S₄, hc₄, ho₄, k₄⟩ => ?_)
    -- The consumption.
    refine WP.seq (WP.mono (drawUsed_ok A S₄ hfull) fun t₇ ⟨S₇, hm₇, k₇⟩ => ?_)
    have h₇ := S₇.ready
    obtain o₇ : Outs (rBase s₀) [(oUsed, 4)] t₄.mem t₇.mem := by rw [hm₇]; exact store_outs _ _ _ (by decide)
    obtain hc₇ := drawUsed_bytes A hm₇ hc₄
    -- The comparison.
    let cs := copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)
    refine WP.seq (WP.mono (inRange_ok A h₇ (cs := cs) S₇.q S₇.width (copiedList_length _ _ _) hw1
      fun i hi => by rw [copiedList_getD _ _ hi]; exact hc₇ i hi) fun t₈ ⟨_, z₈, m₈, h₈, k₈⟩ => ?_)
    obtain S₈ : Smp s₀ (used + rWidth s₀) (d' + 1) t₈ :=
      S₇.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈])
    obtain hacc : accepts s₀ cs = decide (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
        Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := accepts_candidate hdl hw1
    obtain htake : ((rInput s₀).rand.drop used).take (Spec.Dsa.Random.drawBytes (rq s₀)) = drawBytes s₀ used := by
      rw [hdw]
    refine WP.mono (drawFinish_ok A S₈ (by omega_using []) hdb z₈) fun u ⟨k₉, h₉, o₉, hT, hF'⟩ => ?_
    obtain outs : Outs (rBase s₀) sampleRanges t.mem u.mem := by
      obtain e₁ : Outs (rBase s₀) sampleRanges t.mem t₃.mem := by rw [m₃]; exact Outs.refl _ _ _
      obtain e₂ : Outs (rBase s₀) sampleRanges t₃.mem t₄.mem := fun x hx => ho₄ x (by
        have := hx (oNonce, 32) (by decide)
        unfold drawPlace at *; omega_using [hql, hfit, this])
      obtain e₃ : Outs (rBase s₀) sampleRanges t₄.mem t₇.mem := o₇.mono (by decide)
      obtain e₄ : Outs (rBase s₀) sampleRanges t₇.mem t₈.mem := by rw [m₈]; exact Outs.refl _ _ _
      exact (((e₁.trans e₂).trans e₃).trans e₄).trans (o₉.mono (by decide))
    obtain keeps : Rest sampleRegs t u :=
      (((k₃.trans k₄).trans k₇).trans (k₈.mono (by decide))).trans (k₉.mono (by decide))
    -- The nonce's bytes survive the stores of the slots.
    obtain hc₉ : ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
      obtain hle : ∀ r ∈ ([(oDraws, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
      rw [o₉ _ fun r hr => by
        have := hle r hr
        rw [ofs_off0 _ (by unfold drawPlace; omega_using [hon, hql, hfit, hi])]
        right; unfold drawPlace at *; omega_using [this], m₈]
      exact hc₇ i hi
    obtain st₈ : slot t₈.mem (rBase s₀) oStatus = 4 := by
      rw [m₈, hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
        slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace oStatus; omega) (by decide),
        m₃, hst]
    cases ha : accepts s₀ cs with
    | true =>
      obtain ⟨S₉, st₉⟩ := hT ha
      obtain hk : 0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀ := by
        rw [hacc] at ha; exact of_decide_eq_true ha
      obtain hspl : spl s₀ (d' + 1) used =
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
      obtain hk : ¬ (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := by
        rw [hacc] at ha; exact of_decide_eq_false ha
      obtain hnext : ((rInput s₀).rand.drop used).drop (Spec.Dsa.Random.drawBytes (rq s₀)) =
          (rInput s₀).rand.drop (used + rWidth s₀) := by
        rw [List.drop_drop, hdw]
      obtain hspl : spl s₀ (d' + 1) used =
          { spl s₀ d' (used + rWidth s₀) with
            used := rWidth s₀ + (spl s₀ d' (used + rWidth s₀)).used,
            trace := 0 :: (spl s₀ d' (used + rWidth s₀)).trace } := by
        rw [spl, VG.Proof.Dsa.Random.sample_reject _ _ _ hq (by rw [hdw, hrlen]; omega_using [hshort]) (by rw [htake]; exact hk),
          hnext, hdw]
      obtain hstatus : VG.Proof.Dsa.Random.sampleStatus (spl s₀ (d' + 1) used) =
          VG.Proof.Dsa.Random.sampleStatus (spl s₀ d' (used + rWidth s₀)) := by
        rw [hspl]; exact VG.Proof.Dsa.Random.sampleStatus_reject _ _ _ _
      obtain rel : ∀ S' base, SampleRel s₀ S' base used (d' + 1) → SampleRel s₀ S' base (used + rWidth s₀) d' :=
        fun S' base R => ⟨by rw [R.scalarEq, hspl], by rw [R.usedEq, hspl]; dsimp only; omega_using [],
          R.statusEq.trans hstatus⟩
      by_cases h0 : d' = 0
      · subst h0
        refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; simp only [Nat.add_sub_cancel, ↓reduceIte]; decide,
          fun S' base R => ?_, .inr rfl⟩⟩
        obtain R' := rel S' base R
        have h0s : spl s₀ 0 (used + rWidth s₀) = ⟨none, 0, [3]⟩ := rfl
        refine ⟨⟨0, by rw [R'.usedEq, h0s]; exact S₉⟩, ?_, ?_⟩
        · rw [st₉, R'.statusEq, h0s]; simp only [Nat.add_sub_cancel, ↓reduceIte]; rfl
        · intro k hk'; rw [R'.scalarEq, h0s] at hk'; simp at hk'
      · refine ⟨h₉, outs, keeps, .inl ⟨?_, by omega_using [h0], by simpa using S₉, fun S' base R => by simpa using rel S' base R,
          by rw [hspl, Nat.add_sub_cancel]⟩⟩
        rw [st₉]; simp only [Nat.add_sub_cancel, h0, ↓reduceIte]; exact st₈

theorem Smp.mem {s₀ t u : State} (A : KeyABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : RReady s₀ u) (hm : u.mem = t.mem) : Smp s₀ used draws u :=
  S.congr A hr (by rw [hm]; exact Outs.refl _ _ _) (by rw [hm]) (by rw [hm])

theorem SampleOut.mem {s₀ v u : State} (A : KeyABI s₀) {base : Nat} {S : Spec.Dsa.Random.Sample}
    (O : SampleOut s₀ base S v) (hr : RReady s₀ u) (hm : u.mem = v.mem) : SampleOut s₀ base S u :=
  ⟨let ⟨d, Sd⟩ := O.smp; ⟨d, Sd.mem A hr hm⟩, by rw [hm]; exact O.status, by rw [hm]; exact O.nonce⟩

/-- A new budget of 128 draws. -/
theorem sampleInit_ok {s₀ t : State} (A : KeyABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t) :
    WP isa (.block [.mov .r0 (.imm 128), st .r0 oDraws, .mov .r0 (.imm 4), st .r0 oStatus]) t
      fun u => Smp s₀ used 128 u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧
        Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧ Rest sampleRegs t u := by
  have h := S.ready
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_st (h.upd u₁) (by decide) fun t₂ m₂ h₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => wp_st (h₂.upd u₃) (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  obtain hm₄ : t₄.mem = (t.mem.writeW (off (rBase s₀) oDraws) (128 : BitVec 32)).writeW
      (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₄.mem, u₃.gpr, u₃.mem, m₂.mem, u₁.gpr, u₁.mem]
  obtain k₄ : Rest sampleRegs t t₄ :=
    (u₁.rest (by decide)).trans ((m₂.rest _).trans ((u₃.rest (by decide)).trans (m₄.rest _)))
  obtain o₄ : Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem t₄.mem := by
    rw [hm₄]; exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
  obtain S₄ : Smp s₀ used 128 t₄ := S.of A h₄ (o₄.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [drawRanges])
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
      slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
    (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]; rfl) S.usedBound
  obtain st₄ : slot t₄.mem (rBase s₀) oStatus = 4 := by rw [hm₄, slot_write_self]
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

theorem sample_ok {s₀ t : State} (A : KeyABI s₀) {used d₀ : Nat} (S : Smp s₀ used d₀ t)
    (hq : 1 < rq s₀) :
    WP isa KeyRandom.sample t fun u => SampleOut s₀ used (spl s₀ 128 used) u ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used)) ∧
      RReady s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u := by
  unfold KeyRandom.sample
  refine WP.seq (WP.mono (sampleInit_ok A S) fun t₄ ⟨S₄, st₄, o₄, k₄⟩ => ?_)
  let S₀ := spl s₀ 128 used
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used', 1 ≤ n ∧ n ≤ 128 ∧
      Smp s₀ used' n u ∧ slot u.mem (rBase s₀) oStatus = 4 ∧ SampleRel s₀ S₀ used used' n ∧
      Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Rest sampleRegs t u) (fun n u hu => ?_) 128 t₄
    ⟨used, by decide, by decide, S₄, st₄, ⟨rfl, rfl, rfl⟩, o₄.mono (by decide), k₄⟩)
  obtain ⟨used', hn1, hn, Sm, st, R, ou, ku⟩ := hu
  refine WP.seq (WP.mono (draw_ok A Sm hn1 hn hq st) fun v ⟨hv, ov, kv, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  obtain hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  obtain mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  obtain kv₂ : Rest sampleRegs t v₂ := ((ku.trans kv).trans (uv₁.rest (by decide))).trans (fv₂.rest _)
  obtain ov₂ : Outs (rBase s₀) sampleRanges t.mem v₂.mem := by rw [mv₂]; exact ou.trans ov
  rcases hcase with ⟨stv, h2, Sv, rel, _⟩ | ⟨stv, out, _⟩
  · right
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, stv]; rfl, n - 1, by omega_using [hn1], used' + rWidth s₀, by omega_using [h2], by omega_using [hn],
      Sv.mem A hv₂ mv₂, by rw [mv₂]; exact stv, rel S₀ used R, ov₂, kv₂⟩
  · have O := out S₀ used R
    obtain hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
      have := sampleStatus_le S₀
      rw [O.status, status_beq (by omega_using [this]), decide_eq_false (by omega_using [this])]
    left
    refine ⟨by rw [eval_eq, zv₂, uv₁.gpr, hz], ?_⟩
    refine wp_ld hv₂ (by decide) fun u uu => WP.block_nil ?_
    obtain hu : RReady s₀ u := hv₂.upd uu
    obtain mu : u.mem = v.mem := by rw [uu.mem, mv₂]
    refine ⟨O.mem A hu mu, by rw [uu.gpr, mv₂, O.status], hu, by rw [uu.mem]; exact ov₂,
      kv₂.trans (uu.rest (by decide))⟩

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.Finish`, which this module and modules that import it used -/

section

/-!
# The randomized signer's exit (32-bit ARM)

`finish` zeros `out` unless signing succeeded (`zeroOut_ok`), clears the
nonce, publishes the consumption to `used`, returns the status and restores
the callee-saved registers, `r11` last (`rfinish_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str wp_strb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-- Registers but `r11` and memory where the body may write change. -/
theorem RReady.congrW {s₀ t u : State} {ws : List Reg} {rs : List Region} (h : RReady s₀ t) (R : Rest ws t u)
    (hm : Frame rs t.mem u.mem) (hrs : ∀ r ∈ rs, r ∈ rWrites s₀) (h11 : .r11 ∉ ws := by decide) : RReady s₀ u :=
  ⟨h.rf.of_rest R h11, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr, h.frame.trans (hm.mono hrs)⟩

/-! ## Zeroing the output -/

/-- The output, after `k` of its bytes are zeroed. -/
structure ZeroInv (s₀ t₀ : State) (k : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  r1 : t.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 k
  r2 : t.gpr .r2 = BitVec.ofNat 32 ((s₀.gpr .r1).toNat - k)
  r0 : t.gpr .r0 = 0
  frame : Frame [rOut s₀] t₀.mem t.mem
  zero : ∀ i < k, t.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = 0
  rest : Rest [.r0, .r1, .r2] t₀ t

theorem zeroStep_ok {s₀ t₀ t : State} (A : KeyABI s₀) {k : Nat} (hk : k < (s₀.gpr .r1).toNat)
    (I : ZeroInv s₀ t₀ k t) :
    WP isa (.block [.strb .r0 .r1 0, .dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) t
      fun u => ZeroInv s₀ t₀ (k + 1) u ∧ u.z = decide ((s₀.gpr .r1).toNat - (k + 1) = 0) := by
  have hb := A.outBound
  obtain hw : InRegions t.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) 1 :=
    ⟨rOut s₀, by rw [I.ready.wr, A.wr]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine wp_strb (by decide) (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega_arith)]) hw fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  obtain hv : (t.gpr .r0).setWidth 8 = 0 := by rw [I.r0]; rfl
  rw [hv] at m₁
  obtain R : Rest [.r0, .r1, .r2] t u₃ := (m₁.rest _).trans ((v₂.rest (by decide)).trans (v₃.rest (by decide)))
  obtain mem₃ : u₃.mem = t.mem.writeW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  obtain fr : Frame [rOut s₀] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨⟨I.ready.congrW R fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites]),
    ?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.rest.trans R⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r1, Offset.add_ofNat_add_one]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.r0]
  · rw [mem₃]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · have ho : ofs (State.addr (s₀.gpr .r0)) (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = i := by
        rw [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      rw [show State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k = off (State.addr (s₀.gpr .r0)) k from rfl,
        writeW8_outside _ _ (d := k) _ (by omega_arith) _ (by rw [ho]; omega_arith)]
      exact I.zero i (by omega_arith)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith), ofNat_beq_zero (by omega_arith),
      Nat.sub_sub]

theorem zeroOut_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa zeroOut t fun u => RReady s₀ u ∧ Frame [rOut s₀] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        List.replicate (s₀.gpr .r1).toNat 0 ∧ Rest [.r0, .r1, .r2] t u := by
  obtain hL : 0 < (s₀.gpr .r1).toNat := by
    have := A.outLength; have := A.lengths; unfold Spec.Dsa.lengthsValid at *; omega_arith
  unfold zeroOut
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ?_)
  obtain R₃ : Rest [.r0, .r1, .r2] t t₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain I₀ : ZeroInv s₀ t 0 t₃ := ⟨h.congr R₃ (by rw [m₃]; exact Frame.refl _ _),
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), R₃⟩
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = (s₀.gpr .r1).toNat - k ∧
      k < (s₀.gpr .r1).toNat ∧ ZeroInv s₀ t k u) (fun n u hu => ?_) _ t₃ ⟨0, rfl, hL, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok A hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : (s₀.gpr .r1).toNat - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, J.ready, J.frame, ?_, J.rest⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega_arith)
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, _, by omega_arith, k + 1, rfl, by omega_arith, J⟩

/-- A write apart from the stack keeps the frame's slots. -/
theorem apart_slot {s₀ : State} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hd : (rStack s₀).Disjoint r)
    {d : Nat} (hd' : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      refine hd.sub_left ?_
      rw [rBase_off]; exact Offset.sub_base _ (by unfold frameBytes at hd'; omega_arith)) (by decide)

/-! ## The exit -/

/-- After the attempts, ready to finish. -/
structure RFin (s₀ t : State) : Prop where
  ready : RReady s₀ t
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  saved : Saved s₀ t.mem

/-- What the signer returns, writes and publishes, before the frame is freed. -/
structure Finished (s₀ u : State) : Prop where
  sp : u.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : u.rd = s₀.rd
  wr : u.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem u.mem
  r0 : u.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status
  regs : ∀ r ∈ preserved, u.gpr r = s₀.gpr r
  out : Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  usedLo : slot u.mem (State.addr (s₀.gpr .r2)) 0 = BitVec.ofNat 32 (rResult s₀).used
  usedHi : slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0

theorem restore_eq : ((savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) : List Instr) =
    [ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32] := rfl

theorem clearMem_frame (s₀ : State) (m : Mem) : ∀ k, k ≤ 8 → Frame [rStack s₀] m (clearMem m (rBase s₀) k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => (clearMem_frame s₀ m k (by omega_arith)).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce frameBytes; omega_arith) 0)

/-- The last block: clear the nonce, publish the consumption, restore the registers. -/
abbrev finalList : List Instr :=
  [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
    ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28]

theorem finalBlock_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem)
    {used st : BitVec 32} (hu : slot t.mem (rBase s₀) oUsed = used)
    (hs : slot t.mem (rBase s₀) oStatus = st) :
    WP isa (.block (clearNonce ++ finalList)) t fun u =>
      u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ Frame [rStack s₀, rUsed s₀] t.mem u.mem ∧ u.gpr .r0 = st ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ slot u.mem (State.addr (s₀.gpr .r2)) 0 = used ∧
      slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0 := by
  have hub := A.usedBound
  refine clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_
  obtain fr₁ : Frame [rStack s₀] t.mem t₁.mem := by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide)
  obtain o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  obtain sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  obtain sl₁ : ∀ d, d + 4 ≤ oNonce → slot t₁.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Nat.le_refl _) hd
      (by unfold oNonce at hd; omega_arith)
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ld (h₁.upd u₂) (by decide) fun t₃ u₃ => ?_
  obtain h₃ := (h₁.upd u₂).upd u₃
  obtain r4₃ : t₃.gpr .r4 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.gpr]; exact sv₁.2.2.2.1
  obtain r0₃ : t₃.gpr .r0 = used := by rw [u₃.gpr, u₂.mem, sl₁ _ (by decide), hu]
  obtain hU : (rUsed s₀) ∈ t₃.wr := by rw [h₃.wr, A.wr]; simp
  refine wp_str (a := State.addr (s₀.gpr .r2)) (by decide) (by rw [BitVec.add_zero, r4₃])
    ⟨_, hU, by
      have := Offset.contains_base (State.addr (s₀.gpr .r2)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩ fun t₄ m₄ => wp_mov (op2_imm (by decide)) fun t₅ u₅ => ?_
  refine wp_str (a := State.addr (s₀.gpr .r2) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₅.other _ (by decide), m₄.gpr, r4₃, VG.Arm.addr_add (by omega_arith)])
    ⟨_, by rw [u₅.wr, m₄.wr]; exact hU, Offset.contains_base _ (by decide) (by decide)⟩ fun t₆ m₆ => ?_
  obtain mem₆ : t₆.mem = (t₃.mem.writeW (off (State.addr (s₀.gpr .r2)) 0) used).writeW
      (off (State.addr (s₀.gpr .r2)) 4) (0 : BitVec 32) := by
    rw [m₆.mem, u₅.gpr, u₅.mem, m₄.mem, r0₃, off, BitVec.add_zero]
  obtain fu : Frame [rUsed s₀] t₃.mem t₆.mem := by
    rw [mem₆]
    exact (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain ap : ∀ d, d + 4 ≤ frameBytes → slot t₆.mem (rBase s₀) d = slot t₃.mem (rBase s₀) d := fun d hd =>
    apart_slot fu A.stackUsed hd
  obtain m₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  obtain h₆ : RReady s₀ t₆ := h₃.congrW (ws := [.r0]) ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _))) fu
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])
  obtain sv₆ : Saved s₀ t₆.mem := sv₁.of_slots fun d _ hd => by rw [ap d hd, m₃]
  obtain hst₆ : slot t₆.mem (rBase s₀) oStatus = st := by rw [ap _ (by decide), m₃, sl₁ _ (by decide), hs]
  obtain ⟨sr, -⟩ := sv₆
  refine wp_ld h₆ (by decide) fun t₇ u₇ => ?_
  obtain h₇ := h₆.upd u₇
  refine wp_ld h₇ (by decide) fun t₈ u₈ => wp_ld (h₇.upd u₈) (by decide) fun t₉ u₉ =>
    wp_ld ((h₇.upd u₈).upd u₉) (by decide) fun t₁₀ u₁₀ =>
    wp_ld (((h₇.upd u₈).upd u₉).upd u₁₀) (by decide) fun t₁₁ u₁₁ =>
    wp_ld ((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁) (by decide) fun t₁₂ u₁₂ =>
    wp_ld (((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂) (by decide) fun t₁₃ u₁₃ =>
    wp_ld ((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃) (by decide) fun t₁₄ u₁₄ =>
    wp_ld (((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄) (by decide) fun t₁₅ u₁₅ =>
    wp_ld ((((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄).upd u₁₅) (by decide)
      fun t₁₆ u₁₆ => WP.block_nil ?_
  obtain mm : t₁₆.mem = t₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain R : Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] t₆ t₁₆ :=
    (u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
      ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans ((u₁₃.rest (by decide)).trans
      ((u₁₄.rest (by decide)).trans ((u₁₅.rest (by decide)).trans (u₁₆.rest (by decide))))))))))
  obtain R₆ : Rest [.r0, .r2, .r4] t t₆ := ((k₁.mono (by decide)).trans ((u₂.rest (by decide)).trans
    (u₃.rest (by decide)))).trans ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _)))
  obtain hm : ∀ t' : State, t'.mem = t₆.mem → ∀ i < 9, slot t'.mem (rBase s₀) (4 * i) =
      s₀.gpr (savedRegs.getD i .r0) := fun t' e i hi => by rw [e]; exact sr i hi
  refine ⟨by rw [R.sp, R₆.sp], by rw [R.rd, R₆.rd], by rw [R.wr, R₆.wr], ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [mm]; exact (fr₁.mono (by simp)).trans ((show Frame [rUsed s₀] t₁.mem t₆.mem by rw [← m₃]; exact fu).mono
      (by simp))
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.gpr, hst₆]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, u₉.get, reduceCtorEq, ↓reduceIte,
        u₈.gpr, u₇.mem]
      exact hm t₆ rfl 0 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, reduceCtorEq, ↓reduceIte, u₉.gpr]
      exact hm t₈ (by rw [u₈.mem, u₇.mem]) 1 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, reduceCtorEq, ↓reduceIte, u₁₀.gpr]
      exact hm t₉ (by rw [u₉.mem, u₈.mem, u₇.mem]) 2 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, reduceCtorEq, ↓reduceIte, u₁₁.gpr]
      exact hm t₁₀ (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 3 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, reduceCtorEq, ↓reduceIte, u₁₂.gpr]
      exact hm t₁₁ (by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 4 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, reduceCtorEq, ↓reduceIte, u₁₃.gpr]
      exact hm t₁₂ (by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 5 (by decide)
    · simp only [u₁₆.get, u₁₅.get, reduceCtorEq, ↓reduceIte, u₁₄.gpr]
      exact hm t₁₃ (by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 6 (by decide)
    · rw [u₁₆.gpr]
      exact hm t₁₅ (by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 7
        (by decide)
    · simp only [u₁₆.get, reduceCtorEq, ↓reduceIte, u₁₅.gpr]
      exact hm t₁₄ (by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 8 (by decide)
  · rw [mm, mem₆, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]
  · rw [mm, mem₆, slot_write_self]

theorem finishBlock_eq : (clearNonce ++ [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0),
    .str .r0 .r4 4, ld .r0 oStatus] ++ (savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) ++
    [ld .r11 28] : List Instr) = clearNonce ++ finalList := by
  rw [restore_eq]; rfl

theorem rfinish_ok {s₀ t : State} (A : KeyABI s₀) (F : RFin s₀ t) (hR : (rResult s₀).status ≤ 2)
    (hsig : (rResult s₀).status ≠ 1 → (rResult s₀).key = none) :
    WP isa finish t fun u => Finished s₀ u := by
  have h := F.ready
  have hb := A.outBound
  obtain hout : ∀ {m m' : Mem}, Frame [rStack s₀, rUsed s₀] m m' →
      Spec.Rsa.bytesAt m' (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        Spec.Rsa.bytesAt m (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat := fun hf =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.stackOut.symm
      · exact A.outUsed) (by omega_arith)
  unfold finish
  rw [finishBlock_eq]
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  obtain h₂ := (h.upd u₁).fupd f₂
  obtain m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  obtain R₂ : Rest [.r0] t t₂ := (u₁.rest (by decide)).trans (f₂.rest _)
  rw [u₁.gpr, F.status, one_beq (by omega_arith)] at z₂
  obtain fin : ∀ v : State, RReady s₀ v → Rest [.r0, .r1, .r2] t v → Frame (rWrites s₀) t.mem v.mem →
      Saved s₀ v.mem → slot v.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used →
      slot v.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status →
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0) →
      WP isa (.block (clearNonce ++ finalList)) v fun u => Finished s₀ u := fun v hv Rv fv sv hu hs ho =>
    WP.mono (finalBlock_ok A hv sv hu hs) fun u ⟨sp, rd, wr, fr, r0, regs, lo, hi⟩ =>
      ⟨by rw [sp, Rv.sp, h.sp], by rw [rd, Rv.rd, h.rd], by rw [wr, Rv.wr, h.wr],
        hv.frame.trans (fr.mono (by simp [rWrites])), r0, regs, by rw [hout fr]; exact ho, lo, hi⟩
  by_cases h1 : (rResult s₀).status = 1
  · refine WP.seq (WP.ite false (by rw [eval_ne, z₂, decide_eq_true h1]; rfl)
      (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact fin t₂ h₂ (R₂.mono (by decide)) (by rw [m₂]; exact Frame.refl _ _) (by rw [m₂]; exact F.saved)
      (by rw [m₂]; exact F.usedW) (by rw [m₂]; exact F.status) (by rw [m₂]; exact F.out h1)
  · refine WP.seq (WP.ite true (by rw [eval_ne, z₂, decide_eq_false h1]; rfl)
      (fun _ => WP.mono (zeroOut_ok A h₂ (by rw [m₂]; exact F.saved)) fun v ⟨hv, fv, zv, Rv⟩ => ?_)
      (fun e => Bool.noConfusion e))
    obtain ap : ∀ d, d + 4 ≤ frameBytes → slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd => by
      rw [apart_slot fv A.stackOut hd, m₂]
    exact fin v hv ((R₂.mono (by decide)).trans Rv) (by rw [← m₂]; exact fv.mono (by simp [rWrites]))
      (F.saved.of_slots fun d _ hd => ap d hd) (by rw [ap _ (by decide)]; exact F.usedW)
      (by rw [ap _ (by decide)]; exact F.status) (by rw [zv, hsig h1]; rfl)

end VG.Proof.Dsa.Arm.Key

end

end

/-!
# DSA key generation on 32-bit ARM: the body

The entry saves the registers (`entry_ok`); the domain check's call
(`callCheck_ok`) decides whether to sample; one budget of draws
(`sample_ok`) gives x or the status; with x, the derivation's call
(`callDerive_ok`) writes the key and its status. Every path leaves what
`rfinish_ok` needs: the specification's status, consumption and key.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

variable {umaal : Bool}

/-! ## The specification's result -/

/-- The checks of the domain, as the specification makes them. -/
abbrev rChecked (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- With valid lengths, the result is the check, the sampling and the derivation's. -/
theorem rResult_eq {s₀ : State} (A : KeyABI s₀) :
    rResult s₀ = if rChecked s₀ then
        match (spl s₀ 128 0).scalar with
        | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0), (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace⟩
        | some x =>
          let res := Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
            (Spec.Dsa.encodeBE (rInput s₀).qLen x)
          ⟨res, Spec.Dsa.signStatus res, (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace ++ [if res.isSome then 5 else 6]⟩
      else ⟨none, 0, 0, [4]⟩ := by
  obtain hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  rw [rResult, VG.Proof.Dsa.generateKeyBytes_eq hl hk, spl, List.drop_zero, ← rQ_decode]
  cases h : (Spec.Dsa.Random.sample (rq s₀) 128 (rInput s₀).rand).scalar <;>
    simp [VG.Proof.Dsa.Random.sampleStatus, h]

/-- A checked domain has q > 1. -/
theorem rq_of_checked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = true) : 1 < rq s₀ := by
  obtain hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  have := (VG.Proof.Dsa.Arm.checkParametersBytes_iff hl hk).mp hc
  obtain B := VG.Proof.Dsa.supported_bounds this.1.1
  rw [rQ_decode]; omega_arith

theorem rResult_unchecked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = false) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_eq A, hc]; rfl

/-! ## Memory the calls keep -/

abbrev frameR (s₀ : State) : Region := ⟨rBase s₀, frameBytes⟩

theorem frameR_sub (s₀ : State) : Region.Sub (frameR s₀) (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 32) (n := frameBytes) (k := 144) (by decide)
  exact this

/-- The frame's slots, apart from what a call wrote. -/
theorem slot_keep {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (frameR s₀) r) {d : Nat} (hd' : d + 4 ≤ frameBytes) :
    slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have : frameBytes = 112 := rfl; omega_arith))) (by decide)

theorem frame_low (s₀ : State) : Region.Disjoint (frameR s₀) ⟨rLow s₀, 32⟩ :=
  Offset.disjoint_base _ (Nat.le_refl 32) (by decide)

theorem check_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ checkWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [checkWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

theorem derive_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ deriveWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [deriveWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut.sub_left (frameR_sub s₀)
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

/-- The domain's bytes, which nothing writes. -/
theorem key_bytes {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
    Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (by have := (stackArg s₀ 0).isLt; omega_arith)
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-! ## The entry -/

/-- Before `r11` holds the frame's base, `r12` does. -/
structure PreR (s₀ t : State) : Prop where
  r12 : t.gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- `str r, [r12, #d]`, a slot of the frame. -/
theorem wp_strP {s₀ t : State} (A : KeyABI s₀) (P : PreR s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, PreR s₀ u → u.mem = t.mem.writeW (off (rBase s₀) d) (t.gpr r) → u.gpr = t.gpr →
      WP isa (.block is) u Q) :
    WP isa (.block (.str r .r12 d :: is)) t Q := by
  obtain hb := rBase_toNat A
  have hs := A.stackBound
  have hl := A.stackLow
  obtain ha : State.addr (t.gpr .r12 + BitVec.ofNat 32 d) = off (rBase s₀) d := by
    rw [P.r12, VG.Arm.addr_add (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_arith),
      alloc_base A]
  refine wp_str (by unfold frameBytes at hd; omega_arith) ha
    ⟨_, by rw [P.wr]; exact List.mem_cons_self, Offset.contains_base _ hd (by unfold frameBytes at *; omega_arith)⟩
    fun u m => k u ⟨by rw [m.gpr]; exact P.r12, m.sp.trans P.sp, m.rd.trans P.rd, m.wr.trans P.wr,
      P.frame.trans (by
        rw [m.mem]
        exact (frame_store s₀ t.mem hd (t.gpr r)).mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [rWrites])⟩ m.mem m.gpr

theorem entry_eq : GenerateKey.entry = [.addSp .r12 0, .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12,
    .str .r8 .r12 16, .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28, .str .lr .r12 32,
    .mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, st .r0 oStatus] := rfl

/-- Save the callee-saved registers and the register arguments, and start the counts. -/
theorem entry_ok {s₀ : State} (A : KeyABI s₀) :
    WP isa (.block GenerateKey.entry) (allocated frameBytes s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 ∧
      (∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s₀.gpr r) := by
  rw [entry_eq]
  refine VG.Proof.X25519.Arm.WP.cons (s' := (allocated frameBytes s₀).setReg .r12
    ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) (by simp [exec]) ?_
  obtain P₀ : PreR s₀ ((allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) :=
    ⟨by simp [State.setReg, allocated], rfl, rfl, by
      show ⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ :: s₀.wr = _; rw [alloc_base A],
      Frame.refl _ _⟩
  obtain g₀ : ∀ r, r ≠ .r12 → ((allocated frameBytes s₀).setReg .r12
      ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)).gpr r = s₀.gpr r := fun r h => by
    simp [State.setReg, allocated, h]
  refine wp_strP A P₀ (by decide) fun t₁ P₁ m₁ g₁ => wp_strP A P₁ (by decide) fun t₂ P₂ m₂ g₂ =>
    wp_strP A P₂ (by decide) fun t₃ P₃ m₃ g₃ => wp_strP A P₃ (by decide) fun t₄ P₄ m₄ g₄ =>
    wp_strP A P₄ (by decide) fun t₅ P₅ m₅ g₅ => wp_strP A P₅ (by decide) fun t₆ P₆ m₆ g₆ =>
    wp_strP A P₆ (by decide) fun t₇ P₇ m₇ g₇ => wp_strP A P₇ (by decide) fun t₈ P₈ m₈ g₈ =>
    wp_strP A P₈ (by decide) fun t₉ P₉ m₉ g₉ => wp_mov (op2_reg _ _) fun t₁₀ u₁₀ => ?_
  obtain gg : ∀ r, r ≠ .r12 → t₉.gpr r = s₀.gpr r := fun r h => by
    rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact g₀ r h
  obtain nw : (rBase s₀).toNat + frameBytes + 28 ≤ 2 ^ 32 := by
    rw [rBase_toNat A]; have := A.stackBound; have := A.stackLow; unfold frameBytes; omega_arith
  obtain h₁₀ : RReady s₀ t₁₀ :=
    ⟨⟨by rw [u₁₀.gpr, P₉.r12, alloc_base A], by rw [u₁₀.wr, P₉.wr]; exact List.mem_cons_self,
      by rw [u₁₀.rd, P₉.rd, A.rd, rBase_args A]; simp, nw⟩,
      u₁₀.sp.trans P₉.sp, u₁₀.rd.trans P₉.rd, u₁₀.wr.trans P₉.wr, by rw [u₁₀.mem]; exact P₉.frame⟩
  refine wp_st h₁₀ (by decide) fun t₁₁ m₁₁ h₁₁ => wp_st h₁₁ (by decide) fun t₁₂ m₁₂ h₁₂ =>
    wp_st h₁₂ (by decide) fun t₁₃ m₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ m₁₄ h₁₄ =>
    wp_mov (op2_imm (by decide)) fun t₁₅ u₁₅ => wp_st (h₁₄.upd u₁₅) (by decide) fun t₁₆ m₁₆ h₁₆ =>
    wp_st h₁₆ (by decide) fun t₁₈ m₁₈ h₁₈ => WP.block_nil ?_
  obtain e₁₄ : ∀ r, r ≠ .r11 → r ≠ .r12 → t₁₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [m₁₄.gpr, m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ h]; exact gg r h'
  obtain hm : t₁₈.mem = ((((((((((((((s₀.mem.writeW (off (rBase s₀) 0) (s₀.gpr .r4)).writeW
      (off (rBase s₀) 4) (s₀.gpr .r5)).writeW (off (rBase s₀) 8) (s₀.gpr .r6)).writeW
      (off (rBase s₀) 12) (s₀.gpr .r7)).writeW (off (rBase s₀) 16) (s₀.gpr .r8)).writeW
      (off (rBase s₀) 20) (s₀.gpr .r9)).writeW (off (rBase s₀) 24) (s₀.gpr .r10)).writeW
      (off (rBase s₀) 28) (s₀.gpr .r11)).writeW (off (rBase s₀) 32) (s₀.gpr .lr)).writeW
      (off (rBase s₀) oOut) (s₀.gpr .r0)).writeW (off (rBase s₀) oOutLen) (s₀.gpr .r1)).writeW
      (off (rBase s₀) oUsedPtr) (s₀.gpr .r2)).writeW (off (rBase s₀) oKey) (s₀.gpr .r3)).writeW
      (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := by
    obtain v0 : t₁₀.gpr .r0 = s₀.gpr .r0 := by rw [u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v1 : t₁₁.gpr .r1 = s₀.gpr .r1 := by rw [m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v2 : t₁₂.gpr .r2 = s₀.gpr .r2 := by
      rw [m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v3 : t₁₃.gpr .r3 = s₀.gpr .r3 := by
      rw [m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    rw [m₁₈.mem, m₁₆.gpr, u₁₅.gpr, m₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄.mem, m₁₃.mem, m₁₂.mem, m₁₁.mem, v0, v1, v2, v3,
      u₁₀.mem, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    simp only [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, g₀ _ (by decide : Reg.r4 ≠ .r12), g₀ _ (by decide : Reg.r5 ≠ .r12),
      g₀ _ (by decide : Reg.r6 ≠ .r12), g₀ _ (by decide : Reg.r7 ≠ .r12), g₀ _ (by decide : Reg.r8 ≠ .r12),
      g₀ _ (by decide : Reg.r9 ≠ .r12), g₀ _ (by decide : Reg.r10 ≠ .r12), g₀ _ (by decide : Reg.r11 ≠ .r12),
      g₀ _ (by decide : Reg.lr ≠ .r12)]
    rfl
  refine ⟨h₁₈, ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h0 h11 h12 => ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by omega_arith
    all_goals (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; rfl)
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | skip
  rw [m₁₈.gpr, m₁₆.gpr, u₁₅.other _ h0]; exact e₁₄ r h11 h12


/-! ## The results -/

theorem sampleStatus_none {S : Spec.Dsa.Random.Sample} (h : S.scalar = none) :
    VG.Proof.Dsa.Random.sampleStatus S ≠ 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; simp only [h]; split <;> omega_arith

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} {k : Nat} (h : S.scalar = some k) :
    VG.Proof.Dsa.Random.sampleStatus S = 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; rw [h]

theorem rResult_status_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_eq A]
  split
  · split
    · exact sampleStatus_le _
    · have := status_lt (Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen ‹_›)); dsimp only; omega_arith
  · decide

theorem rResult_key {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≠ 1 → (rResult s₀).key = none := by
  rw [rResult_eq A]
  split
  · split
    · intro _; rfl
    · dsimp only; unfold Spec.Dsa.signStatus; split
      · intro h; exact absurd rfl h
      · next h => intro _; simpa using h
  · intro _; rfl

/-! ## The body -/

theorem body_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (body check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) (allocated frameBytes s₀)
      fun u => Finished s₀ u := by
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit := rWidth_le s₀
  have hF : frameBytes = 112 := rfl
  unfold body
  refine WP.seq (WP.mono (entry_ok A) fun t₁ ⟨h₁, sv₁, us₁, st₁, _⟩ => ?_)
  refine WP.seq (WP.mono (checkArgs_ok A h₁ sv₁) fun t₂ ⟨h₂, m₂, C₂, _⟩ => ?_)
  refine WP.seq (WP.mono (callCheck_ok A h₂ C₂ check) fun t₃ ⟨h₃, f₃, _, r0₃⟩ => ?_)
  obtain sl₃ : ∀ d, d + 4 ≤ frameBytes → slot t₃.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd => by
    rw [slot_keep f₃ (check_keeps A) hd, m₂]
  obtain hck : checkResult s₀ t₂ = rChecked s₀ := by
    unfold checkResult; rw [key_bytes A h₂]; rfl
  rw [hck] at r0₃
  obtain sv₃ : Saved s₀ t₃.mem := sv₁.of_slots fun d _ hd => sl₃ d hd
  refine WP.seq (wp_cmp0 fun t₄ f₄ z₄ => WP.block_nil ?_)
  obtain h₄ := h₃.fupd f₄
  have m₄ : t₄.mem = t₃.mem := f₄.mem
  rw [r0₃] at z₄
  suffices H : WP isa (.ite .eq (.block []) (generate derive (Generate.deriveChecked umaal))) t₄ (RFin s₀) from
    WP.seq (WP.mono H fun u hu => rfinish_ok A hu (rResult_status_le A) (rResult_key A))
  by_cases hc : rChecked s₀ = true
  · rw [hc] at z₄
    refine WP.ite false (by rw [eval_eq, z₄]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    obtain hq := rq_of_checked A hc
    obtain sv₄ : Saved s₀ t₄.mem := by rw [m₄]; exact sv₃
    unfold generate
    refine WP.seq (WP.mono (prepare_ok A h₄ sv₄.2.2.2.2) fun t₅ ⟨_, P₅, h₅, o₅, _⟩ => ?_)
    obtain P := P₅ hq
    obtain lo₅ : ∀ d, d + 4 ≤ oQ → slot t₅.mem (rBase s₀) d = slot t₄.mem (rBase s₀) d := fun d hd =>
      outs_low o₅ (by decide) hd (by unfold oQ at hd; omega_arith)
    obtain us₅ : slot t₅.mem (rBase s₀) oUsed = BitVec.ofNat 32 0 := by
      rw [lo₅ _ (by decide), m₄, sl₃ _ (by decide)]; exact us₁
    obtain S₅ : Smp s₀ 0 (slot t₅.mem (rBase s₀) oDraws).toNat t₅ :=
      ⟨h₅, P.q, P.width, P.mask, us₅, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => P.nonce i (by omega_arith), Nat.zero_le _⟩
    obtain sv₅ : Saved s₀ t₅.mem := sv₄.of_outs o₅ (by decide)
    refine WP.seq (WP.mono (sample_ok A S₅ hq) fun t₆ ⟨O₆, r0₆, h₆, o₆, _⟩ => ?_)
    obtain sv₆ : Saved s₀ t₆.mem := sv₅.of_outs o₆ (by decide)
    obtain ⟨d₆, Sm₆⟩ := O₆.smp
    obtain hR := rResult_eq A
    simp only [hc, ↓reduceIte] at hR
    unfold derived
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun t₇ f₇ z₇ => WP.block_nil ?_)
    obtain h₇ := h₆.fupd f₇
    have m₇ : t₇.mem = t₆.mem := f₇.mem
    rw [r0₆, one_beq (by have := sampleStatus_le (spl s₀ 128 0); omega_arith)] at z₇
    cases hk : (spl s₀ 128 0).scalar with
    | none =>
      simp only [hk] at hR
      obtain hn := sampleStatus_none hk
      refine WP.ite false (by rw [eval_eq, z₇, decide_eq_false hn]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨h₇, ?_, ?_, fun e => by rw [hR] at e; exact absurd e hn, by rw [m₇]; exact sv₆⟩
      · rw [m₇, Sm₆.usedW, hR]; simp
      · rw [m₇, O₆.status, hR]
    | some k =>
      simp only [hk] at hR
      obtain h1 := sampleStatus_some hk
      refine WP.ite true (by rw [eval_eq, z₇, decide_eq_true h1]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine WP.seq (WP.mono (deriveArgs_ok A h₇ (by rw [m₇]; exact sv₆)) fun t₈ ⟨h₈, m₈, C₈, _⟩ => ?_)
      refine WP.seq (WP.mono (callDerive_ok A h₈ C₈ derive (by rw [key_bytes A h₈]; exact hc))
        fun t₉ ⟨h₉, f₉, _, r0₉, out₉⟩ => ?_)
      refine wp_st h₉ (by decide) fun t₁₀ mm₁₀ h₁₀ => WP.block_nil ?_
      -- What the derivation read.
      obtain hres : deriveResult s₀ t₈ = Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
          (Spec.Dsa.encodeBE (rInput s₀).qLen k) := by
        unfold deriveResult
        rw [key_bytes A h₈, m₈, m₇, ← hqn, O₆.nonce k hk, hqn]
        rfl
      rw [hres] at r0₉ out₉
      obtain sl₉ : ∀ d, d + 4 ≤ frameBytes → slot t₉.mem (rBase s₀) d = slot t₆.mem (rBase s₀) d := fun d hd => by
        rw [slot_keep f₉ (derive_keeps A) hd, m₈, m₇]
      have mem₁₀ : t₁₀.mem = t₉.mem.writeW (off (rBase s₀) oStatus) (t₉.gpr .r0) := mm₁₀.mem
      refine ⟨h₁₀, ?_, ?_, fun _ => ?_, ?_⟩
      · rw [mem₁₀, slot_write_ne _ _ _ (by decide) (by decide) (by decide), sl₉ _ (by decide), Sm₆.usedW, hR]
        simp
      · rw [mem₁₀, slot_write_self, r0₉, hR]
      · rw [mem₁₀, rBytes_frame (frame_store s₀ t₉.mem (by decide) _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm)
          (by have := (s₀.gpr .r1).isLt; omega_arith), out₉, hR]
      · exact sv₆.of_slots fun d hd hd' => by
          rw [mem₁₀, slot_write_ne _ _ _ (by unfold oStatus; omega_arith) (by omega_arith) (by decide), sl₉ d hd']
  · have hc' : rChecked s₀ = false := by simpa using hc
    rw [hc'] at z₄
    refine WP.ite true (by rw [eval_eq, z₄]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    obtain hR := rResult_unchecked A hc'
    refine ⟨h₄, ?_, ?_, fun e => by rw [hR] at e; exact absurd e (by decide), by rw [m₄]; exact sv₃⟩
    · rw [m₄, sl₃ _ (by decide), us₁, hR]; rfl
    · rw [m₄, sl₃ _ (by decide), st₁, hR]; rfl

end VG.Proof.Dsa.Arm.Key
