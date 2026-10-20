module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomCopy
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepare
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

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
  · simp only [h, decide_true, ↓reduceIte]; omega
  · simp only [h, decide_false]; simp; omega

/-- The sign bit of `-x ∣ x`: whether `x` is nonzero. -/
theorem nz_bit (x : BitVec 32) (h : x.toNat < 256) :
    ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases hx : x = 0
  · subst hx; rfl
  · have : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    simp only [hx, ↓reduceIte, show (0 : BitVec 32).toNat = 0 from rfl]
    have e : decide (2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat + 0) % 2 ^ 32) = true := decide_eq_true (by omega)
    rw [e, Bool.true_or]; rfl

theorem ofNat_add_one_sub {x : BitVec 32} {c : Nat} (hc : c + 1 < 2 ^ 32) :
    x + BitVec.ofNat 32 (c + 1) - 1 = x + BitVec.ofNat 32 c := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub32 _ (by omega) hc]; rfl

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
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hdp := drawPlace_le A
  have hq := I.ready.q A
  have hqfit := hq.fit
  have hrf := I.ready.rf
  unfold rangeByte borrow
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun t₁ u₁ => wp_dp (op2_imm (by decide)) fun t₂ u₂ => ?_
  have e₂ : t₂.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀ + k) := by
    rw [u₂.other _ (by decide), u₁.gpr]
    show t.gpr .r4 - 1 = _
    rw [I.r4, show drawPlace s₀ + (k + 1) = drawPlace s₀ + k + 1 from rfl, ofNat_add_one_sub (by omega)]
  have s₂ : t₂.gpr .r1 = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k) := by
    rw [u₂.gpr, u₁.other _ (by decide)]
    show t.gpr .r1 - 1 = _
    rw [I.r1, show (rQBytes s₀).length - rWidth s₀ + (k + 1) = (rQBytes s₀).length - rWidth s₀ + k + 1 from rfl,
      ofNat_add_one_sub (by omega)]
  have r11₂ : t₂.gpr .r11 = t.gpr .r11 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have hn := hnonce k hk
  rw [← I.mem] at hn
  refine wp_ldrb (a := off (rBase s₀) (drawPlace s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, e₂]; exact hrf.ea (by omega))
    (by rw [u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact hrf.read (d := drawPlace s₀ + k) (n := 1) (by omega)) fun t₃ u₃ => ?_
  rw [u₂.mem, u₁.mem, hn] at u₃
  refine wp_dp (op2_reg _ _) fun t₄ u₄ => ?_
  have hqi : (rQBytes s₀).length - rWidth s₀ + k < (rQBytes s₀).length := by omega
  refine wp_ldrb (a := State.addr (rQ s₀) + BitVec.ofNat 64 ((rQBytes s₀).length - rWidth s₀ + k)) (by decide)
    (by rw [BitVec.add_zero, u₄.other _ (by decide), u₃.other _ (by decide), s₂, VG.Arm.addr_add (by omega)])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hq.rd _ hqi) fun t₅ u₅ => ?_
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq.val _ hqi] at u₅
  refine wp_dp (op2_reg _ _) fun t₆ u₆ => wp_dp (op2_reg _ _) fun t₇ u₇ => wp_mov (op2_lsr (by decide)) fun t₈ u₈ =>
    wp_mov (op2_reg _ _) fun t₉ u₉ => wp_dec fun t₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  -- The values.
  have hc := VG.Proof.Dsa.randomBorrow_le (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
  have hcs' : k < cs.length := by omega
  have hqs' : k < (qSig s₀).length := by rw [qSig_length]; omega
  have hqk : (qSig s₀)[k] = (rQBytes s₀)[(rQBytes s₀).length - rWidth s₀ + k] := by
    simp only [qSig, qSigOf, List.getElem_drop]
  have hdrop : ∀ (l : List Byte) (h : k < l.length), l.drop k = l[k] :: l.drop (k + 1) := fun l h => by
    rw [List.drop_eq_getElem_cons h]
  have hb : randomBorrow (cs.drop k) ((qSig s₀).drop k) =
      if (cs[k]).toNat < ((qSig s₀)[k]).toNat + randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
      then 1 else 0 := by
    rw [hdrop cs hcs', hdrop (qSig s₀) hqs', randomBorrow]
  have hcg : cs.getD k 0 = cs[k] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcs', Option.getD_some]
  have r0₇ : t₇.gpr .r0 = BitVec.ofNat 32 (cs[k]).toNat - BitVec.ofNat 32 (((qSig s₀)[k]).toNat +
      randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))) := by
    rw [u₇.gpr]
    show t₆.gpr .r0 - t₆.gpr .r5 = _
    rw [u₆.gpr, u₆.other .r0 (by decide)]
    show t₅.gpr .r0 - (t₅.gpr .r5 + t₅.gpr .r3) = _
    rw [u₅.gpr, u₅.other .r0 (by decide), u₅.other .r3 (by decide), u₄.other .r0 (by decide),
      u₄.other .r3 (by decide), u₃.gpr, u₃.other .r3 (by decide), u₂.other .r3 (by decide), u₁.other .r3 (by decide),
      I.r3, hcg, hqk, setWidth8_ofNat, setWidth8_ofNat, BitVec.ofNat_add_ofNat]
  have R : Rest rangeRegs t t₁₀ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
      ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
      ((u₉.rest (by decide)).trans (u₁₀.rest (by decide))))))))))
  have hm : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r6₁₀ : t₁₀.gpr .r6 = t.gpr .r6 ||| cs[k].setWidth 32 := by
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
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega), Nat.add_sub_cancel]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, r0₇, borrow_bit (BitVec.isLt _) (by omega), hb]
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
      u₂.other _ (by decide), u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega), Nat.add_sub_cancel,
      ofNat_beq_zero (by omega)]

theorem rangeFinish_ok {s₀ t₀ t : State} {cs : List Byte} (hcs : cs.length = rWidth s₀)
    (I : RangeInv s₀ t₀ cs 0 t) :
    WP isa (.block rangeFinish) t fun u => u.gpr .r3 = (if accepts s₀ cs then 1 else 0) ∧
      u.z = !accepts s₀ cs ∧ u.mem = t₀.mem ∧ RReady s₀ u ∧ Rest rangeRegs t₀ u := by
  unfold rangeFinish
  refine wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_dp (op2_reg _ _) fun t₂ u₂ => wp_dp (op2_reg _ _) fun t₃ u₃ =>
    wp_mov (op2_lsr (by decide)) fun t₄ u₄ => wp_dp (op2_reg _ _) fun t₅ u₅ => wp_cmp0 fun t₆ f₆ z₆ =>
    WP.block_nil ?_
  have hb := VG.Proof.Dsa.randomBorrow_eq cs (qSig s₀) (by rw [hcs, qSig_length])
  have hz : (t.gpr .r6 = 0) ↔ Spec.Dsa.decodeBE cs = 0 := by
    rw [VG.Proof.Dsa.decodeBE_eq_zero]; simpa only [List.drop_zero] using I.r6z
  have r6 : t₂.gpr .r6 = t.gpr .r6 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have r0₄ : t₄.gpr .r0 = if t.gpr .r6 = 0 then 0 else 1 := by
    rw [u₄.gpr, u₃.gpr]
    show (t₂.gpr .r0 ||| t₂.gpr .r6) >>> 31 = _
    rw [u₂.gpr, r6]
    show ((t₁.gpr .r0 - t₁.gpr .r6) ||| t.gpr .r6) >>> 31 = _
    rw [u₁.gpr, u₁.other _ (by decide), nz_bit _ I.r6]
  have r3₅ : t₅.gpr .r3 = (if accepts s₀ cs then 1 else 0) := by
    rw [u₅.gpr]
    show t₄.gpr .r3 &&& t₄.gpr .r0 = _
    rw [r0₄, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), I.r3]
    simp only [List.drop_zero, hb, show (t.gpr .r6 = 0) = (Spec.Dsa.decodeBE cs = 0) from propext hz]
    unfold accepts acceptsOf
    by_cases hp : Spec.Dsa.decodeBE cs = 0 <;> by_cases hl : Spec.Dsa.decodeBE cs < Spec.Dsa.decodeBE (qSig s₀) <;>
      simp [hp, hl] <;> first | decide | omega
  have R : Rest rangeRegs t t₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (f₆.rest _)))))
  have hm : t₆.mem = t.mem := by rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [f₆.gpr]; exact r3₅, ?_, hm.trans I.mem, I.ready.congr R (by rw [hm]; exact Frame.refl _ _),
    I.rest.trans R⟩
  rw [z₆, r3₅]
  cases accepts s₀ cs <;> rfl

/-- The comparison's pointers and count. -/
theorem rangeInit_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {cs : List Byte}
    (hq : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) (hcs : cs.length = rWidth s₀) :
    WP isa (.block rangeInit) t fun u => RangeInv s₀ t cs (rWidth s₀) u ∧ u.mem = t.mem := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit := rWidth_le s₀
  unfold rangeInit
  refine wp_dp (op2_imm (by decide)) fun t₁ u₁ => wp_ldArg A (h.upd u₁) (j := 2) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ld (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ u₄ =>
    wp_ld ((((h.upd u₁).upd u₂).upd u₃).upd u₄) (by decide) fun t₅ u₅ => wp_dp (op2_reg _ _) fun t₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun t₇ u₇ => wp_mov (op2_imm (by decide)) fun t₈ u₈ => WP.block_nil ?_
  have R : Rest rangeRegs t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    (u₈.rest (by decide))))))))
  have m₈ : t₈.mem = t.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hcsd : cs.drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by omega)
  have hqd : (qSig s₀).drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by rw [qSig_length])
  refine ⟨⟨h.congr R (by rw [m₈]; exact Frame.refl _ _), m₈, ?_, ?_, ?_, ?_, ?_, ?_, R⟩, m₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, R.gpr .r11 (by decide)]
    show t₂.gpr .r4 + t₂.gpr .r0 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    show t.gpr .r11 + BitVec.ofNat 32 oNonce + stackArg s₀ 2 = _
    rw [show stackArg s₀ 2 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      Offset.add_add]
    unfold drawPlace; congr 2; omega
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
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine WP.mono (rangeByte_ok A hcs (by omega) hnonce J) fun v ⟨J', z⟩ => ?_
  by_cases hj : j = 0
  · left
    subst hj
    exact ⟨by rw [eval_ne, z]; rfl, WP.mono (rangeFinish_ok hcs J') fun u ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false hj]; rfl, j, by omega, j, rfl, by omega, by omega, J'⟩

end VG.Proof.Dsa.Arm
