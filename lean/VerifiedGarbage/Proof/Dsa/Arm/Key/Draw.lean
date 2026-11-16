module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Copy
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.Arm.Key.Prepare
import VerifiedGarbage.Proof.Dsa.Arm.Key.Scan
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom
import VerifiedGarbage.Proof.Framework.Arm.Reduce

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
