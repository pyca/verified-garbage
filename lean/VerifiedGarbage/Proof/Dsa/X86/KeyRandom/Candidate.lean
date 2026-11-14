module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Copy
public import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.Encoding

/-! ### `Dsa.X86.KeyRandom.InRange`, which only this module used -/

section

/-!
# Whether a candidate is in range (x86)

`inRange` compares the `width` candidate bytes at the draw's place in the
scalar with q's significant bytes, from their ends: `ebx` is the borrow of
the candidate minus q (`randomBorrow`) and `edi` the OR of the candidate's
bytes. `rangeFinish` leaves `ebx = 1` exactly when the candidate is nonzero
and below q.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- q's significant bytes. -/
abbrev qSig (s₀ : State) : List Byte := (rQBytes s₀).drop ((rQBytes s₀).length - rWidth s₀)

/-- The comparison after the last `width - k` bytes. -/
structure RangeInv (s₀ t₀ : State) (cs : List Byte) (k : Nat) (t : State) : Prop where
  ready : Ready s₀ t
  mem : t.mem = t₀.mem
  edx : t.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (drawPlace s₀ + k)
  esi : t.gpr .esi = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  ebx : t.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Dsa.randomBorrow (cs.drop k) ((qSig s₀).drop k))
  edi : (t.gpr .edi).toNat < 256
  ediz : t.gpr .edi = 0 ↔ ∀ b ∈ cs.drop k, b = 0
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t₀ t

/-- The borrow out of `a - (b + c)`, by its sign bit. -/
theorem borrow_bit {a x : Nat} (ha : a < 256) (hx : x ≤ 256) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 x) >>> 31 = BitVec.ofNat 32 (if a < x then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega_arith), Nat.mod_eq_of_lt (a := x) (by omega_arith), Nat.shiftRight_eq_div_pow]
  split <;> rw [BitVec.toNat_ofNat] <;> omega_arith

theorem toNat_setWidth8 (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide : 2 ^ 8 ≤ 2 ^ 32))]

theorem ofNat_add_one_sub {x : BitVec 32} {c : Nat} (hc : c + 1 < 2 ^ 32) :
    x + BitVec.ofNat 32 (c + 1) - 1 = x + BitVec.ofNat 32 c := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_sub32 _ (by omega_arith) hc]; rfl

/-- One byte, from the end. -/
theorem rangeByte_ok {s₀ t₀ t : State} (A : KeyABI s₀) {cs : List Byte} {k : Nat}
    (hcs : cs.length = rWidth s₀) (hk : k < rWidth s₀)
    (hnonce : ∀ i < rWidth s₀, t₀.mem (off (rBase s₀) (drawPlace s₀ + i)) = cs.getD i 0)
    (I : RangeInv s₀ t₀ cs (k + 1) t) :
    WP isa (.block rangeByte) t fun u => RangeInv s₀ t₀ cs k u ∧ u.zf = some (decide (k = 0)) := by
  have hF : KeyRandom.frameBytes = 120 := rfl
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hq := I.ready.q A
  have hqfit := hq.fit
  have hrf := I.ready.rf
  unfold rangeByte borrow
  simp only [List.cons_append, List.nil_append]
  refine wp_subi fun t₁ u₁ _ _ => wp_subi fun t₂ u₂ _ _ => ?_
  have e₂ : t₂.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (drawPlace s₀ + k) := by
    rw [u₂.other _ (by decide), u₁.gpr, I.edx, show drawPlace s₀ + (k + 1) = drawPlace s₀ + k + 1 from rfl,
      ofNat_add_one_sub (by unfold drawPlace oNonce; omega_arith)]
  have s₂ : t₂.gpr .esi = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀ + k) := by
    rw [u₂.gpr, u₁.other _ (by decide), I.esi, show (rQBytes s₀).length - rWidth s₀ + (k + 1) =
      (rQBytes s₀).length - rWidth s₀ + k + 1 from rfl, ofNat_add_one_sub (by omega_arith)]
  have esp₂ : t₂.gpr .esp = t.gpr .esp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have hn := hnonce k hk
  rw [← I.mem] at hn
  refine wp_load8 (a := off (rBase s₀) (drawPlace s₀ + k))
    (by rw [ea_at0, e₂]; exact hrf.ptr (by unfold argOff drawPlace oNonce; omega_arith))
    (hrf.read (d := drawPlace s₀ + k) (n := 1) (by unfold drawPlace oNonce; omega_arith) |> fun h => by
      rw [u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact h) fun t₃ u₃ _ _ => ?_
  rw [u₂.mem, u₁.mem, hn] at u₃
  refine wp_or fun t₄ u₄ => ?_
  have hqi : (rQBytes s₀).length - rWidth s₀ + k < (rQBytes s₀).length := by omega_arith
  refine wp_load8 (a := (rQ s₀).setWidth 64 + BitVec.ofNat 64 ((rQBytes s₀).length - rWidth s₀ + k))
    (by rw [ea_at0, u₄.other _ (by decide), u₃.other _ (by decide), s₂]; exact ptr_add (by omega_arith))
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hq.rd _ hqi)
    fun t₅ u₅ _ _ => ?_
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hq.val _ hqi] at u₅
  refine wp_add fun t₆ u₆ _ => wp_sub fun t₇ u₇ _ => wp_shr (by decide) fun t₈ u₈ _ =>
    wp_mov fun t₉ u₉ => wp_subi fun t₁₀ u₁₀ _ z₁₀ => WP.block_nil ?_
  -- The values.
  have hc := VG.Proof.Dsa.randomBorrow_le (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
  have hcs' : k < cs.length := by omega_arith
  have hqs' : k < (qSig s₀).length := by simp only [qSig, List.length_drop]; omega_arith
  have hqk : (qSig s₀)[k] = (rQBytes s₀)[(rQBytes s₀).length - rWidth s₀ + k] := by
    simp only [qSig, List.getElem_drop]
  have hdrop : ∀ (l : List Byte) (h : k < l.length), l.drop k = l[k] :: l.drop (k + 1) := fun l h => by
    rw [List.drop_eq_getElem_cons h]
  have hb : VG.Proof.Dsa.randomBorrow (cs.drop k) ((qSig s₀).drop k) =
      if (cs[k]).toNat < ((qSig s₀)[k]).toNat + VG.Proof.Dsa.randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1))
      then 1 else 0 := by
    rw [hdrop cs hcs', hdrop (qSig s₀) hqs', VG.Proof.Dsa.randomBorrow]
  have hcg : cs.getD k 0 = cs[k] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcs', Option.getD_some]
  have eax₇ : t₇.gpr .eax = (cs[k].setWidth 32) - (((qSig s₀)[k]).setWidth 32 +
      BitVec.ofNat 32 (VG.Proof.Dsa.randomBorrow (cs.drop (k + 1)) ((qSig s₀).drop (k + 1)))) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .eax (by decide), u₅.gpr, u₅.other .eax (by decide),
      u₅.other .ebx (by decide), u₄.other .eax (by decide), u₄.other .ebx (by decide), u₃.gpr,
      u₃.other .ebx (by decide), u₂.other .ebx (by decide), u₁.other .ebx (by decide), I.ebx, ← hcg, hqk]
  have toOfNat : ∀ b : Byte, b.setWidth 32 = BitVec.ofNat 32 b.toNat := fun b => by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hc' := hc
  rw [toOfNat, toOfNat, BitVec.ofNat_add_ofNat] at eax₇
  have kk : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t t₁₀ :=
    (((((((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))).trans
      (u₇.keeps.mono (by decide))).trans (u₈.keeps.mono (by decide))).trans (u₉.keeps.mono (by decide))).trans
      (u₁₀.keeps.mono (by decide))
  have hm : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edi₁₀ : t₁₀.gpr .edi = t.gpr .edi ||| cs[k].setWidth 32 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hcg]
  refine ⟨⟨I.ready.congr kk (by rw [hm]; exact Frame.refl _ _), hm.trans I.mem, ?_, ?_, ?_, ?_, ?_, ?_,
    I.keeps.trans kk⟩, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂,
      kk.1 .esp (by decide)]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), s₂]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), I.ecx, ofNat_pred (Nat.le_add_left 1 k)]; rfl
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, eax₇, borrow_bit (BitVec.isLt _) (by omega_arith), hb]
  · rw [edi₁₀, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 8) I.edi (by rw [toNat_setWidth8]; exact BitVec.isLt _)
  · have key : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
    rw [edi₁₀, key, hdrop cs hcs', I.ediz, List.forall_mem_cons]
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
      u₂.other _ (by decide), u₁.other _ (by decide), I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

theorem qSig_length {s₀ : State} : (qSig s₀).length = rWidth s₀ := by
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  simp only [qSig, List.length_drop]; omega_arith

/-- Whether the candidate `cs` is accepted: nonzero and below q. -/
def accepts (s₀ : State) (cs : List Byte) : Bool :=
  decide (0 < Spec.Dsa.decodeBE cs ∧ Spec.Dsa.decodeBE cs < Spec.Dsa.decodeBE (qSig s₀))

theorem rangeFinish_ok {s₀ t₀ t : State} {cs : List Byte} (hcs : cs.length = rWidth s₀)
    (I : RangeInv s₀ t₀ cs 0 t) :
    WP isa (.block rangeFinish) t fun u => u.gpr .ebx = (if accepts s₀ cs then 1 else 0) ∧
      u.zf = some (!accepts s₀ cs) ∧ u.mem = t₀.mem ∧ Ready s₀ u ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t₀ u := by
  unfold rangeFinish
  refine wp_movS rfl fun t₁ u₁ _ => wp_subS (src := .reg .edi) rfl fun t₂ u₂ c₂ => ?_
  refine wp_sbb_self c₂ fun t₃ u₃ => wp_and fun t₄ u₄ => wp_test fun t₅ f₅ z₅ => WP.block_nil ?_
  have hb := VG.Proof.Dsa.randomBorrow_eq cs (qSig s₀) (by rw [hcs, qSig_length])
  have hz : (t.gpr .edi = 0) ↔ Spec.Dsa.decodeBE cs = 0 := by
    rw [VG.Proof.Dsa.decodeBE_eq_zero]; simpa only [List.drop_zero] using I.ediz
  have edi : t₁.gpr .edi = t.gpr .edi := u₁.other _ (by decide)
  have ebx₄ : t₄.gpr .ebx = (if accepts s₀ cs then 1 else 0) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), I.ebx,
      u₁.gpr, edi]
    simp only [List.drop_zero, hb]
    unfold accepts
    have h0 : (0 < (t.gpr .edi).toNat) ↔ 0 < Spec.Dsa.decodeBE cs := by
      rw [Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, ne_eq, ne_eq, ← hz]
      exact not_congr ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
    by_cases hp : 0 < Spec.Dsa.decodeBE cs <;> by_cases hl : Spec.Dsa.decodeBE cs < Spec.Dsa.decodeBE (qSig s₀) <;>
      simp [hp, hl, h0]
  have kk : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t t₅ :=
    ((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (f₅.keeps _)
  have hm : t₅.mem = t.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [f₅.gpr]; exact ebx₄, ?_, hm.trans I.mem, I.ready.congr kk (by rw [hm]; exact Frame.refl _ _),
    I.keeps.trans kk⟩
  rw [z₅, ebx₄, BitVec.and_self]
  cases accepts s₀ cs <;> rfl

/-- The comparison's pointers and count. -/
theorem rangeInit_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {cs : List Byte}
    (hq : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) (hcs : cs.length = rWidth s₀) :
    WP isa (.block rangeInit) t fun u => RangeInv s₀ t cs (rWidth s₀) u ∧ u.mem = t.mem := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold rangeInit
  refine wp_movS rfl fun t₁ u₁ _ => wp_addi fun t₂ u₂ => ?_
  have h₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_addS (h₂.argSrc A (j := 6) (by decide)) fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_movS (v := rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (by rw [h₃.rf.readSlot (by decide), u₃.mem, u₂.mem, u₁.mem]; exact congrArg some hq) fun t₄ u₄ _ => ?_
  have h₄ := h₃.upd u₄ (by decide)
  refine wp_movS (v := BitVec.ofNat 32 (rWidth s₀))
    (by rw [h₄.rf.readSlot (by decide), u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact congrArg some hw)
    fun t₅ u₅ _ => wp_add fun t₆ u₆ _ => wp_movS rfl fun t₇ u₇ _ => wp_movS rfl fun t₈ u₈ _ =>
      WP.block_nil ?_
  have k₈ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t t₈ :=
    (((((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))).trans
      (u₇.keeps.mono (by decide))).trans (u₈.keeps.mono (by decide))
  have m₈ : t₈.mem = t.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hcsd : cs.drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by omega_arith)
  have hqd : (qSig s₀).drop (rWidth s₀) = [] := List.drop_eq_nil_of_le (by rw [qSig_length])
  have I₀ : RangeInv s₀ t cs (rWidth s₀) t₈ := by
    refine ⟨h.congr k₈ (by rw [m₈]; exact Frame.refl _ _), m₈, ?_, ?_, ?_, ?_, ?_, ?_, k₈⟩
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, k₈.1 .esp (by decide),
        show X86.arg s₀ 6 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        Offset.add_add]
      unfold drawPlace; congr 2; omega_arith
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₅.gpr,
        Offset.add_add]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    · rw [u₈.other _ (by decide), u₇.gpr, hcsd, hqd]; rfl
    · rw [u₈.gpr]; decide
    · rw [u₈.gpr, hcsd]; simp
  exact ⟨I₀, m₈⟩

theorem inRange_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {cs : List Byte}
    (hq : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀))
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hcs : cs.length = rWidth s₀) (hw1 : 1 ≤ rWidth s₀)
    (hnonce : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) = cs.getD i 0) :
    WP isa inRange t fun u => u.gpr .ebx = (if accepts s₀ cs then 1 else 0) ∧
      u.zf = some (!accepts s₀ cs) ∧ u.mem = t.mem ∧ Ready s₀ u ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t u := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold inRange
  refine WP.seq (WP.mono (rangeInit_ok A h hq hw hcs) fun t₈ ⟨I₀, _⟩ => ?_)
  -- The loop.
  refine WP.seq (WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = k ∧ 1 ≤ k ∧ k ≤ rWidth s₀ ∧
      RangeInv s₀ t cs k u) (fun n u hu => ?_) (rWidth s₀) t₈ ⟨_, rfl, hw1, Nat.le_refl _, I₀⟩)
  · obtain ⟨k, hn, hk1, hk, J⟩ := hu
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
    refine WP.mono (rangeByte_ok A hcs (by omega_arith) hnonce J) fun v ⟨J', z⟩ => ?_
    by_cases hj : j = 0
    · left
      subst hj
      exact ⟨by simp only [eval, z, decide_true, Option.map_some, Bool.not_true],
        WP.mono (rangeFinish_ok hcs J') fun u ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩
    · right
      exact ⟨by simp only [eval, z, hj, decide_false, Option.map_some, Bool.not_false], j, by omega_arith,
        j, rfl, by omega_arith, by omega_arith, J'⟩

end VG.Proof.Dsa.X86.KeyRandom

end

end


/-!
# The copied draw is the specification's candidate (x86)

The bytes `copy` leaves at the draw's place (`copiedList`) decode to the
candidate of FIPS 186-4's rejection sampling, `inRange` accepts exactly the
candidates in `[1, q)`, and the whole `q_len`-byte scalar, with its zero
padding, encodes the candidate.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- q, as the specification reads it. -/
abbrev rq (s₀ : State) : Nat := Spec.Dsa.decodeBE (rQBytes s₀)

theorem qSig_decode (s₀ : State) : Spec.Dsa.decodeBE (qSig s₀) = rq s₀ :=
  VG.Proof.Dsa.random_significant_drop _

theorem rWidth_eq (s₀ : State) : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ :=
  VG.Proof.Dsa.random_drawBytes_scan _

/-- The candidate's bytes. -/
def copiedList (bs : List Byte) (mask : BitVec 32) (w : Nat) : List Byte :=
  (List.range w).map (copied bs mask)

theorem copiedList_length (bs : List Byte) (mask : BitVec 32) (w : Nat) : (copiedList bs mask w).length = w := by
  simp [copiedList]

theorem copiedList_getD (bs : List Byte) (mask : BitVec 32) {w i : Nat} (hi : i < w) :
    (copiedList bs mask w).getD i 0 = copied bs mask i := by
  simp [copiedList, List.getD_eq_getElem?_getD, hi]

theorem copiedList_eq {b : Byte} {bs : List Byte} (mask : BitVec 32) :
    copiedList (b :: bs) mask (bs.length + 1) = ((b.setWidth 32 &&& mask).setWidth 8) :: bs := by
  apply List.ext_getElem
  · simp [copiedList]
  · intro i h₁ h₂
    simp only [copiedList, List.getElem_map, List.getElem_range, copied]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ]
      simp only [List.length_cons] at h₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < bs.length by omega_using [h₂])]

/-- The leading byte's mask, as `random_candidate_mask` states it. -/
theorem masked_head (s₀ : State) (b : Byte) (hpos : 0 < rWidth s₀) :
    (b.setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8 =
      b &&& BitVec.ofNat 8 (2 ^ ((rLead s₀).toNat.log2 + 1) - 1) := by
  have hb : 0 < (rLead s₀).toNat := by
    have hn := VG.Proof.Dsa.significant_nonzero (rQBytes s₀)
    have hz : (rLead s₀).toNat ≠ 0 := by
      intro he
      have h0 : rWidth s₀ = 0 := hn.mpr (BitVec.eq_of_toNat_eq he)
      omega_using [hpos, h0]
    omega_using [hz]
  have hlog : (rLead s₀).toNat.log2 + 1 ≤ 8 := by
    have h := (Nat.log2_lt (by omega_using [hb])).mpr (rLead s₀).isLt
    omega_using [h]
  rw [maskValue_eq _ hb (rLead s₀).isLt, BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq, BitVec.setWidth_ofNat_of_le (by decide)]

/-- The copied bytes decode to the candidate. -/
theorem copied_candidate (s₀ : State) {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    Spec.Dsa.decodeBE (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      Spec.Dsa.Random.candidate (rq s₀) bs := by
  obtain ⟨b, tl, rfl⟩ : ∃ b tl, bs = b :: tl := by
    cases bs with
    | nil => simp at hl; omega
    | cons b tl => exact ⟨b, tl, rfl⟩
  have hw : tl.length + 1 = rWidth s₀ := by simpa using hl
  rw [← hw, copiedList_eq, masked_head s₀ b hpos, VG.Proof.Dsa.random_candidate_mask _ b tl hw]

theorem accepts_candidate (s₀ : State) {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    accepts s₀ (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      decide (0 < Spec.Dsa.Random.candidate (rq s₀) bs ∧ Spec.Dsa.Random.candidate (rq s₀) bs < rq s₀) := by
  rw [accepts, copied_candidate s₀ hl hpos, qSig_decode]

theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons]
    exact ih

/-- The whole scalar, its padding and the candidate's bytes, encodes the candidate. -/
theorem nonce_encodes {s₀ : State} (A : KeyABI s₀) {m : Mem} {bs : List Byte}
    (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀)
    (hpad : ∀ i < (rQBytes s₀).length - rWidth s₀, m (off (rBase s₀) (oNonce + i)) = 0)
    (hc : ∀ i < rWidth s₀, m (off (rBase s₀) (drawPlace s₀ + i)) = copied bs (maskValue (rLead s₀).toNat) i) :
    Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length (Spec.Dsa.Random.candidate (rq s₀) bs) := by
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  let cs := copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)
  let pad := (rQBytes s₀).length - rWidth s₀
  let padded := List.replicate pad (0 : Byte) ++ cs
  have hpLen : padded.length = (rQBytes s₀).length := by
    simp only [padded, cs, List.length_append, List.length_replicate, copiedList_length]; omega_using [hfit]
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
      · have hk : i - pad < rWidth s₀ := by simp only [hpLen] at hj; omega_using [hpos, hj]
        rw [show oNonce + i = drawPlace s₀ + (i - pad) by unfold drawPlace; omega_using [hip], hc _ hk]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := cs) (i := i)
          (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip), List.length_replicate]
        simp only [cs, copiedList, List.getElem_map, List.getElem_range]
  rw [hpBytes, ← hpLen, ← copied_candidate s₀ hl hpos, ← decode_padding cs pad,
    VG.Proof.Dsa.encodeBE_decodeBE]

end VG.Proof.Dsa.X86.KeyRandom
