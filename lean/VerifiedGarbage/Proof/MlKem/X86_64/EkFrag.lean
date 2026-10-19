module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
public import VerifiedGarbage.Proof.MlKem.HSponge
import VerifiedGarbage.Proof.MlKem.X86_64.S4Absorb
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, what does not depend on the layout

The facts about `pad(ek)` and its blocks (`blk`, `hbE`), the sponge's state
after them (`hstate_blk`, `habs_blk`), and the pieces of code
(`zeros_ok`, `mov0_ok`) that `kemEncaps16`'s fragments use
(`EkFrag16.lean`), whatever the layout.
-/

@[expose] public section
namespace VG.Proof.MlKem.X86_64.EkF

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.Sha3 (xorAt)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs)
open VG.Proof.MlKem.HSponge (hstate padBlock)

/-! ## The blocks of `pad(ek)` -/

/-- Block `t` of `pad(E)`, for `E` that does not end at a block boundary. -/
def blk (E : List Byte) (t : Nat) : List Byte :=
  if 136 * t + 136 ≤ E.length then (E.drop (136 * t)).take 136 else padBlock (E.drop (136 * t))

/-- `E`'s length leaves a partial last block, with room for the padding. -/
def Partial (E : List Byte) : Prop := 0 < E.length % 136 ∧ E.length % 136 < 135

theorem hstate_blk {E : List Byte} (hE : Partial E) {t : Nat} (ht : t ≤ E.length / 136) :
    keccakF (xorAt (hstate E t) 0 (blk E t)) = hstate E (t + 1) := by
  unfold blk
  split
  · exact HSponge.hstate_full (by omega)
  · have := Nat.div_add_mod E.length 136
    exact HSponge.hstate_padBlock (by obtain ⟨h1, h2⟩ := hE; omega) (by obtain ⟨h1, h2⟩ := hE; omega)

theorem habs_blk {E : List Byte} (hE : Partial E) {i : Nat} (hi : 3 * i + 3 ≤ E.length / 136 + 1) :
    SH.habs (hstate E (3 * i)) (fun j => blk E (3 * i + j)) 3 = hstate E (3 * i + 3) := by
  simp only [SH.habs, Nat.add_zero]
  rw [hstate_blk hE (by omega), hstate_blk hE (by omega), hstate_blk hE (by omega)]

/-! ## The sponge's state -/

theorem stateAt_keep {rbs wbs : List (Reg × Nat)} {s s' : State} (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) {p : Ptr} (hc : keepB (rbs ++ wbs) ws p 200 = true) :
    stateAt s'.mem (pa s' p) = stateAt s.mem (pa s p) := by
  have e := Lx.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at e ⊢
  refine VG.Proof.Sha3.stateAt_congr fun i hi => ?_
  have := congrArg (fun l => l[i]?) e
  simpa [bytesAt, List.getElem?_map, List.getElem?_range hi] using this

/-! ## Zeros and the padding -/


theorem zeros_ok (b : Reg) (off n : Nat) (s : State) (h0 : s.gpr .rax = 0) (hn : 8 * n < 2 ^ 64)
    (hw : ∀ j < n, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => [.store (at_ b (off + 8 * j)) .rax])) s fun s' =>
      Keep [] s s' ∧ Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
        ∀ i < 8 * n, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0 := by
  refine wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hb : s'.gpr b = s.gpr b := hk'.1 b (by simp)
  have ha : s'.gpr .rax = 0 := by rw [hk'.1 .rax (by simp), h0]
  have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine WP.mono (zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
    fun s'' ⟨hm, hk''⟩ => ⟨(hk'.trans hk'').mono (by simp), ?_, fun i hi => ?_⟩
  · rw [hm, hb, e]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, hb, e, ha]
    simp only [Mem.writeW, Mem.write]
    split
    · simp
    · rename_i hc
      refine hz i (Nat.lt_of_not_le fun hik => hc ?_)
      rw [Offset.sub_toNat _ hik (by omega)]
      omega

theorem mov0_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem) ?_ (by rfl))
    fun s' ⟨⟨h0, hm⟩, k⟩ => ⟨h0, hm, k⟩
  xrun []

theorem padList (n : Nat) (a b : Byte) :
    ((List.replicate (n + 2) (0 : Byte)).set 0 a).set (n + 1) b = a :: (List.replicate n 0 ++ [b]) := by
  rw [List.replicate_succ, List.set_cons_zero, List.set_cons_succ, List.replicate_succ', List.set_append_right _ _ (by simp),
    List.length_replicate, Nat.sub_self, List.set_cons_zero]

/-! ## The blocks of a fragment -/

/-- The 408 bytes of `pad(E)` from `408 i`, for `E` whose last block ends in fragment `i` or later. -/

def hbE (E : List Byte) (i : Nat) : List Byte :=
  if 408 * i + 408 ≤ E.length then (E.drop (408 * i)).take 408
  else E.drop (408 * i) ++ BitVec.ofNat 8 6 :: (List.replicate (406 - (E.length - 408 * i)) 0 ++ [BitVec.ofNat 8 0x80])

theorem hbE_blk {E : List Byte} {i j : Nat} (hj : j < 3)
    (hp : 408 * i + 408 ≤ E.length ∨ (272 < E.length - 408 * i ∧ E.length - 408 * i < 406)) :
    ((hbE E i).drop (136 * j)).take 136 = blk E (3 * i + j) := by
  unfold hbE blk
  split
  · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega), List.drop_take, List.take_take, List.drop_drop]
    rw [show 408 * i + 136 * j = 136 * (3 * i + j) by omega, Nat.min_eq_left (by omega)]
  · rename_i hn
    have hA : (E.drop (408 * i)).length = E.length - 408 * i := List.length_drop
    rcases (by omega : j < 2 ∨ j = 2) with hj2 | rfl
    · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega), List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega), List.drop_drop,
        show 408 * i + 136 * j = 136 * (3 * i + j) by omega]
    · rw [ite_eq_right (show ¬136 * (3 * i + 2) + 136 ≤ E.length by omega), List.drop_append_of_le_length (by omega), List.drop_drop,
        List.take_of_length_le (by simp only [List.length_append, List.length_drop, List.length_cons,
          List.length_replicate, List.length_nil]; omega)]
      simp only [padBlock, List.length_drop, List.append_assoc, List.cons_append, List.nil_append,
        show 408 * i + 136 * 2 = 136 * (3 * i + 2) by omega,
        show 134 - (E.length - 136 * (3 * i + 2)) = 406 - (E.length - 408 * i) by omega]

/-! ## The entries of a fragment -/

theorem allOk_add3 {k : Nat} {ρ : List Byte} {e : Nat} :
    allOk k ρ (e + 3) ↔ allOk k ρ e ∧ ((List.range 3).all fun t =>
      (sampleNTT minIterations (matSeed ρ ((e + t) / k) ((e + t) % k))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun t ht => h (e + t) (by omega)⟩
  · rintro ⟨h, h3⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h3 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

theorem habs_congr (H : Spec.Sha3.State) {f g : Nat → List Byte} :
    ∀ n, (∀ j < n, f j = g j) → SH.habs H f n = SH.habs H g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [SH.habs]
    rw [habs_congr H n fun j hj => h j (by omega), h n (by omega)]

/-- Code whose runs are never related. -/
theorem relFalse {P Q : State → State → Prop} {c : Prog isa} (h : ∀ x y, P x y → False) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp _ _ => (h _ _ hp).elim

end VG.Proof.MlKem.X86_64.EkF
