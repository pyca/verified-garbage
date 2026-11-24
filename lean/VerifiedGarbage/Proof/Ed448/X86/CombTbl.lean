module

public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# edwards448's base-point multiplication on x86 (32-bit): the comb's tables in a static

Untrusted: everything here is checked by Lean. The words of the static
`combSym`, as a contract states them (`CombHeld`), and a memory holding them for
contracts' witnesses (`satMemWith`). Kept apart from the selection's proof, so
that the callers' contracts need none of its algebra.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86

theorem combWords_length : combWords.length = 57 * 112 := by simp [combWords]

theorem combWords_getD {i : Nat} (hi : i < 57 * 112) : combWords.getD i 0 = combWord i := by
  simp [combWords, List.getD_eq_getElem?_getD, hi]

/-! ## A static -/

/-- The region of the words `ws` at `T`. -/
abbrev StR (ws : List (BitVec 64)) (T : Addr) : Region := ⟨T, 8 * ws.length⟩

/-- The words `ws` at `T` in `m`. -/
def StWords (ws : List (BitVec 64)) (T : Addr) (m : Mem) : Prop :=
  ∀ i < ws.length, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0

/-- The static `sym`, of the words `ws`, in `s`, as a contract states it: its words, not
wrapping around the 32-bit address space, apart from the regions `wr`. -/
def StHeld (sym : String) (ws : List (BitVec 64)) (s : State) (wr : List Region) : Prop :=
  StWords ws ((s.syms sym).setWidth 64) s.mem ∧
  (s.syms sym).toNat + 8 * ws.length ≤ 2 ^ 32 ∧
  ∀ r ∈ wr, (StR ws ((s.syms sym).setWidth 64)).Disjoint r

/-- The words survive writes apart from them. -/
theorem StWords.frame {ws : List (BitVec 64)} {T : Addr} {m m' : Mem} (h : StWords ws T m)
    (hl : 8 * ws.length < 2 ^ 64) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (StR ws T).Disjoint r) : StWords ws T m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (r := StR ws T) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hl])) hd (by decide)

/-- The memory of a contract's witness: `ws` at `0x100000`, and `m` elsewhere
(irreducible: unfolding it in a definitional check would evaluate the tables). -/
@[irreducible] def satWith (ws : List (BitVec 64)) (m : Mem) : Mem := fun a =>
  if (a - 0x100000).toNat < 8 * ws.length then constMem 0x100000 ws a else m a

theorem satWith_held (ws : List (BitVec 64)) (hl : 8 * ws.length < 2 ^ 64) (m : Mem) :
    StWords ws 0x100000 (satWith ws m) := by
  intro i hi
  have hm : (satWith ws m).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 ws).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat =
        8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hl, hj])]
    unfold satWith
    rw [e, ite_eq_left (show 8 * i + j < 8 * ws.length by omega_using [hi, hj])]
  exact hm.trans (constMem_held 0x100000 ws (by omega_using [hl]) i hi)

/-- Outside the words, the witness's memory is `m`. -/
theorem satWith_out (ws : List (BitVec 64)) (m : Mem) {a : Addr} (ha : 8 * ws.length ≤ (a - 0x100000).toNat) :
    satWith ws m a = m a := by
  unfold satWith
  rw [ite_eq_right (by omega_using [ha])]

/-! ## The comb's tables -/

/-- The region of the comb's tables at `T`. -/
abbrev TblR (T : Addr) : Region := StR combWords T

/-- The comb's words at `T` in `m`. -/
abbrev TblWords (T : Addr) (m : Mem) : Prop := StWords combWords T m

/-- The comb's tables, the static `combSym`, in `s`, as a contract states them. -/
abbrev CombHeld (s : State) (wr : List Region) : Prop := StHeld combSym combWords s wr

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of a contract's witness: the tables at `0x100000`, and `m` elsewhere. -/
abbrev satMemWith (m : Mem) : Mem := satWith combWords m

theorem satMemWith_held (m : Mem) : TblWords 0x100000 (satMemWith m) :=
  satWith_held _ (by rw [combWords_length]; decide) m

/-- Outside the tables, the witness's memory is `m`. -/
theorem satMemWith_out (m : Mem) {a : Addr} (ha : 8 * 57 * 112 ≤ (a - 0x100000).toNat) :
    satMemWith m a = m a :=
  satWith_out _ m (by rw [combWords_length]; omega_using [ha])

end VG.Proof.Ed448.X86
