import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519's base-point multiplication on x86: the comb's tables in a static

Untrusted: everything here is checked by Lean. The words of the static
`combSym`, as a contract states them (`CombHeld`), and a memory holding them for
contracts' witnesses (`satMemWith`). Kept apart from the selection's proof, so
that the callers' contracts need none of its algebra.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combWords_length : combWords.length = 32 * 96 := by simp [combWords]

theorem combWords_getD {i : Nat} (hi : i < 32 * 96) : combWords.getD i 0 = combWord i := by
  simp [combWords, List.getD_eq_getElem?_getD, hi]

/-- The region of the comb's tables at `T`. -/
abbrev TBL (T : Addr) : Region := ⟨T, 8 * combWords.length⟩

/-- The comb's words at `T` in `m`. -/
def TblWords (T : Addr) (m : Mem) : Prop :=
  ∀ i < combWords.length, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0

/-- The comb's tables, the static `combSym`, in `s`, as a contract states them: its words, not
wrapping around the 32-bit address space, apart from the regions `wr`. -/
def CombHeld (s : State) (wr : List Region) : Prop :=
  TblWords ((s.syms combSym).setWidth 64) s.mem ∧
  (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 32 ∧
  ∀ r ∈ wr, (TBL ((s.syms combSym).setWidth 64)).Disjoint r

/-- The words survive writes apart from them. -/
theorem TblWords.frame {T : Addr} {m m' : Mem} (h : TblWords T m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (TBL T).Disjoint r) : TblWords T m' := fun i hi => by
  have hl := combWords_length
  rw [← h i hi]
  exact hf.readW (r := TBL T) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of a contract's witness: the tables at `0x100000`, and `m` elsewhere
(irreducible: unfolding it in a definitional check would evaluate the tables). -/
@[irreducible] def satMemWith (m : Mem) : Mem := fun a =>
  if (a - 0x100000).toNat < 8 * combWords.length then constMem 0x100000 combWords a else m a

theorem satMemWith_held (m : Mem) : TblWords 0x100000 (satMemWith m) := by
  intro i hi
  have hl := combWords_length
  have hm : (satMemWith m).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 combWords).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat =
        8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold satMemWith
    rw [e, ite_eq_left (show 8 * i + j < 8 * combWords.length by omega)]
  exact hm.trans (constMem_held 0x100000 combWords (by omega) i hi)

/-- Outside the tables, the witness's memory is `m`. -/
theorem satMemWith_out (m : Mem) {a : Addr} (ha : 8 * 32 * 96 ≤ (a - 0x100000).toNat) :
    satMemWith m a = m a := by
  unfold satMemWith
  rw [ite_eq_right (by rw [combWords_length]; omega)]

end VG.Proof.Ed25519.X86
