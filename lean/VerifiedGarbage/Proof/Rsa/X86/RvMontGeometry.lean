module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps
public import VerifiedGarbage.Proof.Dsa.Frame

/-! # Montgomery arithmetic within the prime-recovery workspace

The accumulator occupies arrays 16 and 17. Arrays 20 and 22 hold the
modulus and subtraction temporary. Operand arrays lie above the accumulator.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev MontIndex (j : Nat) : Prop := 20 ≤ j ∧ j < nArr ∧ j ≠ mTmp

theorem words_eq_num {g : Geo} {m : Mem} {j : Nat}
    (h : num m g.B g.w j < 2 ^ (64 * g.n)) :
    wordsVal m g.B (arr g.w j) g.n = num m g.B g.w j := by
  rw [wordsVal_eq_val32]
  apply VG.Proof.Dsa.val32_prefix_of_lt
  · change 2 * g.n ≤ 2 * g.n + 2; omega
  · simpa only [← Nat.mul_assoc] using h

theorem mont_bytes_fit {g : Geo} {s : State} (h : Ws s g.B g.Z g.w nArr)
    {j : Nat} (hj : j < nArr) : arr g.w j + 8 * g.n ≤ g.Z := by
  have := h.arr_fit hj
  change arr g.w j + 4 * (2 * g.n + 2 + 2) ≤ g.Z at this
  omega

theorem mont_bytes_sep {g : Geo} {i j : Nat} (hij : i ≠ j) :
    arr g.w i + 8 * g.n ≤ arr g.w j ∨ arr g.w j + 8 * g.n ≤ arr g.w i := by
  have := arr_disj (w := g.w) hij
  change arr g.w i + 4 * (2 * g.n + 2 + 2) ≤ arr g.w j ∨
    arr g.w j + 4 * (2 * g.n + 2 + 2) ≤ arr g.w i at this
  omega

theorem mont_acc_end (g : Geo) :
    arr g.w mAcc + accLen (montMod g.n) ≤ arr g.w 18 := by
  simp only [arr, S, Geo.w, width, mAcc, accLen, montMod, VG.Impl.Mont.X86.words]
  omega

theorem mont_layout {g : Geo} {s : State} (h : Ws s g.B g.Z g.w nArr)
    {o a b : Nat} (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) :
    OpLay (montMod g.n) g.Z (arr g.w mAcc) (arr g.w o) (arr g.w a) (arr g.w b) := by
  have acc := mont_acc_end g
  have fit : arr g.w 18 ≤ g.Z := Nat.le_trans (Nat.le_add_right _ _) (h.arr_fit (by decide : 18 < nArr))
  have before (j : Nat) (hj : 18 ≤ j) : arr g.w mAcc + accLen (montMod g.n) ≤ arr g.w j :=
    Nat.le_trans acc (arr_mono hj)
  exact ⟨Nat.le_trans acc fit, mont_bytes_fit h ho.2.1, mont_bytes_fit h ha.2.1,
    mont_bytes_fit h hb.2.1, .inl (before o (by omega)), .inl (before a (by omega)),
    .inl (before b (by omega)), .inl (before mBase (by decide)),
    .inl (before mTmp (by decide)), mont_bytes_sep ho.2.2⟩

/-- The invariant needed by the runtime-modulus multiplication. -/
structure MR (g : Geo) (m : Nat) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  positive : 0 < g.n
  modulus : num s.mem g.B g.w mBase = m
  bound : m < 2 ^ (64 * g.n)
  inverse : (m * w32 s.mem g.B sInv + 1) % 2 ^ 32 = 0

theorem MR.modulusReady {g : Geo} {m : Nat} {s : State} (h : MR g m s) :
    VG.Proof.Mont.X86.Dynamic.Modulus (montMod g.n) g.Z m s.mem g.B :=
  ⟨h.positive, mont_bytes_fit h.ws (by decide : mBase < nArr),
    mont_bytes_fit h.ws (by decide : mTmp < nArr), mont_bytes_sep (by decide : mBase ≠ mTmp),
    (words_eq_num (h.modulus ▸ h.bound)).trans h.modulus⟩

end VG.Proof.Rsa.X86.Recover
