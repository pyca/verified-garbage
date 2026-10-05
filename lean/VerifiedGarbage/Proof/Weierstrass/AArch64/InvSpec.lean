import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow

/-!
# Inversion by divsteps on AArch64: what it computes

What the proofs of the functions that invert need, without the algebra of
its proof (`InvMain.lean`): the slots (`InvLay`), what the inversion writes
(`invW`), the configuration's facts about the modulus (`InvOk`: batches
enough for its bits, and the constants), and `InvSound m`, that the
inversion leaves `[acc] = [base]^(m - 2)` (in Montgomery form), which a prime
`m` gives (`invSound_of_prime`). An inversion with a power's slots takes the
power's place (`InvLay.of_chain`, `invW_eq`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

/-- The inversion's slots: the result, the input and the working slots in the
working space, aligned and apart, and the modulus and its temporary area apart from them. -/
structure InvLay (P : InvCfg) (size : Nat) : Prop where
  n4 : 4 ≤ P.M.n
  n10 : P.M.n < 10
  acc : P.acc + 8 * P.M.n ≤ size
  base : P.base + 8 * P.M.n ≤ size
  tbl : P.tbl + 9 * (8 * P.M.n) ≤ size
  acc8 : P.acc % 8 = 0
  base8 : P.base % 8 = 0
  tbl8 : P.tbl % 8 = 0
  mod : ModA P.M
  acc_base : P.acc + 8 * P.M.n ≤ P.base ∨ P.base + 8 * P.M.n ≤ P.acc
  acc_tbl : P.acc + 8 * P.M.n ≤ P.tbl ∨ P.tbl + 9 * (8 * P.M.n) ≤ P.acc
  base_tbl : P.base + 8 * P.M.n ≤ P.tbl ∨ P.tbl + 9 * (8 * P.M.n) ≤ P.base
  acc_tmp : P.acc + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.acc
  tbl_tmp : P.tbl + 9 * (8 * P.M.n) ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.tbl
  mo_acc : P.M.mo + 8 * P.M.n ≤ P.acc ∨ P.acc + 8 * P.M.n ≤ P.M.mo
  mo_tbl : P.M.mo + 8 * P.M.n ≤ P.tbl ∨ P.tbl + 9 * (8 * P.M.n) ≤ P.M.mo
  mo_tmp : P.M.mo + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.M.mo
  base_mo : P.base + 8 * P.M.n ≤ P.M.mo ∨ P.M.mo + 8 * P.M.n ≤ P.base

theorem InvLay.mo8 {P : InvCfg} {size : Nat} (h : InvLay P size) : P.M.mo % 8 = 0 := h.mod.mo

/-- What the inversion writes: the result, the slots and the modulus's temporary area. -/
def invW (P : InvCfg) : List (Nat × Nat) :=
  [(P.acc, 8 * P.M.n), (P.tbl, 9 * (8 * P.M.n)), (P.M.tmp, 8 * P.M.n)]

/-- The inversion is the modulus's: batches enough for its divsteps to end
(`590` for up to 4 words, `885` for up to 6, `1328` for up to 9), counts the loop can take, and
the constants `C = 2^(5 B) R³ mod m` and `Cn = m - C`. -/
structure InvOk (P : InvCfg) (m : Nat) : Prop where
  B1 : 1 ≤ P.B
  B16 : P.B < 2 ^ 16
  C : P.C = 2 ^ (5 * P.B) * (2 ^ (64 * P.M.n)) ^ 3 % m
  Cpos : 0 < P.C
  Cn : P.Cn = m - P.C
  bound : (P.M.n ≤ 4 ∧ 590 ≤ 59 * P.B) ∨ (P.M.n ≤ 6 ∧ 885 ≤ 59 * P.B) ∨ (P.M.n ≤ 9 ∧ 1328 ≤ 59 * P.B)

/-- The inversion modulo `m` leaves `[acc] = [base]^(m - 2)` (in Montgomery form). -/
def InvSound (m : Nat) [NeZero m] : Prop :=
  ∀ {P : InvCfg} {base : Addr} {size : Nat}, InvLay P size → 2 < m → UnitMod m (2 ^ (64 * P.M.n)) →
    ∀ {s : State}, Scr s base size → ModOkA P.M size m s.mem base → wordsVal s.mem base P.base P.M.n < m →
      InvOk P m → WP isa (InvCfg.inv P) s fun s' =>
        KeepRegs (powClob P.M.n) s s' ∧ Unch base (invW P) s.mem s'.mem ∧
        wordsVal s'.mem base P.acc P.M.n < m ∧
        toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
          toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2)

theorem ofMod_C (M : Mod) (acc base tbl m : Nat) :
    (InvCfg.ofMod M acc base tbl m).C =
      2 ^ (5 * (InvCfg.ofMod M acc base tbl m).B) * (2 ^ (64 * M.n)) ^ 3 % m := rfl

theorem ofMod_Cn (M : Mod) (acc base tbl m : Nat) :
    (InvCfg.ofMod M acc base tbl m).Cn = m - (InvCfg.ofMod M acc base tbl m).C := rfl

/-- `InvOk` for `InvCfg.ofMod`: its constant nonzero, and its batches for the modulus's words. -/
theorem InvOk.ofMod {M : Mod} {acc base tbl m : Nat} (hC : 0 < (InvCfg.ofMod M acc base tbl m).C)
    (hn : M.n ≤ 9) : InvOk (InvCfg.ofMod M acc base tbl m) m := by
  refine ⟨?_, ?_, ofMod_C _ _ _ _ _, hC, ofMod_Cn _ _ _ _ _, ?_⟩ <;>
    simp only [InvCfg.ofMod] <;> split <;> (try split) <;> omega

/-- The power with an inversion's slots. -/
def _root_.VG.Impl.Weierstrass.AArch64.InvCfg.toChain (P : InvCfg) : ChainCfg :=
  ⟨P.M, P.acc, P.base, P.tbl, 1, []⟩

theorem invW_eq (P : InvCfg) : invW P = chainW P.toChain := rfl

theorem InvLay.of_chain {P : InvCfg} {size : Nat} (h : ChainLay P.toChain size) (h4 : 4 ≤ P.M.n)
    (h7 : P.M.n < 10) : InvLay P size := by
  have mo := h.mo_w
  simp only [chainW, InvCfg.toChain, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mo
  exact ⟨h4, h7, h.acc, h.base, h.tbl, h.acc8, h.base8, h.tbl8, h.mod, h.acc_base, h.acc_tbl, h.base_tbl,
    h.acc_tmp, h.tbl_tmp, mo.1, mo.2.1, mo.2.2, h.base_mo⟩

end VG.Proof.Weierstrass.AArch64
