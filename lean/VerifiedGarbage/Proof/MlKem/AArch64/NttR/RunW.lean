module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on AArch64: the run of the 16-bit NTT of a polynomial stored with 16 bits

The regions of `fwdW` (`rsW`: the polynomial at `x0`, the working space at
`x1`, the table of zetas), the terms it starts from (`initW`: coefficient `p`
of the input in halfword `p`, the table's halfwords as constants), and the
check, by the kernel, that the run leaves the reduced coefficients of `NTT`
in the polynomial (`checkW`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-- `n` chunks, chunk `j`'s halfword `e` the term `f j e`. -/
def packY (f : Nat → Nat → T) (n : Nat) : Nat :=
  (List.range n).foldr (fun j acc => Y.ofFn (f j) + 2 ^ yw * acc) 0

def rsW : List Rg :=
  [⟨.reg .x0, 0, 32, true⟩, ⟨.reg .x1, 0, 32, true⟩, ⟨.sym "VG_MLKEM_NTT16_ZETAS", 0, 32, false⟩]

/-- The input, coefficient `p` in halfword `p`. -/
def fInW : Nat := packY (fun j e => lvT 0 (8 * j + e)) 32

materialize_value fInW

/-- Nothing followed but the pointers to the polynomial and the working space. -/
def initW : St := ((⟨0, 0, [fInW, 0, tabT]⟩ : St).setG .x0 (.ptr 0 0)).setG .x1 (.ptr 1 0)

/-- The polynomial's halfwords are the reduced coefficients of `NTT`. -/
def outW (σ : St) : Bool :=
  (List.range 32).all fun j => (List.range 8).all fun e => Nat.beq ((σ.chunk 0 j).get e) (outT (8 * j + e))

theorem checkW_ok :
    (initW.runP fwdRules rsW 16 Impl.MlKem.AArch64.Ntt16.Readonly.fwdW).elim false outW = true := by
  lit_decide

theorem initW_f : ∀ j < 32, ∀ e < 8, (initW.chunk 0 j).get e = lvT 0 (8 * j + e) := by decide +kernel

theorem initW_s : ∀ j < 32, ∀ e < 8, (initW.chunk 1 j).get e = 0 := by decide +kernel

/-- Lane `e` of chunk `j` of the table. -/
theorem tabT_get {j e : Nat} (hj : j < 32) (he : e < 8) :
    Y.get (slot yw tabT j) e = cT (Impl.MlKem.AArch64.Ntt16.tableHalves.getD (8 * j + e) 0) := by
  have hl : Impl.MlKem.AArch64.Ntt16.tableHalves.length = 256 := by
    rw [Impl.MlKem.AArch64.Ntt16.tableHalves.lit_eq]; decide +kernel
  show slot tw (slot (tw * 8) tabT j) e = _
  rw [slot_slot _ _ _ _ _ he, tabT, slot_foldr cT (fun h => Nat.lt_trans (mk_lt _ _ _ _ _) (by decide)) _ _ (by omega)]

theorem initW_t {j e : Nat} (hj : j < 32) (he : e < 8) :
    (initW.chunk 2 j).get e = cT (Impl.MlKem.AArch64.Ntt16.tableHalves.getD (8 * j + e) 0) :=
  tabT_get hj he

end VG.Proof.MlKem.AArch64.NttR
