module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunU
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitI
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunU
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitI
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on AArch64: the runs of the 16-bit inverse NTTs

The regions of `inv` (`rsIU`: the polynomial stored with 32 bits at `x0`, the
working space at `x1`, the table of zetas) and `invW` (`rsIW`: stored with 16
bits), the terms they start from (`initIU`, `initIW`: the input's coefficients,
the table's halfwords as constants), and the checks, by the kernel, that the
runs leave the reduced coefficients of `NTT⁻¹` in the polynomial (`checkIU_ok`,
`checkIW_ok`, and `checkIN_ok` for the end of `nttInv`, with the table in the
working space).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

def rsIU : List Rg := rsUs "VG_MLKEM_INTT16_ZETAS"

def rsIW : List Rg := rsWs "VG_MLKEM_INTT16_ZETAS"

def initIU : St := initUs itabT

def initIW : St := initWs itabT

theorem checkIU_ok :
    (initIU.runP invRules rsIU 16 Impl.MlKem.AArch64.Ntt16.Readonly.inv).elim false outU = true := by
  lit_decide

theorem checkIN_ok : (initIU.runP invRules rsN 16 nttInvTail).elim false outU = true := by
  lit_decide

theorem checkIW_ok :
    (initIW.runP invRules rsIW 16 Impl.MlKem.AArch64.Ntt16.Readonly.invW).elim false outW = true := by
  lit_decide

/-- Lane `e` of chunk `j` of the table. -/
theorem itabT_get {j e : Nat} (hj : j < 32) (he : e < 8) :
    Y.get (slot yw itabT j) e = cT (Impl.MlKem.AArch64.Ntt16.invTableHalves.getD (8 * j + e) 0) := by
  have hl : Impl.MlKem.AArch64.Ntt16.invTableHalves.length = 256 := by
    rw [Impl.MlKem.AArch64.Ntt16.invTableHalves.lit_eq]; decide +kernel
  show slot tw (slot (tw * 8) itabT j) e = _
  rw [slot_slot _ _ _ _ _ he, itabT, slot_foldr cT (fun h => Nat.lt_trans (mk_lt _ _ _ _ _) (by decide)) _ _ (by omega)]

end VG.Proof.MlKem.AArch64.NttR
