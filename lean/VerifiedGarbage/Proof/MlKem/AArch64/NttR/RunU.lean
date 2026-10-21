module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on AArch64: the runs of the 16-bit NTT of a polynomial stored with 32 bits

`fwd` and the end of `ntt` (`nttTail`) read and write coefficient `p` as
the word at `4p`, halfwords `2p` (the coefficient) and `2p + 1` (zero). Their
regions (`rsU`, `rsN`: the table in the working space, as `ntt` stores it),
the terms they start from (`initU`), and the checks, by the kernel, that the
runs leave the reduced coefficients of `NTT` in the low halfwords and zero
in the high ones (`checkU_ok`, `checkN_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

def rsU : List Rg :=
  [⟨.reg .x0, 0, 64, true⟩, ⟨.reg .x1, 0, 32, true⟩, ⟨.sym "VG_MLKEM_NTT16_ZETAS", 0, 32, false⟩]

def rsN : List Rg :=
  [⟨.reg .x0, 0, 64, true⟩, ⟨.reg .x1, 0, 32, true⟩, ⟨.reg .x1, 512, 32, false⟩]

/-- The input, coefficient `p` in halfword `2p`. -/
def fInU : Nat := packY (fun j e => if e % 2 = 0 then lvT 0 (4 * j + e / 2) else junkT) 64

materialize_value fInU

def initU : St := ((⟨0, 0, [fInU, 0, tabT]⟩ : St).setG .x0 (.ptr 0 0)).setG .x1 (.ptr 1 0)

/-- The polynomial's words are the reduced coefficients of `NTT`. -/
def outU (σ : St) : Bool :=
  (List.range 64).all fun j => (List.range 8).all fun e =>
    Nat.beq ((σ.chunk 0 j).get e) (if e % 2 = 0 then outT (4 * j + e / 2) else cT 0)

theorem checkU_ok :
    (initU.runP fwdRules rsU 16 Impl.MlKem.AArch64.Ntt16.Readonly.fwd).elim false outU = true := by
  lit_decide

theorem checkN_ok : (initU.runP fwdRules rsN 16 nttTail).elim false outU = true := by
  lit_decide

theorem initU_f : ∀ j < 64, ∀ e < 8,
    (initU.chunk 0 j).get e = if e % 2 = 0 then lvT 0 (4 * j + e / 2) else junkT := by
  decide +kernel

theorem initU_s : ∀ j < 32, ∀ e < 8, (initU.chunk 1 j).get e = 0 := by decide +kernel

theorem initU_t {j e : Nat} (hj : j < 32) (he : e < 8) :
    (initU.chunk 2 j).get e = cT (Impl.MlKem.AArch64.Ntt16.tableHalves.getD (8 * j + e) 0) :=
  tabT_get hj he

end VG.Proof.MlKem.AArch64.NttR
