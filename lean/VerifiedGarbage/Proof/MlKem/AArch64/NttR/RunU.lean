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

/-- The polynomial at `x0`, the working space at `x1`, the table at `sym`. -/
def rsUs (sym : String) : List Rg := [⟨.reg .x0, 0, 64, true⟩, ⟨.reg .x1, 0, 32, true⟩, ⟨.sym sym, 0, 32, false⟩]

def rsU : List Rg := rsUs "VG_MLKEM_NTT16_ZETAS"

def rsN : List Rg :=
  [⟨.reg .x0, 0, 64, true⟩, ⟨.reg .x1, 0, 32, true⟩, ⟨.reg .x1, 512, 32, false⟩]

/-- The input, coefficient `p` in halfword `2p`. -/
def fInU : Nat := packY (fun j e => if e % 2 = 0 then lvT 0 (4 * j + e / 2) else junkT) 64

materialize_value fInU

/-- Nothing followed but the input, the table `tab` and the pointers to the polynomial and the
working space. -/
def initUs (tab : Nat) : St := ((⟨0, 0, [fInU, 0, tab]⟩ : St).setG .x0 (.ptr 0 0)).setG .x1 (.ptr 1 0)

def initU : St := initUs tabT

/-- The polynomial's words are the reduced coefficients of `NTT`. -/
def outU (σ : St) : Bool :=
  (List.range 64).all fun j => (List.range 8).all fun e =>
    Nat.beq ((σ.chunk 0 j).get e) (if e % 2 = 0 then outT (4 * j + e / 2) else cT 0)

theorem checkU_ok :
    (initU.runP fwdRules rsU 16 Impl.MlKem.AArch64.Ntt16.Readonly.fwd).elim false outU = true := by
  lit_decide

theorem checkN_ok : (initU.runP fwdRules rsN 16 nttTail).elim false outU = true := by
  lit_decide

theorem fInU_get : ∀ j < 64, ∀ e < 8,
    Y.get (slot yw fInU j) e = if e % 2 = 0 then lvT 0 (4 * j + e / 2) else junkT := by
  decide +kernel

end VG.Proof.MlKem.AArch64.NttR
