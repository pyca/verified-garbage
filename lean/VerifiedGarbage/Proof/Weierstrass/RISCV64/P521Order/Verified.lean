module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.RV
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.CT
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.CT

/-!
# Arithmetic modulo P-521's order on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`), from
the functions of any wide modulus (`Proof/Weierstrass/RISCV64/GenWide/RV.lean`),
which the shared contracts of `Proof/Weierstrass/MontContract.lean` imply with
their own working space the top 576 bytes of `ws`, from 7616 to 8192. They are
constant time: the zero-extension is related by its results, after which only
`a0`–`a3` are public, and the taint analysis finds every branch and address
depends on them alone (`GenWide.fn_ct`).
-/

-- Checking the facts of the modulus (`WideOk`) evaluates `2⁵²¹` and `2⁵⁷⁶`.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Order

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Order
open VG.Impl.Weierstrass.Mont (numAt p521n Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Weierstrass.RISCV64.GenWide (WideOk)
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)

theorem wide : WideOk p521n := ⟨by decide, by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p521n).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521n).post s s' :=
  GenWide.mul_rv wide s hs

theorem add_rv (s : State) (hs : (addRV p521n).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p521n).post s s' :=
  GenWide.add_rv wide s hs

theorem sub_rv (s : State) (hs : (subRV p521n).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p521n).post s s' :=
  GenWide.sub_rv wide s hs

/-! ## Constant time -/

open VG.Proof.Ed25519.RISCV64 (mulAgreeLo)

theorem mulFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub mulFn :=
  GenWide.fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem addFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub addFn :=
  GenWide.fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem subFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub subFn :=
  GenWide.fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem rvPub_agree : ∀ s₁ s₂ : State, rvPre p521n s₁ → rvPre p521n s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

end VG.Proof.Weierstrass.RISCV64.P521Order
