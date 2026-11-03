module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Mersenne
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.CT
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.CT

/-!
# Arithmetic modulo P-521's prime on RISC-V: verified

Each function meets a contract by register (`mulRV`, `addRV`, `subRV`), from
the functions of any wide modulus (`Proof/Weierstrass/RISCV64/GenWide/RV.lean`)
and, for the product, its Mersenne form (`Proof/Weierstrass/RISCV64/P521Mersenne.lean`),
which the shared contracts of `Proof/Weierstrass/MontContract.lean` imply with
their own working space the top 576 bytes of `ws`, from 7616 to 8192. They are
constant time: the zero-extension is related by its results, after which only
`a0`–`a3` are public, and the taint analysis finds every branch and address
depends on them alone (`GenWide.fn_ct`).
-/

-- Checking the facts of the modulus (`WideOk`) evaluates `2⁵²¹` and `2⁵⁷⁶`.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P521Field

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Field
open VG.Impl.Weierstrass.Mont (numAt p521p Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)
open VG.Proof.Weierstrass.RISCV64.GenWide (WideOk)
open VG.Impl.Weierstrass.RISCV64.GenWide (wordOf negInv)

theorem wide : WideOk p521p := ⟨by decide, by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p521p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' :=
  P521Mersenne.mul_rv s hs

theorem add_rv (s : State) (hs : (addRV p521p).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p521p).post s s' :=
  GenWide.add_rv wide s hs

theorem sub_rv (s : State) (hs : (subRV p521p).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p521p).post s s' :=
  GenWide.sub_rv wide s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p521p)).pre s) :
    ∃ t s', Exec isa mulFnA s t s' ∧ abiPreserved s s' ∧ (mulRV p521p).post s s' :=
  P521Mersenne.mulA_rv s hs

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p521p)).pre s) :
    ∃ t s', Exec isa addFnA s t s' ∧ abiPreserved s s' ∧ (addRV p521p).post s s' :=
  GenWide.addA_rv wide s hs

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p521p)).pre s) :
    ∃ t s', Exec isa subFnA s t s' ∧ abiPreserved s s' ∧ (subRV p521p).post s s' :=
  GenWide.subA_rv wide s hs

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

theorem rvPub_agree : ∀ s₁ s₂ : State, rvPre p521p s₁ → rvPre p521p s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

/-! ## The shared contracts -/

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

/-- A state satisfying the preconditions: `ws` at `0x1000`, every offset 0, memory zero. -/
def satWs : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_pre : rvPre p521p satWs ∧ arg p521p satWs .a2 = 0 ∧ arg p521p satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn, Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownBytes,
      satWs, offArg, p521p]

theorem mul_verified :
    Verified RISCV64.target mulFn (p521p.mulContract RISCV64.abi (own := 7616) (ownEnd := 8192)) :=
  Verified.of_correct mul_rv (mulFn_ct (Pre := (mulRV p521p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem add_verified :
    Verified RISCV64.target addFn (p521p.addContract RISCV64.abi (own := 7616) (ownEnd := 8192)) :=
  Verified.of_correct add_rv (addFn_ct (Pre := (addRV p521p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem sub_verified :
    Verified RISCV64.target subFn (p521p.subContract RISCV64.abi (own := 7616) (ownEnd := 8192)) :=
  Verified.of_correct sub_rv (subFn_ct (Pre := (subRV p521p).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs,
        VG.Proof.Weierstrass.RISCV64.rvOwn, VG.Proof.Weierstrass.RISCV64.rvOwnEnd]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

end VG.Proof.Weierstrass.RISCV64.P521Field
