module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Correct
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
public import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery

/-!
# ML-DSA signing on x86-64: verified

`vg_mldsa{44,65,87}_sign` (`sign (primsWith v.code) p`, for an implementation
`v` of the polynomial arithmetic) is verified against `signContract`, whose
`signLeak` says of each rejected iteration which check rejected it, and at
which polynomial: the checks of `z` and `r₀` stop at the first polynomial
that fails.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

/-- A state satisfying `signContract`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x3100 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (signContract p X86_64.abi signStack).pre s) :
    (signK p signStack).Implies (signContract p X86_64.abi signStack) where
  pre := by sig_implies_pre [signContract, signSig, signK, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [signContract, signSig, signK, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContract, signSig, signK, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : Ok3 p) :
    (signK p signStack).Implies (signContract p X86_64.abi signStack) := by
  refine signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa44
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa65
  · sig_implies_sat [signContract, signSig, X86_64.abi, X86_64.argRegs] [signSat] using signSat mlDsa87

/-! ## For any implementation of the polynomial arithmetic

A check that composes over the code (`Comp`) gives the same result on
signing with the polynomial arithmetic `B` as with every function of it
empty, if it holds of `B`'s functions (`sign_same`), so MXCSR (`sign_ctl`)
and the stack pointer (`sign_spSafe`) are checked by evaluating signing
with no implementation of it. -/

theorem sign_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h2 : mc B.invNtt = true) (h3 : mc B.mul = true) (h5 : mc B.add = true)
    (h6 : mc B.sub = true) (h7 : mc B.rej4 = true) (h8 : mc B.expandMask4 = true) (h9 : mc B.highBits = true)
    (h10 : mc B.lowBits = true) (h11 : mc B.normLt = true) (h12 : mc B.makeHint = true)
    (h13 : mc B.dotInv4 = true) (h14 : mc B.dotInv5 = true) (h15 : mc B.dotInv7 = true) (p : Params) :
    Same m (Impl.MlDsa.X86_64.Sign.sign (primsWith B) p) (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) := by
  have hd : mc ((primsWith B).dotInv p.ℓ) = true := by
    unfold Prims.dotInv; split
    · exact h13
    · split
      · exact h14
      · exact h15
  have he : (primsWith Backend.empty).dotInv p.ℓ = .block [] := by
    unfold Prims.dotInv; split
    · rfl
    · split <;> rfl
  unfold Impl.MlDsa.X86_64.Sign.sign
  same_tac hm
  all_goals rw [he]; exact Same.call hm hd _ _

theorem sign0_ctlC {p : Params} (h3 : Ok3 p) : ctlC (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) = true := by
  rcases h3 with rfl | rfl | rfl
  · exact (by lit_decide : ctlC sign44 = true)
  · exact (by lit_decide : ctlC sign65 = true)
  · exact (by lit_decide : ctlC sign87 = true)

theorem sign0_sp {p : Params} (h3 : Ok3 p) :
    (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases h3 with rfl | rfl | rfl
  · exact (by lit_decide : sign44.allInstrs (fun i => !isa.writesSp i) = true)
  · exact (by lit_decide : sign65.allInstrs (fun i => !isa.writesSp i) = true)
  · exact (by lit_decide : sign87.allInstrs (fun i => !isa.writesSp i) = true)

variable (v : ArithImpl) {p : Params} (h3 : Ok3 p)
include h3

theorem sign_ctl : ctlOk (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) = true :=
  ctlOk_of_ctlC (Same.ok (sign_same Comp.ctlC v.ok.ntt.ctl v.ok.invNtt.ctl v.ok.mul.ctl
    v.ok.add.ctl v.ok.sub.ctl v.ok.rej4.ctl v.ok.expandMask4.ctl v.ok.highBits.ctl v.ok.lowBits.ctl
    v.ok.normLt.ctl v.ok.makeHint.ctl (v.ok.dotInv 4 (.inl rfl)).ctl (v.ok.dotInv 5 (.inr (.inl rfl))).ctl
    (v.ok.dotInv 7 (.inr (.inr rfl))).ctl p) (sign0_ctlC h3))

theorem sign_spSafe : (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (sign_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.invNtt.sp) (Code.allInstrs_of_all v.ok.mul.sp)
    (Code.allInstrs_of_all v.ok.add.sp)
    (Code.allInstrs_of_all v.ok.sub.sp) (Code.allInstrs_of_all v.ok.rej4.sp)
    (Code.allInstrs_of_all v.ok.expandMask4.sp)
    (Code.allInstrs_of_all v.ok.highBits.sp) (Code.allInstrs_of_all v.ok.lowBits.sp)
    (Code.allInstrs_of_all v.ok.normLt.sp) (Code.allInstrs_of_all v.ok.makeHint.sp)
    (Code.allInstrs_of_all (v.ok.dotInv 4 (.inl rfl)).sp) (Code.allInstrs_of_all (v.ok.dotInv 5 (.inr (.inl rfl))).sp)
    (Code.allInstrs_of_all (v.ok.dotInv 7 (.inr (.inr rfl))).sp) p) (sign0_sp h3))

theorem sign_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) (signContract p X86_64.abi signStack) :=
  Verified.of_correct (sign_correct (prims_okWith v) h3 (sign_ctl v h3)) (sign_ct (prims_okWith v) h3)
    (signK_implies h3)

theorem sign_verified' :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) (signContract p X86_64.abi signStack) :=
  sign_verified v h3

end VG.Proof.MlDsa.X86_64.Sign
