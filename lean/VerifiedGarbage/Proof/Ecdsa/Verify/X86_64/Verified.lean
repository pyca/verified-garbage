module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.VerifyErased
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Batteries.Data.List.Lemmas
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Batteries.Data.List.Lemmas
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.WinLay

/-!
# ECDSA verification over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P256.law`, `Proof.P256.combOk7` and the
variant's `inv`), so `verify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). Direct table lookup uses the scalar determined by
the public digest and signature. `verify_public_ct` relates those lookups,
and taint tracking checks the remaining code against the shared contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256_combConsts, show p256.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p256_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

/-- The verification `code` of a curve `c` (P-256, with either multiplication)
that the proof supports, whose precondition the contract's gives (`hpre`),
never writing `rsp`, or loading MXCSR, its calls inlined (which its literal decides). -/
theorem verify_x86_of {c : Cfg} {code : Prog isa} (hc : CfgOk c) (hL : Weierstrass.Law c.C) (hT : CombTbls c)
    (hmn : c.mul = none)
    (hpre : ∀ s, verifyX86_64.pre s → VPre c s) (hpost : ∀ s s', VPost c s s' → verifyX86_64.post s s')
    (hcode : Impl.Ecdsa.Verify.X86_64.Cfg.verify c = code)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.InlineOk = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa code.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := verify_ok hc hL hT (hpre s hs) fun h => absurd h (by rw [hmn]; decide)
  have hsp : ∀ i ∈ instrs (Impl.Ecdsa.Verify.X86_64.Cfg.verify c).inline, Taint.clobbers i .rsp = false := by
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he (Code.noCalls_inline hnc)).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he ⟨fun r hr => ?_, ?_⟩, hpost _ _ hpost'⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      exact hrs) (by decide)

theorem verify_x86 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP256.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_x86_of (p256_ok hI) hL (p256_tbls hL hT) rfl (fun _ => pre_of) (fun _ _ => id) rfl verifyP256_noRsp
    verifyP256_inlineOk verifyP256_noMxcsr s hs

theorem verify_checks : VerifyChecks p256 p256Table where
  comb := {
    init := VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)
    head := VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
    tail := VG.Taint.constantTime_mapBlocks (c' := tailErased) taint_eraseInv
      (Taint.ofRegs [.rdi,.rbx,.rdx]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide) }
  before := VG.Taint.constantTime_mapBlocks (c' := beforeErased) taint_eraseInv
    (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide)
  after := VG.Taint.constantTime_mapBlocks (c' := afterErased) taint_eraseInv
    (Taint.ofRegs [.rdi]) rfl (fun _ _ _ _ h => h) rfl (by taint_decide)

/-- The shared contract declares all verification input buffers public. -/
theorem verify_public_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub s₁ s₂) :
    VerifyPublic p256 p256Table s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨Taint.agree_ofRegs ?_,hsy,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have digest := (List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])).2
    exact publicU_congr digest parts.2

theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub verifyP256.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact verify_public_ct (p256_ok hI) hL (p256_tbls hL hT) rfl (by decide) verify_checks rfl
    _ _ _ _ _ _ (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (verify_public_of_spec pub) e₁ e₂


/-- The shared contract, but with `verifyX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyK₀ : Contract isa :=
  { pre := (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
    post := verifyX86_64.post
    pub := (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub }

theorem sat_spec8 :
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8).pre satState := by
  have held : ∀ i < p256W.length, satState.mem.readW (satState.syms "VG_P256_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
    Abi.withConsts, p256_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    verifyK₀.Implies (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => implies.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satState, sat_spec8⟩⟩

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) verifyP256_inlineOk (fun s hs => verify_x86 hL hT hI s (implies.pre _ hs))
    (verify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end VG.Proof.Ecdsa.Verify.X86_64
