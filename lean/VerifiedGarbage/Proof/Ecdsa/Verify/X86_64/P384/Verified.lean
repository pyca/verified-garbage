import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-!
# ECDSA verification over P-384 on x86-64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P384.law`, `Proof.P384.combOk7` and the
variant's `inv`), so `verify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). Constant time by taint tracking with the address of
the comb's static public (`taintSym`): the only branches are on loop
counters, and every address is an argument or the static's address plus a
constant or a counter, so only the pointers affect timing (the contract would
let the key, the hash and the signature affect it too).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384_combConsts, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p384_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem verify_x86 (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP384 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (p384_ok hI) hL (p384_tbls hT) (pre_of hs)
  have hsp : ∀ i ∈ instrs verifyP384, Taint.clobbers i .rsp = false := by
    have h : verifyP384.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

theorem verify_ct : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifyP384 :=
  VG.Taint.constantTime (A := taintSym ["VG_P384_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem verify_verified (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyP384
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)) :=
  Verified.of_correct (verify_x86 hL hT hI) verify_ct implies

end VG.Proof.Ecdsa.Verify.X86_64.P384
