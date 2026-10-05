import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Contract
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.P521.X86_64.TaintSums

/-!
# P-521 public keys on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P521.law`), so `publicKey_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter.
-/

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h8, h9⟩

theorem post_of {s s' : State} (h : PkPost p521 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 133 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 133 = List.replicate 133 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p521.C (dk p521 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_x86 (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP521 s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok p521_ok hL (pre_of hs)
  have hsp : ∀ i ∈ instrs publicKeyP521, Taint.clobbers i .rsp = false := by
    have h : publicKeyP521.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP521 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx]) publicKeyP521 h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.ladderGSum, Proof.P521.X86_64.powPSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ hc
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem pk_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified X86_64.target publicKeyP521 (Spec.EcKey.P521.inst.publicKeyContract X86_64.abi) :=
  Verified.of_correct (pk_x86 hL) pk_ct implies

end VG.Proof.EcKey.X86_64.P521
