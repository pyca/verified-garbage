import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Contract
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-!
# P-224 public keys on x86-64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P224.law`, `Proof.P224.combOk7` and the
variant's `inv`), so `publicKey_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking with
the address of the comb's static public (`taintSym`): the only branches are
on loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

namespace VG.Proof.EcKey.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224_combConsts, show p224.C.len = 28 from rfl]; simp only [Abi.constRegions,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p224_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem post_of {s s' : State} (h : PkPost p224 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 57 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 57 = List.replicate 57 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p224.C (dk p224 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_x86 (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP224 s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p224_ok hI) hL (p224_tbls hT) (pre_of hs)
  have hsp : ∀ i ∈ instrs publicKeyP224, Taint.clobbers i .rsp = false := by
    have h : publicKeyP224.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
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

theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP224 :=
  VG.Taint.constantTime (A := taintSym ["VG_P224_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP224
      (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)) :=
  Verified.of_correct (pk_x86 hL hT hI) pk_ct implies

end VG.Proof.EcKey.X86_64.P224
