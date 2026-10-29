module

public import VerifiedGarbage.Proof.EcKey.X86_64.Main
public import VerifiedGarbage.Proof.EcKey.X86_64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
public import VerifiedGarbage.Impl.EcKey.P224.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.EcKey.X86_64.P224.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
meta import VerifiedGarbage.Impl.EcKey.P224.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

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

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224_combConsts, show p224.C.len = 28 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p224_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
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

/-- `publicKeyP224` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def publicKeyP224Erased : Prog isa := Code.erase publicKeyP224

materialize_shared publicKeyP224Erased

theorem pk_inlineOk : publicKeyP224.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyP224Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP224.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p224_ok hI) hL (p224_tbls hT) (pre_of hs) p224_mulBase
  have hsp : ∀ i ∈ instrs publicKeyP224.inline, Taint.clobbers i .rsp = false := by
    have h : publicKeyP224.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
      rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [Taint.clobbers_erase]]
      show publicKeyP224Erased.allInstrs _ = true
      lit_decide
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyP224Erased.allInstrs _ = true
    lit_decide) he
    ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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
  VG.Taint.constantTime_mapBlocks (c' := publicKeyP224Erased) (taintSym_eraseInv ["VG_P224_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem sat_spec8 :
    (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8).pre satState := by
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p224_combConsts, Abi.withConsts, p224_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    pkX86_64.Implies (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre_consts hs) (p := s.gpr .rdi) (n := 57)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP224
      (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hT hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) pk_patch

end VG.Proof.EcKey.X86_64.P224
