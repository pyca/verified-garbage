import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Contract
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.P521.X86_64.TaintSums
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# P-521 public keys on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the registration
file supplies: `Proof.P521.law`, `Proof.P521.combOk7` and the variant's
`inv`), so `publicKey_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking with
the address of the comb's static public (`taintSym`): the only branches are
on loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521_combConsts, p521_constRegions, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p521_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

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

theorem pk_x86 (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP521.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (c := p521) (p521_ok hI).toBaseCfgOk hL (p521_tbls hT) (pre_of hs)
  have hsp : ∀ i ∈ instrs publicKeyP521.inline, Taint.clobbers i .rsp = false := by
    have h : publicKeyP521.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (Code.noCalls_inline (by lit_decide))).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he
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

theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP521 := by
  obtain ⟨_, hc⟩ : ∃ h, ((taintSym ["VG_P521_COMB"]).check
      (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) publicKeyP521 h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.combGSum, Proof.P521.X86_64.invPSum]
  refine VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ hc
  exact fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩

theorem sat_spec8 :
    (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8).pre satState := by
  have held : ∀ i < p521W.length, satState.mem.readW (satState.syms "VG_P521_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0 := satMem_held
  sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    pkX86_64.Implies (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre_consts hs) (p := s.gpr .rdi) (n := 133)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP521
      (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8) :=
  Verified.of_inline_ct (by lit_decide) (pk_x86 hL hT hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) pk_patch

end VG.Proof.EcKey.X86_64.P521
