import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.EcKey.X86_64.Contract
import VerifiedGarbage.Proof.EcKey.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym

/-!
# P-256 public keys on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P256.law`, `Proof.P256.combOk7` and the
variant's `inv`), so `publicKey_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking with
the address of the comb's static public (`taintSym`): the only branches are
on loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256_combConsts, show p256.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p256_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- The postcondition, for any configuration of P-256 (either multiplication). -/
theorem post_of {c : Cfg} (hC : c.C = Spec.P256.curve) {s s' : State} (h : PkPost c s s') :
    pkX86_64.post s s' := by
  obtain ⟨n, C, comb, fastN, adx, avx2, pubVerify, nbits⟩ := c
  subst hC
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey Spec.P256.curve (dk ⟨n, Spec.P256.curve, comb, fastN, adx, avx2, pubVerify, nbits⟩ s) =
    pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- The public key `code` of a curve `c` (P-256, with either multiplication)
that the proof supports, whose precondition the contract's gives (`hpre`),
never writing `rsp`, calling or loading MXCSR (which its literal decides). -/
theorem pk_x86_of {c : Cfg} {code : Prog isa} (hc : CfgOk c) (hL : Weierstrass.Law c.C) (hT : CombTbls c)
    (hpre : ∀ s, pkX86_64.pre s → PkPre c s) (hpost : ∀ s s', PkPost c s s' → pkX86_64.post s s')
    (hcode : Impl.EcKey.X86_64.Cfg.publicKey c = code)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.noCalls = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := publicKey_ok hc hL hT (hpre s hs)
  have hsp : ∀ i ∈ instrs (Impl.EcKey.X86_64.Cfg.publicKey c), Taint.clobbers i .rsp = false := by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, hpost _ _ hpost'⟩
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

theorem pk_x86 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP256 s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' :=
  pk_x86_of (p256_ok hI) hL (p256_tbls hL hT) (fun _ => pre_of) (fun _ _ => post_of rfl) rfl (by lit_decide)
    (by lit_decide) (by lit_decide) s hs

theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP256 :=
  VG.Taint.constantTime (A := taintSym ["VG_P256_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx])
    (fun _ _ _ _ ⟨_, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

theorem pk_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP256
      (Spec.EcKey.P256.inst.publicKeyContract (X86_64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (pk_x86 hL hT hI) pk_ct implies

end VG.Proof.EcKey.X86_64
