module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP320r1.Lit
public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `EcKey.X86_64.BrainpoolP320r1.Contract`, which only this module used -/

section

/-!
# brainpoolP320r1 public keys on x86-64: the contract the proof is written against

The facts of `Spec.EcKey.BrainpoolP320r1.inst.publicKeyContract` for x86-64, by name:
`vg_ec_brainpoolp320r1_public_key(out = rdi, d = rsi, scratch = rdx)`, the result in
`eax`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.BrainpoolP320r1

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.BrainpoolP320r1.curve) :=
  publicKey Spec.BrainpoolP320r1.curve (ofBytes (bytesAt m d 40))

def pkX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 81⟩
    let d : Region := ⟨s.gpr .rsi, 40⟩
    let scratch : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 81 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 81 = encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 81 = List.replicate 81 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 40⟩]
  wr := [⟨0x1000, 81⟩, ⟨0x8000, 8192⟩]

theorem implies : pkX86_64.Implies (Spec.EcKey.BrainpoolP320r1.inst.publicKeyContract X86_64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
        simp only [pkX86_64, pk, Spec.BrainpoolP320r1.curve] at h
        revert h
        generalize publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, satState] [satState] using satState }

end VG.Proof.EcKey.X86_64.BrainpoolP320r1

end

end

/-!
# brainpoolP320r1 public keys on x86-64: `Verified`

brainpoolp320r1 is a curve the proof supports (`brainpoolp320r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP320r1.law`), so `publicKey_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.BrainpoolP320r1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP320r1

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre brainpoolp320r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h8, h9, by simp [TblsHeld, Cfg.combConsts, brainpoolp320r1, Abi.constsHeld, Abi.constRegions]⟩

theorem post_of {s s' : State} (h : PkPost brainpoolp320r1 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  dsimp only [pkX86_64]
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey brainpoolp320r1.C (dk brainpoolp320r1 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeyBrainpoolP320r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def publicKeyBrainpoolP320r1Erased : Prog isa := Code.erase publicKeyBrainpoolP320r1

materialize_shared publicKeyBrainpoolP320r1Erased

theorem pk_inlineOk : publicKeyBrainpoolP320r1.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyBrainpoolP320r1Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyBrainpoolP320r1.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (brainpoolp320r1_ok hI) hL brainpoolp320r1_tbls (pre_of hs) brainpoolp320r1_mulBase
  have hsp : ∀ i ∈ instrs publicKeyBrainpoolP320r1.inline, Taint.clobbers i .rsp = false := by
    have h : publicKeyBrainpoolP320r1.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
      rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [Taint.clobbers_erase]]
      show publicKeyBrainpoolP320r1Erased.allInstrs _ = true
      lit_decide
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyBrainpoolP320r1Erased.allInstrs _ = true
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


theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyBrainpoolP320r1 := by
  refine VG.Taint.constantTime_mapBlocks (c' := publicKeyBrainpoolP320r1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h0

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : pkX86_64.Implies (Spec.EcKey.BrainpoolP320r1.inst.publicKeyContract X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.BrainpoolP320r1.inst.publicKeyContract X86_64.abi 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 81)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyBrainpoolP320r1 (Spec.EcKey.BrainpoolP320r1.inst.publicKeyContract X86_64.abi 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre h) pk_patch

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_brainpoolp320r1_public_key` must wipe on
return, from the residue analysis (`X86_64.RScrub.keepFor`). -/
def scrubKs : List Nat := keep_for% Spec.EcKey.BrainpoolP320r1.publicKeyApi.sig 8 publicKeyBrainpoolP320r1 []

theorem scrubOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.EcKey.BrainpoolP320r1.publicKeyApi.sig 8 []) publicKeyBrainpoolP320r1 h).any
      (RScrub.resOkB · 8 scrubKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_brainpoolp320r1_public_key`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.RScrub.withScrub`): it returns without secret residue. -/
def scrubReg (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Registration Spec.EcKey.BrainpoolP320r1.publicKeyApi X86_64.target :=
  RScrub.scrubOf {
    code := publicKeyBrainpoolP320r1
    stack := 8
    verified := pk_verified hL hI } .sse true [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
    (EcKey.X86_64.Scrub.publicKeyOut _ _) [] (RScrub.pubOk_nil _) ⟨scrubKs, scrubOk⟩
    (by dsimp only [VG.X86_64.Scrub.retBitsOf]; lit_decide)

end VG.Proof.EcKey.X86_64.BrainpoolP320r1
