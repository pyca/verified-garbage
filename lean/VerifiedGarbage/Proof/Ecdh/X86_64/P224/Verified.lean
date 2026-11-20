module

import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ecdh.X86_64.P224.Lit
public import VerifiedGarbage.Impl.Ecdh.P224.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P224.Lit
meta import VerifiedGarbage.Impl.Ecdh.P224.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdh.X86_64.P224.Contract`, which only this module used -/

section

/-!
# ECDH over P-224 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdh.P224.exchangeApi`'s contract for x86-64, by name:
`vg_ecdh_p224(out = rdi, d = rsi, peer = rdx, scratch = rcx)`, the result
in `eax`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P224

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P224.curve (ofBytes (bytesAt m d 28)) (bytesAt m peer 57)

def ecdhX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 28⟩
    let d : Region := ⟨s.gpr .rsi, 28⟩
    let peer : Region := ⟨s.gpr .rdx, 57⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 28 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 28 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 28 = List.replicate 28 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 28⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x1000, 28⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhX86_64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86_64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
        simp only [ecdhX86_64, ex, Spec.P224.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.X86_64.P224

end

end

/-!
# ECDH over P-224 on x86-64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law
and `InvSounds` for its inversions, which the registration file supplies:
`Proof.P224.law` and the variant's `inv`), so `exchange_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p224 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of {s s' : State} (h : EPost p224 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  dsimp only [ecdhX86_64]
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p224.C (dk p224 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p224.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_inlineOk : exchangeP224.InlineOk = true := by lit_decide

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP224.inline s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (p224_ok hI) hL (pre_of hs)
  have hsp := Code.clobbers_rsp_of_inlineOk ecdh_inlineOk
  have F := (Exec.regions he (Code.noCalls_inline ecdh_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
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

/-- `exchangeP224` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def exchangeP224Erased : Prog isa := Code.erase exchangeP224

materialize_shared exchangeP224Erased

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP224 := by
  refine VG.Taint.constantTime_mapBlocks (c' := exchangeP224Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h0

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    ecdhX86_64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
      Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem ecdh_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86_64.abi 8).pre s)
    (hp : ecdhX86_64.post s b) : ecdhX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 28)
    (by rw [hwr]; simp) (by decide)
  simpa only [ecdhX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem ecdh_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target exchangeP224 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86_64.abi 8) :=
  Verified.of_inline_ct ecdh_inlineOk (ecdh_x86 hL hI) ecdh_ct implies8
    (fun _ h => Sig.clear_of_pre h) ecdh_patch

/-! ## Without secret residue -/

theorem exchange_codeSp : exchangeP224.all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_ecdh_p224` as emitted (`Impl.Ecdh.X86_64.Fn.exchangeP224`), its cleanup included,
meets its contract in constant time and returns without secret residue. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.X86_64.InvSounds) :
    VerifiedScrubbed X86_64.target Impl.Ecdh.X86_64.Fn.exchangeP224 (Spec.Ecdh.P224.exchangeApi.contract X86_64.abi 8) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ecdh.P224.exchangeApi)
    { code := exchangeP224
      stack := 8
      verified := ecdh_verified hL hI
      spSafe := exchange_codeSp } .sse (VG.Proof.EcKey.X86_64.Scrub.exchangeOut _ _)

theorem exchange_spSafe :
    Impl.Ecdh.X86_64.Fn.exchangeP224.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe exchange_codeSp

end VG.Proof.Ecdh.X86_64.P224
