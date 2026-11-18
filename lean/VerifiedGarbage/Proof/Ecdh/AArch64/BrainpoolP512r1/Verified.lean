module

import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Main
public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Main
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
meta import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdh.AArch64.BrainpoolP512r1.Contract`, which only this module used -/

section

/-!
# ECDH over brainpoolP512r1 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdh.BrainpoolP512r1.exchangeApi`'s contract for AArch64, by name:
`vg_ecdh_brainpoolp512r1(out = x0, d = x1, peer = x2, scratch = x3)`, the result in
`w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP512r1

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (bytesAt m peer 129)

def ecdhAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let d : Region := ⟨s.gpr .x1, 64⟩
    let peer : Region := ⟨s.gpr .x2, 129⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 64 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 129⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhAArch64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
        simp only [ecdhAArch64, ex, Spec.BrainpoolP512r1.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.AArch64.BrainpoolP512r1

end

end

/-!
# ECDH over brainpoolP512r1 on AArch64: `Verified`

brainpoolp512r1 is a curve the proof supports (`brainpoolp512r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP512r1.law`), so `exchange_ok`
gives the contract's postcondition; `x19` and `x20` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP512r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP512r1

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost brainpoolp512r1 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  dsimp only [ecdhAArch64]
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange brainpoolp512r1.C (dk brainpoolp512r1 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * brainpoolp512r1.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa VG.Impl.Ecdh.AArch64.BrainpoolP512r1.exchange s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (brainpoolp512r1_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_ofK he (by lit_decide) hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub VG.Impl.Ecdh.AArch64.BrainpoolP512r1.exchange :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target VG.Impl.Ecdh.AArch64.BrainpoolP512r1.exchange
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.BrainpoolP512r1
