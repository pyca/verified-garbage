module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Contract
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.BrainpoolP512r1.Prime
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Point
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # brainpoolP512r1 signing on x86-64: correctness, memory safety and constant time

The general complete-addition ladder works for any `a`. Field and scalar
inversions use the existing divsteps implementation, instantiated with
kernel-checked primality certificates.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits brainpoolp512r1.C = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h1 : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP512r1.curve.n.log2 < 512 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `64` bytes is dropped. -/
theorem brainpoolp512r1_sh : brainpoolp512r1.sh = 0 := by
  unfold Cfg.sh
  rw [brainpoolp512r1_nBits]
  rfl

theorem brainpoolp512r1_ok (hI : InvSounds) : BaseCfgOk brainpoolp512r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [brainpoolp512r1_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.BrainpoolP512r1.curve.p
    exact Proof.BrainpoolP512r1.p_prime),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ brainpoolp512r1.C.n_ne_zero Proof.BrainpoolP512r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

theorem brainpoolp512r1_tbls : CombTbls brainpoolp512r1 := fun _ h => by cases h

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, by simp [TblsHeld, Cfg.combConsts, brainpoolp512r1, Abi.constsHeld, Abi.constRegions]⟩

/-- `[k]G` is a call of `vg_brainpoolp512r1_mul`, which calls no other function. -/
theorem brainpoolp512r1_mulBase : MulBaseOk brainpoolp512r1 :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨.inr (.inr rfl), by lit_decide⟩⟩

theorem sign_x86 (hL : Law Spec.BrainpoolP512r1.curve)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signBrainpoolP512r1.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (brainpoolp512r1_ok hI) hL brainpoolp512r1_tbls (pre_of hs) brainpoolp512r1_mulBase
  have hok : signBrainpoolP512r1.InlineOk = true := by lit_decide
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : signBrainpoolP512r1.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]; lit_decide
  have F := (Exec.regions he (Code.noCalls_inline hok)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

/-- `signBrainpoolP512r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signBrainpoolP512r1Erased : Prog isa := Code.erase signBrainpoolP512r1

materialize_shared signBrainpoolP512r1Erased

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signBrainpoolP512r1 :=
  VG.Taint.constantTime_mapBlocks (c' := signBrainpoolP512r1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0) rfl (by taint_decide)

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : signX86_64.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig, Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 128) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.BrainpoolP512r1.curve) (hI : InvSounds) (s : State) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (by lit_decide) (sign_x86 hL hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

theorem sign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst X86_64.abi 8).pre s)
    (hp : signX86_64.post s b) : signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 128)
    (by rw [hwr]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

theorem sign_verified (hL : Law Spec.BrainpoolP512r1.curve)
    (hI : InvSounds) :
    Verified X86_64.target signBrainpoolP512r1
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst X86_64.abi 8) :=
  Verified.of_inline_ct (by lit_decide) (sign_x86 hL hI) sign_ct implies8
    (fun _ h => Sig.clear_of_pre h) sign_patch

end VG.Proof.Ecdsa.X86_64.BrainpoolP512r1
