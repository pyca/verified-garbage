module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Contract
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.P192.OrderPrime
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.P192.Prime
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Contract
meta import VerifiedGarbage.Proof.P192.Point
meta import VerifiedGarbage.Proof.P192.OrderPrime
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.P192.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # p192 signing on x86-64: correctness, memory safety and constant time

The general complete-addition ladder also handles P-192’s `a = -3`. Field and scalar
inversions use the existing divsteps implementation, instantiated with
kernel-checked primality certificates.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P192

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p192_nBits : Spec.Ecdsa.nBits p192.C = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h1 : 191 ≤ Spec.P192.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P192.curve.n.log2 < 192 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `24` bytes is dropped. -/
theorem p192_sh : p192.sh = 0 := by
  unfold Cfg.sh
  rw [p192_nBits]
  rfl

theorem p192_ok (hI : InvSounds) : BaseCfgOk p192 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P192.onCurve_G
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
  sh := by rw [p192_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P192.curve.p
    rw [show Spec.P192.curve.p = 6277101735386680763835789423207666416083908700390324961279 by decide +kernel]
    exact Proof.P192.prime_6277101735386680763835789423207666416083908700390324961279),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p192.C.n_ne_zero Proof.P192.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

theorem p192_tbls : CombTbls p192 := fun _ h => by cases h

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p192 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, by simp [TblsHeld, Cfg.combConsts, p192, Abi.constsHeld, Abi.constRegions]⟩

/-- `[k]G` is a call of `vg_p192_mul`, which calls no other function. -/
theorem p192_mulBase : MulBaseOk p192 :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨.inl rfl, by lit_decide⟩⟩

theorem sign_x86 (hL : Law Spec.P192.curve)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP192.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p192_ok hI) hL p192_tbls (pre_of hs) p192_mulBase
  have hok : signP192.InlineOk = true := by lit_decide
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : signP192.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
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

/-- `signP192` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signP192Erased : Prog isa := Code.erase signP192

materialize_shared signP192Erased

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP192 :=
  VG.Taint.constantTime_mapBlocks (c' := signP192Erased) taintS_eraseInv
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
theorem implies8 : signX86_64.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.Ecdsa.P192.inst, Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig, Spec.P192.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 48) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.P192.curve) (hI : InvSounds) (s : State) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP192 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (by lit_decide) (sign_x86 hL hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

theorem sign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst X86_64.abi 8).pre s)
    (hp : signX86_64.post s b) : signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 48)
    (by rw [hwr]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

theorem sign_verified (hL : Law Spec.P192.curve)
    (hI : InvSounds) :
    Verified X86_64.target signP192
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst X86_64.abi 8) :=
  Verified.of_inline_ct (by lit_decide) (sign_x86 hL hI) sign_ct implies8
    (fun _ h => Sig.clear_of_pre h) sign_patch

end VG.Proof.Ecdsa.X86_64.P192
