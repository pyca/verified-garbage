module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombGeneral
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Contract
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.BrainpoolP384r1.Prime
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Contract
meta import VerifiedGarbage.Proof.BrainpoolP384r1.Point
meta import VerifiedGarbage.Proof.BrainpoolP384r1.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # brainpoolP384r1 signing on x86-64: correctness, memory safety and constant time

The general complete-addition ladder works for any `a`. Field and scalar
inversions use the existing divsteps implementation, instantiated with
kernel-checked primality certificates.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP384r1

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits brainpoolp384r1.C = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h1 : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP384r1.curve.n.log2 < 384 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem brainpoolp384r1_sh : brainpoolp384r1.sh = 0 := by
  unfold Cfg.sh
  rw [brainpoolp384r1_nBits]
  rfl

theorem brainpoolp384r1_ok (hI : InvSounds) : BaseCfgOk brainpoolp384r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP384r1.onCurve_G
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
  sh := by rw [brainpoolp384r1_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.BrainpoolP384r1.curve.p
    exact Proof.BrainpoolP384r1.p_prime),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ brainpoolp384r1.C.n_ne_zero Proof.BrainpoolP384r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

theorem brainpoolp384r1_tbls : CombTbls brainpoolp384r1 := fun _ h => by cases h

/-- ECDH's, verification's and the public key's `[k]G` is a call of
`vg_brainpoolp384r1_mul`, which calls no other function. -/
theorem brainpoolp384r1_mulBase : MulBaseOk brainpoolp384r1 :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨.inr (.inl rfl), by lit_decide⟩⟩

theorem brainpoolp384r1S_sh : brainpoolp384r1S.sh = 0 := brainpoolp384r1_sh

/-- `brainpoolp384r1_ok` for the signature's configuration, which only declares
the comb's tables. -/
theorem brainpoolp384r1S_ok (hI : InvSounds) : BaseCfgOk brainpoolp384r1S where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP384r1.onCurve_G
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
  sh := by rw [brainpoolp384r1S_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.BrainpoolP384r1.curve.p
    exact Proof.BrainpoolP384r1.p_prime),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ brainpoolp384r1S.C.n_ne_zero Proof.BrainpoolP384r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

/-- The comb's digits of 7 bits, 55 of them, cover the scalar's 384 bits. -/
theorem brainpoolp384r1S_comb : CombOk brainpoolp384r1S brainpoolp384r1Comb :=
  ⟨by decide, by decide, by decide⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre brainpoolp384r1S s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, held, fun r hr => ⟨(fit r hr).1, fun w hw => ?_⟩⟩
  rw [h2] at hw
  exact (fit r hr).2 w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h])

theorem sign_x86 (hL : Law Spec.BrainpoolP384r1.curve)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signBrainpoolP384r1.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signG_ok (brainpoolp384r1S_ok hI) hL brainpoolp384r1S_comb
    (Proof.BrainpoolP384r1.combOk7 hL) rfl (pre_of hs)
  obtain ⟨hsp, hmx⟩ := rsp_mxcsr (c := signBrainpoolP384r1) (by lit_decide)
  have F := (Exec.regions he (Code.noCalls_inline (by lit_decide))).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
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

/-- `signBrainpoolP384r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signBrainpoolP384r1Erased : Prog isa := Code.erase signBrainpoolP384r1

materialize_shared signBrainpoolP384r1Erased

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signBrainpoolP384r1 :=
  VG.Taint.constantTime_mapBlocks (c' := signBrainpoolP384r1Erased)
    (taintSym_eraseInv ["VG_BRAINPOOLP384R1_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn
        exact hsy _ (gtab_mem_consts (c := brainpoolp384r1S) rfl)⟩)
    rfl (by taint_decide)

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 96) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.BrainpoolP384r1.curve) (hI : InvSounds) (s : State) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signBrainpoolP384r1 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (by lit_decide) (sign_x86 hL hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

end VG.Proof.Ecdsa.X86_64.BrainpoolP384r1
