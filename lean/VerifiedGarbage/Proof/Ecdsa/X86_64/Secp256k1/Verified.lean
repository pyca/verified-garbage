import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Secp256k1.Prime
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-! # secp256k1 signing on x86-64: correctness, memory safety and constant time

The general complete-addition ladder works with `a = 0`. Field and scalar
inversions use the existing divsteps implementation, instantiated with
kernel-checked primality certificates.
-/

namespace VG.Proof.Ecdsa.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem secp256k1_nBits : Spec.Ecdsa.nBits secp256k1.C = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h1 : 255 ≤ Spec.Secp256k1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.Secp256k1.curve.n.log2 < 256 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `32` bytes is dropped. -/
theorem secp256k1_sh : secp256k1.sh = 0 := by
  unfold Cfg.sh
  rw [secp256k1_nBits]
  rfl

theorem secp256k1_ok (hI : InvSounds) : BaseCfgOk secp256k1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.Secp256k1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [secp256k1_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.Secp256k1.curve.p
    rw [show Spec.Secp256k1.curve.p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 by decide +kernel]
    exact Proof.Secp256k1.prime_115792089237316195423570985008687907853269984665640564039457584007908834671663),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ secp256k1.C.n_ne_zero Proof.Secp256k1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even _ := by decide

theorem secp256k1_tbls : CombTbls secp256k1 := fun _ h => by cases h

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, by simp [TblsHeld, Cfg.combConsts, secp256k1, Abi.constsHeld, Abi.constRegions]⟩

theorem sign_x86 (hL : Law Spec.Secp256k1.curve)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signSecp256k1 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (secp256k1_ok hI) hL secp256k1_tbls (pre_of hs)
  have hsp : ∀ i ∈ instrs signSecp256k1, Taint.clobbers i .rsp = false := by
    have h : signSecp256k1.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

/-- `signSecp256k1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signSecp256k1Erased : Prog isa := Code.erase signSecp256k1

materialize_shared signSecp256k1Erased

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signSecp256k1 :=
  VG.Taint.constantTime_mapBlocks (c' := signSecp256k1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) rfl
    (fun _ _ _ _ ⟨_, h1, h2, h3, h4, h5⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5) rfl (by taint_decide)

theorem sign_verified (hL : Law Spec.Secp256k1.curve)
    (hI : InvSounds) :
    Verified X86_64.target signSecp256k1
      (Spec.Ecdsa.Secp256k1.inst.signContract X86_64.abi) :=
  Verified.of_correct (sign_x86 hL hI) sign_ct implies

end VG.Proof.Ecdsa.X86_64.Secp256k1
