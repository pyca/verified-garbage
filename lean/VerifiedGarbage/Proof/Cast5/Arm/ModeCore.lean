module

public import VerifiedGarbage.Proof.Cast5.ModeCipher
public import VerifiedGarbage.Proof.Modes.Arm.Core
public import VerifiedGarbage.Impl.Cast5.Arm.Modes
import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Cast5.Arm.Lit
public import VerifiedGarbage.Proof.Cast5.ModeScratch

/-!
# CAST5's ECB functions as the ARMv7 modes' core

`ecbSpec up`: `vg_cast5_ecb_encrypt` (`up`) or `vg_cast5_ecb_decrypt`, which
take their working space as a stack argument, meet what the modes need of a
core (`Proof.Modes.Arm.CoreSpec`) from their shared contract, with the
cipher `Proof.Cast5.dirCipher up` under the subkeys at `r0` and the number
of rounds in `r1`. They use no stack of their own: the 8 bytes of the push
of their stack argument. They read the table `VG_CAST5_S1234` (`consts`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Proof.Modes (blocksOf)
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

/-- The direction of `up`. -/
def upDir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

theorem ecb_verified (up : Bool) :
    Verified target (ecb up) (Spec.Cast5.ecbContract (Arm.abi.withConsts ecbConsts) (upDir up)) := by
  cases up
  · exact ecbDecrypt_verified
  · exact ecbEncrypt_verified

theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksOf 8 m p n = (Spec.Cast5.blocksAt m p n).map Vector.toList := by
  simp only [VG.Proof.Modes.blocksOf, Spec.Cast5.blocksAt, List.map_map]
  exact List.map_congr_left fun i _ => Proof.Cast5.bytesAt_eq _ _

theorem dirCipher_toList (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (v : Spec.Cast5.Block) :
    Proof.Cast5.dirCipher up k n v.toList =
      ((match upDir up with
        | .encrypt => Spec.Cast5.encryptBlock k n | .decrypt => Spec.Cast5.decryptBlock k n) v).toList := by
  have e : (Vector.ofFn fun i : Fin 8 => v.toList.getD i.val 0) = v := by ext i hi; simp
  cases up <;> simp only [Proof.Cast5.dirCipher, upDir, Spec.Cast5.cipher, Spec.Cast5.invCipher, e,
    Bool.false_eq_true, ↓reduceIte]

theorem ecb_stack (up : Bool) : VG.Arm.FrameStack.armStack (ecbCore up).code + 8 ≤ 8 := by
  cases up <;> decide +kernel

theorem dReg_eq (up : Bool) : (ecbCore up).dReg = .r2 := rfl
theorem nReg_eq (up : Bool) : (ecbCore up).nReg = .r3 := rfl

/-- CAST5's ECB function of `up`, as the modes' core. -/
def ecbSpec (up : Bool) : CoreSpec (ecbCore up) where
  keyLen := 128
  stack := 8
  rok R := R.toNat = 12 ∨ R.toNat = 16
  consts := ecbConsts
  ciphAt m K R := Proof.Cast5.dirCipher up (Spec.Cast5.scheduleAt m K) R.toNat
  contract := Spec.Cast5.ecbContract (Arm.abi.withConsts ecbConsts) (upDir up)
  correct := (ecb_verified up).1
  ct := (ecb_verified up).2.1
  depth := by have := ecb_stack up; omega
  pre_of h := absurd h (by cases up <;> decide)
  post_of h := absurd h (by cases up <;> decide)
  pub_of h := absurd h (by cases up <;> decide)
  ciphAt_congr h := congrArg (Proof.Cast5.dirCipher up · _) (Proof.Cast5.scheduleAt_congr h)
  ciphAt_R h := by simp [ecbCore] at h
  cipher_len _ _ _ b _ := Proof.Cast5.dirCipher_length up _ _ b
  bw_pos := by cases up <;> decide
  bw_le := by cases up <;> decide
  bs_enc := by cases up <;> decide
  consts_plain h := absurd h (by cases up <;> decide)
  pre_ofS _ s h := by
    obtain ⟨_, spF, rd, wr, kd, ks, ds, da, sa, -, -, -, -, fK, fD, fS, rr, held, tabs⟩ := h
    have rr := rr rfl
    have hl : s.rd.length = 3 := by rw [rd]; rfl
    refine pre_consts.mpr ⟨?_, ?_, held, fun t ht => ⟨(tabs t ht).1, (tabs t ht).2.1, fun r hr => ?_⟩⟩
    · have rd' : (stripConsts ecbConsts s).rd = [⟨State.addr (s.gpr .r0), 128⟩, ⟨stackArgAddr s 0, 4⟩] := by
        simp only [stripConsts, State.withRegions_rd, hl]; rw [rd]; rfl
      sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val]
      exact ⟨spF, rd', wr, kd, ks, ds, da, sa, fK, fD, fS, rr⟩
    · rw [hl, rd]; rfl
    · exact absurd hr (by simp [Arm.abi, stackBelow])
  post_ofS _ s s' hp h := by
    have rr := hp.rr rfl
    have h := post_consts.mp h
    sig_post [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPost, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    show blocksOf 8 _ _ _ = (blocksOf 8 _ _ _).map _
    rw [dReg_eq, nReg_eq]
    simp only [State.addr]
    rw [blocksOf_eq, blocksOf_eq, h, Spec.Cast5.ecb.eq_def, List.map_map, List.map_map]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp, dirCipher_toList]
    rfl
  pub_ofS _ s₁ s₂ h0 h1 h2 h3 h4 h5 h6 := by
    refine pub_consts.mpr ⟨?_, fun x hx => symAddr_eq_iff.mpr (h6 x hx)⟩
    sig_pub [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h0, h1, h2, h3, h4 rfl, h5⟩
  depthS _ := ecb_stack up
  cs_enc _ := by cases up <;> decide

end VG.Proof.Cast5.Arm
