module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopBody
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopCTMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ScrubSign
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: verification, verified and without secret residue

`verify` meets `verifyContract` in constant time (`verify_verified`, from
`verify_correct`, `verify_ct` and `vg_implies`). As emitted
(`Impl.SlhDsa.AArch64.Fn.verify`), over any implementation `T` of `thash4`:
its code with every register the calling convention does not preserve
cleared and the 16 bytes below its stack pointer zeroed (`scrubAll 16 32
Clear.all`). What the cleanup needs of the code is evaluated by the kernel
once for each parameter set and each single-state Keccak, of the code with
`thash4`'s calls holes (`KeyGen.stubOf`), whatever the names of the
functions (`verify_fill`), and `T` gives it of its own code
(`Thash4Impl.side`). Then the six parameter sets, as their registrations
name them.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64 VG.AArch64.Scrub
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.SlhDsa.AArch64.KeyGen (Shake6 fnsOf stubOf)
open VG.Proof.SlhDsa.AArch64.Sign (fnsOf')

/-! ## `Verified` -/

theorem vg_implies {p : Params} (hz : Sz p) : (vgK p).Implies (verifyContract p AArch64.abi 16) := by
  refine ⟨fun s h => ?_, fun s s' _ h => ?_, fun s₁ s₂ _ _ h => ?_, ⟨verifySat p, verifySat_pre hz⟩⟩
  · sig_pre [Spec.SlhDsa.verifyContract, Spec.SlhDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at h
    sig_split h
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, h⟩
  · sig_post [Spec.SlhDsa.verifyContract, Spec.SlhDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
    exact h
  · have hv := vpub_of h
    have g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := hv.regs
    refine ⟨g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide),
      g _ (by decide), g _ (by decide), hv.sp, ?_, ?_, ?_, ?_⟩
    · show bytesAt _ _ _ = bytesAt _ _ _
      rw [hv.pk, g .x0 (by decide)]
    · show bytesAt _ _ _ = bytesAt _ _ _
      rw [hv.msg, g .x1 (by decide), g .x2 (by decide)]
    · show bytesAt _ _ _ = bytesAt _ _ _
      rw [hv.ctx, g .x3 (by decide), g .x4 (by decide)]
    · show bytesAt _ _ _ = bytesAt _ _ _
      rw [hv.sig, g .x5 (by decide), g .x6 (by decide)]

theorem Shake6.hh {p : Params} (hp : Shake6 p) : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `vg_slhdsa_shake_*_verify` for a SHAKE parameter set `p`, over any
implementation `T` of `thash4`, meets `verifyContract` in constant time. -/
theorem verify_verified {p : Params} (hS : Shake6 p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee) (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (g : Impl.SlhDsa.AArch64.Verify.VFns) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Verify.verify p f g) (Spec.SlhDsa.verifyContract p AArch64.abi 16) :=
  have hp := X86_64.VerifyTop.S6.par hS
  Verified.of_correct (verify_correct hp (Shake6.hh hS) v hv T ht g) (verify_ct hS hp (Shake6.hh hS) v hv T ht g)
    (vg_implies (Sz.of_vpar hp))

/-! ## The cleanup -/

/-- `verify`'s internal functions for the variant over `T` and the parameter set named `set`. -/
abbrev vfnsOf {n : Nat} (T : Thash4Impl n) (set : String) : Impl.SlhDsa.AArch64.Verify.VFns :=
  Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set T.sfx

theorem verify_fill {p : Params} (hp : Shake6 p) (sha3 : Bool) (sfx set : String) :
    Impl.SlhDsa.AArch64.Verify.verify p (fnsOf' p sha3 sfx set) (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set sfx) =
      Code.fillCalls (fnsOf' p sha3 sfx set).t4name (fnsOf' p sha3 sfx set).t4
        (Impl.SlhDsa.AArch64.Verify.verify p (stubOf (fnsOf' p sha3 sfx set))
          (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set sfx)) := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases sha3 <;> kernel_rfl

/-- What the kernel evaluates of verification, for each parameter set and
Keccak: with `thash4` a hole, its frames nest once and it writes no
PSTATE.DIT. -/
theorem vstub_ok {p : Params} (hp : Shake6 p) (sha3 : Bool) (sfx set : String) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Verify.verify p (stubOf (fnsOf' p sha3 sfx set))
        (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set sfx)) = true ∧
      Nat.ble (Impl.SlhDsa.AArch64.Verify.verify p (stubOf (fnsOf' p sha3 sfx set))
        (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set sfx)).aarch64Depth 1 = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases sha3 <;> exact ⟨by kernel_rfl, by kernel_rfl⟩

theorem verify_side {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    sideAll (fun i => !i.writesDit) (Impl.SlhDsa.AArch64.Verify.verify p (fnsOf p T set) (vfnsOf T set)) = true ∧
      (Impl.SlhDsa.AArch64.Verify.verify p (fnsOf p T set) (vfnsOf T set)).aarch64Depth ≤ 1 := by
  have h := vstub_ok hp T.sha3 T.sfx set
  have ht := KeyGen.t4_side T set
  rw [show fnsOf p T set = fnsOf' p T.sha3 T.sfx set from rfl, verify_fill hp]
  refine ⟨sideAll_fillCalls ht.1 h.1, ?_⟩
  have := Code.aarch64Depth_fillCalls_le (fnsOf' p T.sha3 T.sfx set).t4name (fnsOf' p T.sha3 T.sfx set).t4
    (Impl.SlhDsa.AArch64.Verify.verify p (stubOf (fnsOf' p T.sha3 T.sfx set))
      (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set T.sfx))
  have h2 : (Impl.SlhDsa.AArch64.Verify.verify p (stubOf (fnsOf' p T.sha3 T.sfx set))
      (Impl.SlhDsa.AArch64.Verify.VFns.ofVariant set T.sfx)).aarch64Depth ≤ 1 := Nat.le_of_ble_eq_true h.2
  rw [ht.2.1] at this
  omega

theorem verifyOk (p : Params) :
    ScrubAllOk (verifyContract p AArch64.abi 16) 16 ((verifySig p).retBits AArch64.abi.ptrBits) :=
  scrubAllOk_regs (sig := verifySig p) (Nat.le_of_ble_eq_true rfl) (by decide) (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _, _], _ => exact h

/-- `vg_slhdsa_shake_*_verify` as emitted, over any implementation `T` of
`thash4`, meets its contract in constant time and returns without secret
residue. -/
theorem verify_scrubbed {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify p (fnsOf p T set) (vfnsOf T set))
      ((verifyApi p module name).contract AArch64.abi 16) 32 := by
  have hv := verify_verified hp (f := fnsOf p T set) (kperm T.sha3) (kperm_callee T.sha3).symm T T.code_eq.symm (vfnsOf T set)
  have hs := verify_side hp T set
  exact verifiedScrubbedClearAll hv (verifyOk p) ⟨by decide, by decide, by decide⟩ (by omega) hs.1 (by decide)

theorem verify_spSafe (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (g : Impl.SlhDsa.AArch64.Verify.VFns) :
    (Impl.SlhDsa.AArch64.Fn.verify p f g).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

/-! The parameter sets, as their registrations name them. -/

theorem verify128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_128s (fnsOf shake_128s T "128s") (vfnsOf T "128s"))
      (verifyShake_128sApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inl rfl) T _ _ "128s"

theorem verify128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_128s (fnsOf shake_128s T "128s") (vfnsOf T "128s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

theorem verify128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_128f (fnsOf shake_128f T "128f") (vfnsOf T "128f"))
      (verifyShake_128fApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inr (.inl rfl)) T _ _ "128f"

theorem verify128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_128f (fnsOf shake_128f T "128f") (vfnsOf T "128f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

theorem verify192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_192s (fnsOf shake_192s T "192s") (vfnsOf T "192s"))
      (verifyShake_192sApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s"

theorem verify192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_192s (fnsOf shake_192s T "192s") (vfnsOf T "192s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

theorem verify192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_192f (fnsOf shake_192f T "192f") (vfnsOf T "192f"))
      (verifyShake_192fApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f"

theorem verify192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_192f (fnsOf shake_192f T "192f") (vfnsOf T "192f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

theorem verify256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_256s (fnsOf shake_256s T "256s") (vfnsOf T "256s"))
      (verifyShake_256sApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s"

theorem verify256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_256s (fnsOf shake_256s T "256s") (vfnsOf T "256s")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

theorem verify256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed AArch64.target (Impl.SlhDsa.AArch64.Fn.verify shake_256f (fnsOf shake_256f T "256f") (vfnsOf T "256f"))
      (verifyShake_256fApi.contract AArch64.abi 16) 32 :=
  verify_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f"

theorem verify256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.AArch64.Fn.verify shake_256f (fnsOf shake_256f T "256f") (vfnsOf T "256f")).all
      (fun i => !isa.writesSp i) = true :=
  verify_spSafe _ _ _

end VG.Proof.SlhDsa.AArch64.VerifyTop
