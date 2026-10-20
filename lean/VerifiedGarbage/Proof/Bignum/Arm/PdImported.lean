module

import VerifiedGarbage.Proof.Bignum.Arm.PdPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.PdChecked
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # The precomputed RSA path imports, validates, and applies a packed public key -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdImported_ok (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s) :
    WP isa PdFn.imported s fun t => PdOutput dst k N R eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PdFn.imported, WP.seq_iff]
  refine WP.mono (pdPrepare_ok s h) ?_
  rintro u ⟨hu, input, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (pdImport_ok u input) ?_
  rintro v ⟨ready, modulus, r2, frameV, restV⟩
  have hv := hu.after_workspace frameV restV ready.ptr
  have check : PdCheckState base len (Spec.Rsa.modulusWords k) N R v :=
    ⟨ready, by have := hv.stack.nowrap; omega,
      ⟨_, hv.stack.frameWritable, Offset.contains_base _ (by decide) (by decide)⟩,
      hv.stack.separate.symm.sub_right (Offset.sub_base _ (by decide)),
      modulus.trans hu.modulus, r2.trans hu.r2⟩
  refine WP.mono (pdChecked_ok v hv check) ?_
  rintro t ⟨result, frameT, restT⟩
  rw [restV.sp, restU.sp] at frameT
  exact ⟨result, (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans frameT),
    restU.trans (restV.trans restT)⟩
end VG.Proof.Bignum.Arm
