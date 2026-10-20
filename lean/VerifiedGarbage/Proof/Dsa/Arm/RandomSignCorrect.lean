module
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFinish

import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The randomized signer meets its contract (32-bit ARM)

`code` reserves its frame and runs the body (`body_ok`): on return the
callee-saved registers and `sp` are as on entry, and the status, `out` and
`used` are those of `Spec.Dsa.randomSignBytes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (toNat_imm)

theorem code_ok (name : String) {s₀ : State} (A : RandomABI s₀) :
    WP isa (code name (Entry.operation true)) s₀ fun s' => ∃ u, Finished s₀ u ∧ s' = freed frameBytes u :=
  WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by have := A.stackLow; unfold frameBytes; omega)
    (WP.mono (body_ok name A) fun u hu => ⟨u, hu, rfl⟩)

/-- `vg_dsa_sign_random` meets its contract. -/
theorem randomSign_correct (name : String) (s : State)
    (hpre : (Spec.Dsa.randomSignContract Arm.abi 144).pre s) :
    ∃ t s', Exec isa (code name (Entry.operation true)) s t s' ∧ abiPreserved s s' ∧
      (Spec.Dsa.randomSignContract Arm.abi 144).post s s' := by
  have A := randomABI_of hpre
  obtain ⟨t, s', he, u, hF, rfl⟩ := code_ok name A
  refine ⟨t, _, he, ⟨fun r hr => hF.regs r hr, by
    show u.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hF.sp, BitVec.sub_add_cancel]⟩, ?_⟩
  sig_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero]
  have hle := rResult_status_le A
  have hul : (rResult s).used < 2 ^ 32 := by
    have := rResult_used_le (s₀ := s)
    have : (rInput s).rand.length < 2 ^ 32 := by simp only [rInput, rBytes_length]; exact BitVec.isLt _
    omega
  refine ⟨?_, hF.out, ?_⟩
  · rw [BitVec.setWidth_append_eq_right]
    show (u.gpr .r0).toNat = (rResult s).status
    rw [hF.r0, toNat_imm (by omega)]
  · show Spec.Rsa.wordsAt u.mem (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (rResult s).used]
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    refine congrArg (· :: []) (BitVec.eq_of_toNat_eq ?_)
    have := word_eq_w32 u.mem (State.addr (s.gpr .r2)) 0
    simp only [Mont.word, w32, off] at this
    show (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 64).toNat = _
    rw [this, show (0 + 4 : Nat) = 4 from rfl]
    have lo : (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 32) = _ := hF.usedLo
    have hi : (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 4) 32) = _ := hF.usedHi
    rw [lo, hi, toNat_imm hul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl

end VG.Proof.Dsa.Arm
