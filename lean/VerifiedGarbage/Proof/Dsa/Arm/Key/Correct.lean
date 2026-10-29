module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Mont.Words32

/-!
# DSA key generation on 32-bit ARM: correctness

`generateKey_correct`: from the shared contract's precondition,
`vg_dsa_generate_key` returns the status of `Spec.Dsa.generateKeyBytes`,
writes its key (or zeros) and publishes its consumption as a 64-bit count,
and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (toNat_imm)

theorem rResult_used_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).used ≤ (rInput s₀).rand.length := by
  rw [rResult_eq A]
  split
  · split
    all_goals
      have := VG.Proof.Dsa.Random.sample_used_le (rq s₀) 128 ((rInput s₀).rand.drop 0)
      simpa [spl] using this
  · exact Nat.zero_le _

theorem code_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (code check derive Generate.checkParameters Generate.deriveKey) s₀ fun s' => ∃ u, Finished s₀ u ∧ s' = freed frameBytes u :=
  WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by have := A.stackLow; unfold frameBytes; omega)
    (WP.mono (body_ok check derive A) fun u hu => ⟨u, hu, rfl⟩)

/-- `vg_dsa_generate_key` meets its contract. -/
theorem generateKey_correct (check derive : String) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract Arm.abi 144).pre s) :
    ∃ t s', Exec isa (code check derive Generate.checkParameters Generate.deriveKey) s t s' ∧
      abiPreserved s s' ∧ (Spec.Dsa.generateKeyContract Arm.abi 144).post s s' := by
  have A := keyABI_of hpre
  obtain ⟨t, s', he, u, hF, rfl⟩ := code_ok check derive A
  refine ⟨t, _, he, ⟨fun r hr => hF.regs r hr, by
    show u.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hF.sp, BitVec.sub_add_cancel]⟩, ?_⟩
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero]
  have hle := rResult_status_le A
  have hul : (rResult s).used < 2 ^ 32 := by
    have := rResult_used_le A
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

end VG.Proof.Dsa.Arm.Key
