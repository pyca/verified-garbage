module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.MillerRabin.Word32
/-! # A witness conversion preserves all of the candidate's cached data -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/WitnessMont.lean`, which only this module imported.
section

/-! # Cached R² converts any sampled witness to Montgomery form -/

section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.MillerRabin

theorem witness_r2 {c w x : Nat} (odd : c % 2 = 1) :
    Word32.mm c w x (2 ^ (64 * w) * 2 ^ (64 * w) % c) = x * 2 ^ (64 * w) % c := by
  have cancel : (2 ^ (64 * w) * 2 ^ (64 * w) % c) * Word32.rinv c w % c = 2 ^ (64 * w) % c := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Word32.R_rinv odd,
      ← Nat.mul_mod, Nat.mul_one]
  unfold Word32.mm
  rw [Nat.mul_assoc, Nat.mul_mod, cancel, ← Nat.mul_mod]

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessMont
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Prepare.Data g c capacity p s)
    (odd : c % 2 = 1) (positive : 0 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont) s fun t =>
      Prepare.Data g c capacity p t ∧
      val32 t.mem g.W (g.array 5) g.words = val32 s.mem g.W (g.array 6) g.words * 2 ^ (64 * g.w) % c ∧
      WorkspaceFrame g (ranges g) s.mem t.mem ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessMont.code
  have A := S.ready
  refine WP.seq (WP.mono (mulY_ok verified noSp stack v A.context length A.modulus
    (by unfold Proof.Rsa.Mont.Operand; decide) odd (by rw [S.r2]; exact Nat.mod_lt _ positive)
    A.caller.readLen (by rw [A.caller.sp]; exact A.caller.low)
    (by rw [A.caller.sp]; exact A.caller.stackFar)) fun b ⟨Vb, Ob, Kb, Cb, Mb, Fb⟩ => ?_)
  rw [A.caller.sp] at Fb
  have B : Ready g c capacity p b := ⟨Cb, Mb, A.caller.keepFrame Kb (by decide) Fb,
    A.scratch.of_keeps Kb (by decide)⟩
  rw [S.r2, witness_r2 odd] at Vb
  refine WP.mono (Prepared.copy_ready v B 5 6 (by decide) (by decide) (by decide))
    fun t ⟨T, Vt, Ot, Kt⟩ => ?_
  have Wb := Ob.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ montWrites g 6, r ∈ ranges g)
  have Wt : WorkspaceFrame g (ranges g) b.mem t.mem :=
    WorkspaceFrame.of_outs B.scratch.nowrap (Outs.of_outside Ot (by simp [ranges]))
  have W := Wb.trans Wt
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) b.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside Ot (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide))).mono
      (fun r mem => List.mem_append_left _ mem)
  refine ⟨data_keep v S T W, Vt.trans Vb, W, Fb.trans F, ?_⟩
  exact (Kb.mono (by unfold clob; decide)).widen Kt

end VG.Proof.RsaKeyGen.X86.WitnessMont
