import VerifiedGarbage.Proof.Camellia.X86_64.KeyChecks
import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey

/-!
# The key schedule's evaluated facts on x86-64

The planes of `Sigma1 … Sigma6` that `sigmaOne` stores (`sigma_planes`),
and `spread k`, which bitslices the word in slot `k` into all eight lanes
as `toBs` bitslices eight words, keeping the masks and both halves'
slots (`spread_check`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (HalfRel pos)

theorem bytePos_eq : bytePos = pos := rfl

/-- The planes `sigmaOne` stores hold the constant in every lane. -/
theorem sigma_planes : ∀ x ∈ sigmas, ∀ b < 8, ∀ c < 8, ∀ j < 8,
    (keyPlane x j).getLsbD (8 * c + b) = (Camellia.byteOf x (pos c)).getLsbD j := by
  decide +kernel

/-- All the slots of the scratch buffer, from `sb`. -/
def scrCfg : Cfg := { base := sb, slots := slots, ext := sb, exts := 0 }

/-- Slot `k` is input word 0, both halves' slots words `1 … 16`. -/
def spreadIns (k : Nat) : List (Nat × Nat) := (k, 0) :: (List.range 16).map fun j => (d1Slot + j, 1 + j)

def spreadEnv (k : Nat) : Env (Nat × Nat) := linEnvG [] (spreadIns k) layerMasks

theorem spread_checkW :
    check (lanes 64 11) scrCfg (linExt 0) (spread wSlot) (spreadEnv wSlot)
      (linPostG 11 (qOuts (keyBsG 0)) [] (maskSlots ++ (spreadIns wSlot).map (·.1)) (spreadEnv wSlot)) = true := by
  decide +kernel

theorem spread_checkW1 :
    check (lanes 64 11) scrCfg (linExt 0) (spread (wSlot + 1)) (spreadEnv (wSlot + 1))
      (linPostG 11 (qOuts (keyBsG 0)) [] (maskSlots ++ (spreadIns (wSlot + 1)).map (·.1))
        (spreadEnv (wSlot + 1))) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
