import VerifiedGarbage.Proof.Camellia.X86_64.KeyChecks
import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey

/-!
# The key schedule's evaluated facts on x86-64

The planes of a constant that `sigmaOne` stores (`sigma_planes`),
and `spread d`, which bitslices the word at `[rdi + d]` into all eight
lanes as `toBs` bitslices eight words, keeping the masks and both halves'
slots (`spread0_check`, `spread8_check`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (HalfRel pos)

theorem bytePos_eq : bytePos = pos := rfl

theorem keyPlane_bit (x : BitVec 64) (j : Nat) {p : Nat} (hp : p < 64) :
    (keyPlane x j).getLsbD p = x.getLsbD (56 - 8 * bytePos (p / 8) + j) := by
  rw [keyPlane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hp]
  simp [hp]

/-- The planes `sigmaOne` stores hold the constant in every lane. -/
theorem sigma_planes (x : BitVec 64) {b c j : Nat} (hb : b < 8) (hc : c < 8) (hj : j < 8) :
    (keyPlane x j).getLsbD (8 * c + b) = (Camellia.byteOf x (pos c)).getLsbD j := by
  rw [keyPlane_bit x j (by omega), Camellia.getLsbD_byteOf x (Camellia.pos_lt hc) hj, bytePos_eq,
    show (8 * c + b) / 8 = c by omega]

/-- The halves' slots are input words 2–17, after the running value's two at `rdi`. -/
def kaIns : List (Nat × Nat) := (List.range 16).map fun j => (d1Slot + j, 2 + j)

def kaEnv : Env (Nat × Nat) := linEnvG [] kaIns layerMasks

/-- `spread d`: the running value's word at `[rdi + d]` in all lanes,
keeping the masks and both halves' slots. -/
theorem spread0_check :
    check (lanes 64 11) (keyCfg 2) (linExt 0) (spread 0) kaEnv
      (linPostG 11 (qOuts (keyBsG 0)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

theorem spread8_check :
    check (lanes 64 11) (keyCfg 2) (linExt 0) (spread 8) kaEnv
      (linPostG 11 (qOuts (keyBsG 8)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
