module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame

/-!
# `vg_rsa_recover_primes` on PPC64LE: a bit's flags

`flags_ok`: from the bit, `done`, `ok` and whether the new `y` is 1 or -1,
`live` (the root is the old `y`), `ok` and `done`, as `Fused.step` has them.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (flags nArr sDone sOk sBit sLive sE1 sE2)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The flags, on words. -/
theorem flags64 (bit done ok e1 e2 : Bool) :
    (b64 done ^^^ 1#64) &&& (b64 bit ^^^ 1#64) &&& b64 e1 = b64 (!bit && !done && e1) ∧
      (b64 ok ||| b64 (!bit && !done && e1)) &&& (b64 bit ^^^ 1#64) =
        b64 ((ok || (!bit && !done && e1)) && !bit) ∧
      (b64 done &&& (b64 bit ^^^ 1#64) ||| b64 e1 ||| b64 e2) = b64 (done && !bit || e1 || e2) := by
  cases bit <;> cases done <;> cases ok <;> cases e1 <;> cases e2 <;> decide

/-- `flags`: `live`, `ok` and `done`. -/
theorem flags_ok {s0 u : State} (w : Ws u (rvB s0) (rvZ s0) (ww (kK s0)) nArr) {bit done ok e1 e2 : Bool}
    (hB : slot u.mem (rvB s0) sBit = b2n bit) (hD : slot u.mem (rvB s0) sDone = b2n done)
    (hO : slot u.mem (rvB s0) sOk = b2n ok) (h1 : slot u.mem (rvB s0) sE1 = b2n e1)
    (h2 : slot u.mem (rvB s0) sE2 = b2n e2) :
    WP isa (.block flags) u fun v => v.mem =
      ((u.mem.writeW (off (rvB s0) sLive) (BitVec.ofNat 32 (b2n (!bit && !done && e1)))).writeW
        (off (rvB s0) sOk) (BitVec.ofNat 32 (b2n ((ok || (!bit && !done && e1)) && !bit)))).writeW
        (off (rvB s0) sDone) (BitVec.ofNat 32 (b2n (done && !bit || e1 || e2))) ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8] u v := by
  have hz : 160 ≤ rvZ s0 := w.hdr_le
  obtain ⟨F1, F2, F3⟩ := flags64 bit done ok e1 e2
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8] (Q := fun x => x.mem =
    ((u.mem.writeW (rvB s0 + BitVec.ofNat 64 sLive)
      (BitVec.setWidth 32 ((b64 done ^^^ 1#64) &&& (b64 bit ^^^ 1#64) &&& b64 e1))).writeW
      (rvB s0 + BitVec.ofNat 64 sOk)
      (BitVec.setWidth 32 ((b64 ok ||| (b64 done ^^^ 1#64) &&& (b64 bit ^^^ 1#64) &&& b64 e1) &&&
        (b64 bit ^^^ 1#64)))).writeW
      (rvB s0 + BitVec.ofNat 64 sDone)
      (BitVec.setWidth 32 (b64 done &&& (b64 bit ^^^ 1#64) ||| b64 e1 ||| b64 e2)))
    ?_ (by decide)) fun v ⟨m, kv⟩ => ⟨?_, kv⟩
  · prun [flags, w.r31, w.scr.ld (show sBit + 4 ≤ rvZ s0 by simp only [sBit]; omega),
      w.scr.ld (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega),
      w.scr.ld (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega),
      w.scr.ld (show sE1 + 4 ≤ rvZ s0 by simp only [sE1]; omega),
      w.scr.ld (show sE2 + 4 ≤ rvZ s0 by simp only [sE2]; omega),
      w.scr.st (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega),
      w.scr.st (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega),
      w.scr.st (show sLive + 4 ≤ rvZ s0 by simp only [sLive]; omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sBit < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE1 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE2 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sLive < 2 ^ 15 by decide),
      ld_slot hB, ld_slot hD, ld_slot hO, ld_slot h1, ld_slot h2]
  · rw [m, F1, F2, F3, b64_w32, b64_w32, b64_w32]

end VG.Proof.Rsa.PPC64LE.Recover
