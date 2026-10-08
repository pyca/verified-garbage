import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.ScratchGather

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, ARMv7: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
allocates its frame of 40 bytes at `P = sp - 40`, lays out in it the call's
stack arguments, our return address and `r0`–`r3` (`entered_wp`), gathers
the slices to `dst` (`gathered_wp`), reloads `r0`–`r3` (`ready_wp`) and calls
`vg_aes_gcm_seal` on them in place (`called_wp`, by its shared contract); the
call keeps our frame, so the return address comes back from it (`ret_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Arm.FrameStack VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)
open VG.Proof.AesGcm.Arm (add_ofNat_zero covers_of_mem covers_cons covers_append' covers_prefix covers_nil
  bytesAt_frame blockAt_frame)

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 68 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 68) : State.addr (P + BitVec.ofNat 32 d) = State.addr P + BitVec.ofNat 64 d :=
  addr_add (by omega)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 68) (he : e + 4 ≤ 68) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega), aP hP (by omega)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 68) (h : 4 ≤ e) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr P) 32 = m.readW (State.addr P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_ofNat_zero] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 68) (h : 4 ≤ d) :
    (m.writeW (State.addr P) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_ofNat_zero] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

end VG.Proof.AesGcm.Arm.Gather
