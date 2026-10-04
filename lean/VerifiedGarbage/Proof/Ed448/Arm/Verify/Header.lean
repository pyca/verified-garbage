import VerifiedGarbage.Proof.Ed448.Arm.Verify.Layout
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Header

/-!
# Ed448 verification on ARMv7: the header of `dom4`

`hdr_ok`: the block `hdr` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten
bytes of `dom4(0, context)`, in the frame at `HDR` (`Shake.Kit.hdr_ok`).
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem hdr_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.block hdr) t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L :=
  WP.mono (hL.kit.hdr_ok hc ha (j := 2) (by decide) hL.cl (by decide)) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

end VG.Proof.Ed448.Arm.Verify
