module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-! Branch-free masking of either complete key encoding by its saved validity flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyMaskArgs_ok (s : State) {p : Inputs} {slots : List Nat} {flag : BitVec 32} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag) :
    WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64,
      .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) s fun t =>
      (t.gpr .r0 = p.slotValue slot ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧
        t.gpr .r2 = 0 - flag ∧ t.mem = s.mem) ∧ Rest [.r0, .r2, .r3, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  refine withRest_all [.r0, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  ffrun [(by omega : slot < 4096), addr slot fit, addr 32 (by decide), addr 64 (by decide),
    h.locals.read fit, h.locals.read (d := 32) (by decide), h.locals.read (d := 64) (by decide),
    h.saved slot hs, h.saved 32 hk, result, Inputs.slotValue]

theorem keyMask_ok (s : State) {p : Inputs} {slots : List Nat} {flag : BitVec 32} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag)
    (output : OutputBuffer (p.slotValue slot) p.k s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (p.slotValue slot)) p.k =
        (Spec.Rsa.bytesAt s.mem (State.addr (p.slotValue slot)) p.k).map (· &&& (0 - flag).setWidth 8) ∧
      Frame [⟨State.addr (p.slotValue slot), p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput, WP.seq_iff]
  refine WP.mono (keyMaskArgs_ok s slot h fit hs hk result) ?_
  rintro u ⟨⟨ptr, count, mask, mem⟩, restU⟩
  refine WP.mono (VG.Proof.Bignum.Arm.maskBuffer_ok u (by have := p.minLength; omega)
    (by have := p.maxLength; omega) output.fits (by rw [restU.wr]; exact output.writable) ptr count) ?_
  rintro t ⟨bytes, frame, rest⟩
  rw [mask, mem] at bytes
  exact ⟨bytes, by rw [mem] at frame; exact frame, (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm
