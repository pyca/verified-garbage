module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! Mask the first significant entropy byte and set the remaining public count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sampleFirst_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {src dst : BitVec 32}
    (h : SampleMemory p l slots s)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) 1)
    (write : InRegions s.wr (State.addr dst) 1)
    (separate : (⟨off (State.addr s.sp) 20, 4⟩ : Region).Disjoint ⟨State.addr dst, 1⟩) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s fun t =>
      (t.mem = s.mem.writeW (State.addr dst) ((s.mem (State.addr src)) &&& l.mask.setWidth 8) ∧
        t.gpr .r0 = dst + 1 ∧ t.gpr .r1 = src + 1 ∧
        t.gpr .lr = BitVec.ofNat 32 l.width - 1) ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have r20 := h.locals.read (d := 20) (by decide)
  have r68 := h.locals.read (d := 68) (by decide)
  refine withRest_all [.r0, .r1, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  have keep (v : Byte) : (s.mem.writeW (State.addr dst) v).readW (off (State.addr s.sp) 20) 32 =
      BitVec.ofNat 32 l.width := by
    have frame : Frame [⟨State.addr dst, 1⟩] s.mem (s.mem.writeW (State.addr dst) v) :=
      (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    rw [frame.readW (r := ⟨off (State.addr s.sp) 20, 4⟩) (Region.contains_self _ _)
      (by simpa using separate) (by decide)]
    exact h.scalarWidth
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.first
  ffrun [source, dest, read, write, addr 20 (by decide), addr 68 (by decide), r20, r68,
    h.scalarWidth, h.scalarMask, Inputs.slotValue, BitVec.add_zero, off, BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  exact congrArg (fun x : BitVec 32 => x - 1) (keep _)

end VG.Proof.Ffdh.Arm
