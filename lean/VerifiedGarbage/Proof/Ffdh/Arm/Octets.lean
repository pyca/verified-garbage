module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! External octet buffers stay intact across native FFDH arithmetic. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure Octets (base src : BitVec 32) (len : Nat) (bs : List Byte) (s : State) : Prop where
  fits : src.toNat + bs.length ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) bs.length
  separate : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : Spec.Rsa.bytesAt s.mem (State.addr src) bs.length = bs

theorem Octets.after_workspace {base src : BitVec 32} {len : Nat} {bs : List Byte}
    {s t : State} {rs : List Reg} (h : Octets base src len bs s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    Octets base src len bs t := by
  refine ⟨h.fits, ?_, h.separate, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.readable
  · rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := h.fits; omega)
      (by simpa using h.separate)]; exact h.bytes

theorem Octets.byte {base src : BitVec 32} {len : Nat} {bs : List Byte} {s : State}
    (h : Octets base src len bs s) (i : Nat) (hi : i < bs.length) :
    s.mem (State.addr src + BitVec.ofNat 64 i) = bs[i] := by
  have eq := congrArg (fun l : List Byte => l[i]?) h.bytes
  simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, List.getElem?_eq_getElem hi, Option.some.injEq] using eq

end VG.Proof.Ffdh.Arm
