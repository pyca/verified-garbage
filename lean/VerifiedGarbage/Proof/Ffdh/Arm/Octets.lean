module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

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

theorem Octets.after_frame {base src : BitVec 32} {len : Nat} {bs : List Byte}
    {s t : State} {rs : List Reg} {regions : List Region} (h : Octets base src len bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (separate : ∀ r ∈ regions, (⟨State.addr src, bs.length⟩ : Region).Disjoint r) :
    Octets base src len bs t := by
  refine ⟨h.fits, ?_, h.separate, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.readable
  · rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := h.fits; omega) separate]
    exact h.bytes

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

theorem Octets.slice {base src : BitVec 32} {len : Nat} {bs : List Byte} {s : State}
    (h : Octets base src len bs s) {d k : Nat} (positive : 0 < k) (fit : d + k ≤ bs.length) :
    Octets base (src + BitVec.ofNat 32 d) len ((bs.drop d).take k) s := by
  have size : ((bs.drop d).take k).length = k := by
    simp only [List.length_take, List.length_drop]
    omega
  have dn : d < 2 ^ 32 := by have := h.fits; omega
  have pn : src.toNat + d < 2 ^ 32 := by have := h.fits; omega
  have ptrNat : (src + BitVec.ofNat 32 d).toNat = src.toNat + d := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt dn, Nat.mod_eq_of_lt pn]
  have addr : State.addr (src + BitVec.ofNat 32 d) = State.addr src + BitVec.ofNat 64 d :=
    VG.Arm.addr_add pn
  refine ⟨by rw [size, ptrNat]; have := h.fits; omega, ?_, ?_, ?_⟩
  · rw [size, addr]
    exact CallLay.inRegions_sub h.readable fit (by have := h.fits; omega)
  · rw [size, addr]
    exact h.separate.sub_left (Offset.sub_base _ fit)
  · rw [size, addr, ← VG.Proof.Dsa.bytesAt_slice _ _ fit, h.bytes]

end VG.Proof.Ffdh.Arm
