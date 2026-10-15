module

public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Byte-exact equality for two readable buffers without input-dependent branches -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem compareBuffer_ok (s : State) {a b : BitVec 32} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 32) (aFit : a.toNat + n ≤ 2 ^ 32) (bFit : b.toNat + n ≤ 2 ^ 32)
    (aRead : InRegions (s.rd ++ s.wr) (State.addr a) n) (bRead : InRegions (s.rd ++ s.wr) (State.addr b) n)
    (first : s.gpr .r0 = a) (second : s.gpr .r1 = b) (count : s.gpr .lr = BitVec.ofNat 32 n) (zero : s.gpr .r2 = 0) :
    WP isa compareBytes s fun t =>
      (t.gpr .r2 = 0 ↔ Spec.Rsa.bytesAt s.mem (State.addr a) n = Spec.Rsa.bytesAt s.mem (State.addr b) n) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  have byte {p : BitVec 32} (fit : p.toNat + n ≤ 2 ^ 32) (read : InRegions (s.rd ++ s.wr) (State.addr p) n)
      (i : Nat) (hi : i < n) : InRegions (s.rd ++ s.wr) (State.addr (p + BitVec.ofNat 32 i)) 1 := by
    rw [addr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  have ctx : CompareCtx s a b n := ⟨hn', byte aFit aRead, byte bFit bRead⟩
  refine WP.mono (compareBytes_ok s ctx hn first second count zero) ?_
  intro t inv
  refine ⟨?_, inv.mem, inv.rest⟩
  rw [inv.equal, VG.Proof.Rsa.bytesAt_eq_iff]
  constructor
  · intro equal i hi
    have h := equal i hi
    rw [addr_add (by omega), addr_add (by omega)] at h
    exact h
  · intro equal i hi
    rw [addr_add (by omega), addr_add (by omega)]
    exact equal i hi
end VG.Proof.Bignum.Arm
