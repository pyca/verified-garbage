module

public import VerifiedGarbage.Impl.Bignum.Arm.Store64
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rc2.PairMem
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A native store pair has exactly the shared 64-bit memory effect -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_str)

theorem store64_ok (s : State) (lo hi ptr : Reg) (d : Nat) (a : Addr)
    (hd : d + 4 < 4096)
    (pa : State.addr (s.gpr ptr + BitVec.ofNat 32 d) = a)
    (pb : State.addr (s.gpr ptr + BitVec.ofNat 32 (d + 4)) = a + BitVec.ofNat 64 4)
    (wa : InRegions s.wr a 4) (wb : InRegions s.wr (a + BitVec.ofNat 64 4) 4) :
    WP isa (.block (store64 lo hi ptr d)) s fun t =>
      t.mem = s.mem.writeW a (s.gpr hi ++ s.gpr lo) ∧ Rest [] s t := by
  unfold store64
  refine wp_str (a := a) (by omega) pa wa fun u h => ?_
  refine wp_str (a := a + BitVec.ofNat 64 4) hd (by rw [h.gpr]; exact pb)
    (by rw [h.wr]; exact wb) fun t j => WP.block_nil ?_
  refine ⟨?_, (h.rest _).trans (j.rest _)⟩
  rw [j.mem, h.mem, h.gpr, ← VG.Proof.Rc2.Word32.write64_pair]

/-- A zero high half is the ordinary zero-extended native pointer. -/
theorem zero_high_addr (p : BitVec 32) : ((0 : BitVec 32) ++ p) = State.addr p := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt p.isLt, Nat.shiftLeft_eq]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add]
  simp only [State.addr, BitVec.toNat_setWidth]
  have hp : p.toNat < 2 ^ 64 := by have := p.isLt; omega
  exact (Nat.mod_eq_of_lt hp).symm

end VG.Proof.Bignum.Arm
