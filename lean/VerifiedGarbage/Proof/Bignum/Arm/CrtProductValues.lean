module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # Interpret native product operands in the shared RSA number model -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem val32_numAt_offset (m : Mem) (base child : Addr) (d w j : Nat)
    (address : child = base + BitVec.ofNat 64 d) :
    val32 m base (d + arrAt w j) (2 * w) = numAt m child w j := by
  rw [← read_eq_val32, numAt, address, Offset.add_add]
  congr 2 <;> omega

theorem CrtShared.product_values {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (coefficient : Bool) :
    val32 s.mem (State.addr g.base) (crtProductA g.words coefficient) (2 * g.words) =
      numAt s.mem (State.addr (crtP g.base g.words)) g.words (if coefficient then 5 else 0) ∧
    val32 s.mem (State.addr g.base) (crtProductB g.words) (2 * g.words) =
      numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses h.buffers.workspace h.buffers.storageFits
  exact ⟨val32_numAt_offset _ _ _ _ _ _ paddr, val32_numAt_offset _ _ _ _ _ _ qaddr⟩

end VG.Proof.Bignum.Arm
