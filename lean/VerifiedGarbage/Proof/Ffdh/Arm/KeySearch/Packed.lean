module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Ffdh.Arm.InitValues
import VerifiedGarbage.Proof.Framework.Offset

/-! Exact packed-u64 reads and preservation of their zero high halves. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

theorem packedWord (m : Mem) (base : BitVec 32) (j n : Nat) (fits : n < 2 ^ 32)
    (lo : lowWord m base j = BitVec.ofNat 32 n)
    (hi : m.readW (off (State.addr base) (8 * j + 4)) 32 = 0) :
    m.readW (off (State.addr base) (8 * j)) 64 = BitVec.ofNat 64 n := by
  rw [VG.Proof.Rc2.Word32.read64_pair]
  have addr : off (State.addr base) (8 * j) + BitVec.ofNat 64 4 =
      off (State.addr base) (8 * j + 4) := by simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [addr, hi, show m.readW (off (State.addr base) (8 * j)) 32 = BitVec.ofNat 32 n from lo, zeroHigh]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

theorem highWord_store (m : Mem) (base : BitVec 32) (v : BitVec 32) {i j : Nat}
    (hi : i < 16) (hj : j < 16) :
    (m.writeW (off (State.addr base) (8 * i)) v).readW (off (State.addr base) (8 * j + 4)) 32 =
      m.readW (off (State.addr base) (8 * j + 4)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem highWord_writeLow (m : Mem) (base : BitVec 32) (values : List (Nat × BitVec 32))
    (bounds : ∀ e ∈ values, e.1 < 16) (j : Nat) (hj : j < 16) :
    (writeLow m base values).readW (off (State.addr base) (8 * j + 4)) 32 =
      m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  induction values generalizing m with
  | nil => rfl
  | cons e tail ih =>
    change (writeLow (m.writeW (off (State.addr base) (8 * e.1)) e.2) base tail).readW _ _ = _
    rw [ih _ (fun v hv => bounds v (List.mem_cons_of_mem _ hv)),
      highWord_store _ _ _ (bounds e (List.mem_cons_self ..)) hj]

end VG.Proof.Ffdh.Arm.KeySearch
