module

public import VerifiedGarbage.Impl.Bignum.Arm.InitInverse
public import VerifiedGarbage.Proof.Bignum.Arm.Newton64
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.Minv64
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Full-width inverse initialization on ARMv7 -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem initInverse_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (header : 64 ≤ size) (modFit : d + 8 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 d) (saved : s.gpr .r12 = base)
    (odd : (s.mem.readW (off (State.addr base) d) 64).toNat % 2 = 1) :
    WP isa initInverse s fun t => ∃ inv : BitVec 64,
      ((s.mem.readW (off (State.addr base) d) 64).toNat * inv.toNat + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem.writeW (off (State.addr base) 56) inv ∧
      t.gpr .r0 = base ∧ Rest (.r0 :: newtonClobbers) s t := by
  have pair := VG.Proof.Rc2.Word32.read64_pair s.mem (off (State.addr base) d)
  have next : off (State.addr base) d + BitVec.ofNat 64 4 = off (State.addr base) (d + 4) :=
    Offset.add_add _ _ _
  rw [next] at pair
  rw [initInverse, WP.seq_iff]
  refine WP.mono (minv64_ok s (off (State.addr base) d) (off (State.addr base) (d + 4))
    (by simpa using ws.ea (imm := 0) ptr (by omega))
    (ws.ea ptr (by omega)) (ws.read (by omega)) (ws.read (by omega)) (pair ▸ odd)) ?_
  rintro u ⟨inverse, mem, rest⟩
  have savedU : u.gpr .r12 = base := (rest.gpr .r12 (by simp [newtonClobbers])).trans saved
  have wsU := ws.congr rest.wr
  rw [WP.seq_iff]
  refine WP.mono (store64_ok u .r2 .r11 .r12 56 (off (State.addr base) 56) (by decide)
    (wsU.ea (off := 0) (by simpa using savedU) (by omega))
    (by rw [show off (State.addr base) 56 + BitVec.ofNat 64 4 = off (State.addr base) 60 from Offset.add_add _ _ _]
        exact wsU.ea (off := 0) (by simpa using savedU) (by omega))
    (wsU.write (by omega))
    (by rw [show off (State.addr base) 56 + BitVec.ofNat 64 4 = off (State.addr base) 60 from Offset.add_add _ _ _]
        exact wsU.write (by omega))) ?_
  rintro v ⟨stored, keep⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  refine ⟨u.gpr .r11 ++ u.gpr .r2, ?_, ?_, ?_, ?_⟩
  · rw [pair]; exact inverse
  · rw [moved.mem, stored, mem]
  · rw [moved.gpr, keep.gpr .r12 (by simp), savedU]
  · exact (rest.mono (by simp)).trans ((keep.mono (by simp)).trans (moved.rest (by simp)))

end VG.Proof.Bignum.Arm
