module
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Bignum.Arm.Setup

import VerifiedGarbage.Proof.Bignum.Arm.SetupArgs
import VerifiedGarbage.Proof.Bignum.Arm.SetBases
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Establish the shared RSA workspace contract on ARMv7 -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem setup_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) (ptr : s.gpr .r0 = base)
    (count : s.gpr .r7 = BitVec.ofNat 32 w) (zero : s.gpr .r3 = 0) :
    WP isa setup s fun t => Layout t.mem (State.addr base) len ∧
      wOf t.mem (State.addr base) = w ∧ t.gpr .r0 = base ∧
      Outs (State.addr base) [(48, 8), (64, 64)] s.mem t.mem ∧
      Rest [.r0, .r4, .r5, .r8, .lr] s t := by
  have nowrap := ws.nowrap
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have a48 : State.addr (s.gpr .r0 + BitVec.ofNat 32 48) = off (State.addr base) 48 := by
    rw [ptr]; exact addr_add (by omega)
  have a52 : State.addr (s.gpr .r0 + BitVec.ofNat 32 (48 + 4)) =
      off (State.addr base) 48 + BitVec.ofNat 64 4 := by
    rw [ptr, addr_add (by omega)]
    exact (Offset.add_add _ _ _).symm
  have wr52 : InRegions s.wr (off (State.addr base) 48 + BitVec.ofNat 64 4) 4 := by
    rw [Offset.add_add]; exact ws.write (by omega)
  rw [setup, WP.seq_iff]
  refine WP.mono (store64_ok s .r7 .r3 .r0 48 _ (by decide) a48 a52
    (ws.write (by omega)) wr52) ?_
  rintro u ⟨memU, restU⟩
  have width : (s.gpr .r3 ++ s.gpr .r7) = BitVec.ofNat 64 w := by
    rw [zero, count, zero_high_addr]
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : w < 2 ^ 32), Nat.mod_eq_of_lt (by omega : w < 2 ^ 64)]
  rw [width] at memU
  have outU := writeW_outside s.mem (State.addr base) (d := 48) (BitVec.ofNat 64 w) (by decide)
  rw [← memU] at outU
  rw [WP.seq_iff]
  refine WP.mono (setupArgs_ok u ((restU.gpr .r7 (by decide)).trans count)) ?_
  rintro v ⟨saved, vp, vc, stride, remaining, memV, restV⟩
  have up : u.gpr .r0 = base := (restU.gpr .r0 (by decide)).trans ptr
  rw [up] at saved vp vc
  rw [WP.seq_iff]
  refine WP.mono (setBases_ok v (ws.congr (restV.wr.trans restU.wr)) fits vp vc remaining stride
    ((restV.gpr .r3 (by decide)).trans ((restU.gpr .r3 (by decide)).trans zero))) ?_
  intro z bases
  refine wp_mov (op2_reg _ _) fun t h => WP.block_nil ?_
  have memT : t.mem = z.mem := h.mem
  have baseT : t.gpr .r0 = base := by rw [h.gpr, bases.rest.gpr .r8 (by decide), saved]
  have widthT : word t.mem (State.addr base) 48 = BitVec.ofNat 64 w := by
    rw [memT, bases.outside.word (d := 48) (by decide) (by decide), memV, memU, word_writeW_self]
  have wT : wOf t.mem (State.addr base) = w := by
    change (word t.mem (State.addr base) 48).toNat = w
    rw [widthT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, wT, baseT, ?_, ?_⟩
  · change 2 ≤ wOf t.mem (State.addr base) ∧ _
    rw [wT]
    refine ⟨hw, hw', fits, ?_⟩
    intro j hj
    change word t.mem (State.addr base) (8 * (8 + j)) = _
    rw [show 8 * (8 + j) = 64 + 8 * j by omega, memT]
    exact bases.header j hj
  · have outZ := bases.outside
    rw [memV] at outZ
    rw [memT]
    exact (Outs.of_outside outU (by decide)).trans (Outs.of_outside outZ (by decide))
  · exact (restU.mono (by decide)).trans (restV.trans
      ((bases.rest.mono (by decide)).trans (h.rest (by decide))))

end VG.Proof.Bignum.Arm
