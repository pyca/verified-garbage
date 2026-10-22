module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideTile

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! Preserve the selected prefix and table context across 128-byte tiles. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

structure WLoopInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc v j : Nat)
    (t : State) : Prop where
  ctx : TableCtx t P w mi X Xc
  tab : word t.mem P (8 * Crt.sTab) = off P (slot w 8)
  stride : t.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2))
  ptr : t.gpr .x17 = off P (slot w Crt.aT + 128 * j)
  digit : t.gpr .x5 = BitVec.ofNat 64 (32 - v)
  ones : t.gpr .x7 = BitVec.allOnes 64
  zero : t.gpr .x8 = 0
  frame : Outside P (slot w Crt.aT) (128 * j) s.mem t.mem
  bytes : ∀ k < 128 * j, t.mem (off P (slot w Crt.aT + k)) =
    s.mem (off P (slot w 8 + 8 * (w + 2) * v + k))
  keep : Keep mmRegs s t

def wtileStep : Prog isa := .seq wtile
  (.block [.addImm .x .x17 .x17 128, .subImm .x .x13 .x13 1])

def rawWide : Prog isa :=
  .seq (.block (wideHead ++
      VG.Impl.Rsa.AArch64.WindowSelectVector.accsWide.map fun r => .vop (.movi0 r)))
    (.seq (countLoop .x14 VG.Impl.Rsa.AArch64.WindowSelectVector.innerWide)
      (.block (stores 8 ++ [.addImm .x .x17 .x17 128, .subImm .x .x13 .x13 1])))

theorem rawWide_wp (s : State) (Q : State → Prop) :
    WP isa rawWide s Q ↔ WP isa wtileStep s Q := by
  unfold rawWide wtileStep wtile
  simp only [WP.seq_iff (M := isa), WP.block_append_iff (M := isa)]

theorem wloopStep_ok {s t : State} {P : Addr} {w v j : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hv : v < 32) (hj : 16 * j + 16 ≤ w) (hI : WLoopInv s P w mi X Xc v j t) :
    WP isa wtileStep t fun u => WLoopInv s P w mi X Xc v (j + 1) u ∧
      u.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.ctx.scrT.nowrap
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  have hE := VG.Proof.Bignum.CrtWindowFive.ent32_le w hv
  have he : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]
  unfold wtileStep
  apply WP.seq
  refine WP.mono (wtile_ok hI.ctx hv hI.tab hI.ptr hI.stride hI.digit hI.ones hI.zero
    (by omega) (fun r hr i hi => wtile_ld hI.ctx hj hr hi)
    (fun i hi => wtile_st hI.ctx hj hi)) fun a ⟨ka,ho,hb⟩ => ?_
  have hcopy : ∀ k < 128, a.mem (off P (slot w Crt.aT + 128 * j + k)) =
      s.mem (off P (slot w 8 + 8 * (w + 2) * v + 128 * j + k)) := by
    intro k hk
    rw [hb k hk]
    have hs := hI.frame (off P (slot w 8 + 128 * j + 8 * (w + 2) * v + k)) (by
      simp only [ofs, off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show slot w 8 + 128 * j + 8 * (w + 2) * v + k < 2 ^ 64 by omega)]
      omega)
    rw [hs]
    congr 2
    omega
  have copied := copy_append (by omega) hI.frame ho hI.bytes hcopy
  refine WP.mono (wtileAdvance_ok a) fun u ⟨⟨hp,hc,hm,_⟩,ku⟩ => ?_
  have frame : Outside P (slot w Crt.aT) (128 * (j + 1)) s.mem u.mem := by
    rw [hm, Nat.mul_add, Nat.mul_one]
    exact copied.1
  have localFrame : Frm P (crtWinRanges w) t.mem u.mem := by
    rw [hm]
    exact (Frm.of_outside (ho.mono (o' := slot w Crt.aT) (n' := 8 * (w + 2))
      (by omega) (by omega)) (by simp [crtWinRanges]))
  have keep := (ka.trans ku).mono (rs' := mmRegs) (by decide)
  refine ⟨⟨hI.ctx.of_win localFrame keep.wr (keep.gpr .x0 (by decide)), ?_, ?_, ?_, ?_, ?_, ?_,
    frame, ?_, (hI.keep.trans keep).mono (by decide)⟩, ?_⟩
  · rw [hm, ho.word (by have := hdr_lt_slot w Crt.aT (show Crt.sTab < 32 by decide); omega)
      (by decide)]
    exact hI.tab
  · rw [ku.gpr .x6 (by decide), ka.gpr .x6 (by decide)]
    exact hI.stride
  · rw [hp, ka.gpr .x17 (by decide), hI.ptr, off_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  · rw [ku.gpr .x5 (by decide), ka.gpr .x5 (by decide)]; exact hI.digit
  · rw [ku.gpr .x7 (by decide), ka.gpr .x7 (by decide)]; exact hI.ones
  · rw [ku.gpr .x8 (by decide), ka.gpr .x8 (by decide)]; exact hI.zero
  · simpa only [hm, Nat.mul_add, Nat.mul_one] using copied.2
  · rw [hc, ka.gpr .x13 (by decide)]

theorem wblocks_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hw : 16 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (h0 : WLoopInv s P w mi X Xc v 0 s)
    (hc : s.gpr .x13 = BitVec.ofNat 64 (w / 16)) :
    WP isa (.loop rawWide (.nonzero .x .x13)) s (WLoopInv s P w mi X Xc v (w / 16)) := by
  apply wp_countdown (by omega) (by omega) (fun j => WLoopInv s P w mi X Xc v j)
    (fun j hj t hI _ => (rawWide_wp _ _).mpr (wloopStep_ok hv (by omega) hI)) h0 hc

end VG.Proof.Bignum.AArch64.WindowVector
