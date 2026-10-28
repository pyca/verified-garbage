module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorHead
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStart
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBlock
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! One complete SIMD selection tile, including initialization, all rows and stores. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs inner)

def tile : Prog isa := .seq (.block (blockHead ++ accs.map fun r => .vop (.movi0 r)))
  (.seq (countLoop .x14 inner) (.block (stores 4)))

theorem tableTile_ld {s : State} {P : Addr} {w b j i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hb : 8 * b + 8 ≤ w) (hj : j < 32) (hi : i < 4) :
    InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i)) 16 := by
  have he : slot w 8 + 8 * (w + 2) * j = slot w (8 + j) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm j, Nat.add_assoc]
  have hE := VG.Proof.Bignum.CrtWindowFive.ent32_le w hj
  obtain ⟨r, hr, hR⟩ := hc.scrT.region
    (d := slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i) (n := 16)
    (by omega) (by decide)
  exact ⟨r, List.mem_append_right _ hr, hR⟩

theorem tableTile_st {s : State} {P : Addr} {w b i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hb : 8 * b + 8 ≤ w) (hi : i < 4) :
    InRegions s.wr (off P (slot w Crt.aT + 64 * b + 16 * i)) 16 := by
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  exact hc.good.scr.region (by omega) (by decide)

theorem tile_ok {s : State} {P : Addr} {w b v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1)
    (hd : slot w Crt.aT + 64 * b + 64 ≤ 2 ^ 64)
    (hld : ∀ j < 32, ∀ i < 4, InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 64 * b + 8 * (w + 2) * j + 16 * i)) 16)
    (hw : ∀ i < 4, InRegions s.wr (off P (slot w Crt.aT + 64 * b + 16 * i)) 16) :
    WP isa tile s fun t =>
      Keep [.x16,.x3,.x14] s t ∧ Outside P (slot w Crt.aT + 64 * b) 64 s.mem t.mem ∧
      t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧
      ∀ j < 64, t.mem (off P (slot w Crt.aT + 64 * b + j)) =
        s.mem (off P (slot w 8 + 64 * b + 8 * (w + 2) * v + j)) := by
  unfold tile
  apply WP.seq
  refine WP.mono (startScan_ok hc ht hp h22 h24) fun u ⟨hu,h0,hm,ku⟩ => ?_
  refine WP.mono (scan_store_ok hv
    (by rw [ku.gpr .x6 (by decide)]; exact hs) hu h0
    (by rw [ku.gpr .x17 (by decide)]; exact hp) hd
    (fun j hj i hi => by rw [ku.rd,ku.wr]; exact hld j hj i hi)
    (fun i hi => by rw [ku.wr]; exact hw i hi)) fun t ⟨kt,ho,h22',h24',hb⟩ => ?_
  exact ⟨(ku.trans kt).mono (by decide), hm ▸ ho, h22', h24', hm ▸ hb⟩

theorem tileAdvance_ok (s : State) :
    WP isa (.block [.addImm .x .x17 .x17 64, .subImm .x .x13 .x13 1]) s fun t =>
      (t.gpr .x17 = s.gpr .x17 + BitVec.ofNat 64 64 ∧
       t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.v = s.v) ∧
      Keep [.x17,.x13] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector
