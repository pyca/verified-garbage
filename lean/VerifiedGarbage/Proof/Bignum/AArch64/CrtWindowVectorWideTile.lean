module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideScan

import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorClear
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! One complete 128-byte selection tile: its start, all rows and stores. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accsWide innerWide)

def wideHead : List Instr :=
  [ldh .x16 (sArr Crt.aT), .sub .x .x16 .x17 .x16,
   ldh .x3 Crt.sTab, .add .x .x16 .x16 .x3, movi .x14 32]

theorem wideHead_ok {s : State} {P : Addr} {w b : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 128 * b)) :
    WP isa (.block wideHead) s fun t =>
      (t.gpr .x16 = off P (slot w 8 + 128 * b) ∧ t.gpr .x14 = BitVec.ofNat 64 32 ∧
       t.v = s.v ∧ t.mem = s.mem) ∧ Keep [.x16,.x3,.x14] s t := by
  have hp' : off P (slot w Crt.aT + 128 * b) - off P (slot w Crt.aT) =
      BitVec.ofNat 64 (128 * b) := by
    rw [off, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.add_sub_cancel_left _ _
  refine WP.keep _ ?_ rfl rfl rfl
  brun [wideHead, hc.good.x0, hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hdr_enc (show Crt.sTab < 32 by decide), hc.ld (i := sArr Crt.aT) (by decide),
    hc.ld (i := Crt.sTab) (by decide), hc.good.hdr.harr Crt.aT (by decide), ht, hp, hp',
    RegUpd.v_write]
  exact BitVec.add_comm _ _ |>.trans (off_add P (slot w 8) (128 * b))

theorem startWide_ok {s : State} {P : Addr} {w b v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 128 * b)) :
    WP isa (.block (wideHead ++ accsWide.map fun r => .vop (.movi0 r))) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 32 ∧
      WScanInv t (off P (slot w 8 + 128 * b)) (8 * (w + 2)) v 0 t ∧
      t.mem = s.mem ∧ Keep [.x16,.x3,.x14] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (wideHead_ok hc ht hp) fun u ⟨⟨h16,h14,_,hm⟩, ku⟩ => ?_
  refine WP.mono (clearVectors_ok accsWide u) fun t ⟨hz, kt⟩ => ?_
  have keep : Keep [] u t := ⟨fun r _ => congrFun kt.gpr r, kt.rd, kt.wr, kt.sp,
    fun r hr => congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (kt.v r ((by decide : ∀ r ∈ preservedV, r ∉ accsWide) r hr))⟩
  refine ⟨by rw [kt.gpr, h14], ⟨rfl, Keep.refl _ _, ?_, ?_⟩,
    kt.mem.trans hm, (ku.trans keep).mono (by decide)⟩
  · simpa only [Nat.mul_zero, BitVec.add_zero, kt.gpr] using h16
  · intro i hi
    simpa only [Nat.not_lt_zero, ite_false] using
      hz (acc i) ((by decide : ∀ i < 8, acc i ∈ accsWide) i hi)

theorem wscan_store_ok {s : State} {B : Addr} {base stride dst v : Nat}
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v)) (h7 : s.gpr .x7 = BitVec.allOnes 64)
    (h8 : s.gpr .x8 = 0)
    (hc : s.gpr .x14 = BitVec.ofNat 64 32)
    (h0 : WScanInv s (off B base) stride v 0 s)
    (hp : s.gpr .x17 = off B dst) (hd : dst + 128 ≤ 2 ^ 64)
    (hld : ∀ j < 32, ∀ i < 8,
      InRegions (s.rd ++ s.wr) (off B (base + stride * j + 16 * i)) 16)
    (hw : ∀ i < 8, InRegions s.wr (off B (dst + 16 * i)) 16) :
    WP isa (.seq (countLoop .x14 innerWide) (.block (stores 8))) s fun t =>
      Keep [.x9, .x14, .x16] s t ∧ Outside B dst 128 s.mem t.mem ∧
      ∀ j < 128, t.mem (off B (dst + j)) =
        s.mem (off B (base + stride * v + j)) := by
  apply WP.seq
  refine WP.mono (wscan_ok hv hs h5 h7 h8 hc h0 (fun j hj i hi => by
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc] using hld j hj i hi))
    fun u hu => ?_
  refine WP.mono (stores_ok 8 (src := base + stride * v) (by decide)
    (by rw [hu.keep.gpr .x17 (by decide)]; exact hp) hd
    (fun i hi => by
      simp only [hu.value i hi, hv, ite_true, hu.mem]
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc])
    (fun i hi => by rw [hu.keep.wr]; exact hw i hi)) fun t ht => ?_
  refine ⟨(hu.keep.trans ht.keep).mono (by decide), ?_, ?_⟩
  · simpa only [hu.mem] using ht.frame
  · simpa only [hu.mem] using ht.bytes

def wtile : Prog isa := .seq (.block (wideHead ++ accsWide.map fun r => .vop (.movi0 r)))
  (.seq (countLoop .x14 innerWide) (.block (stores 8)))

theorem wtile_ld {s : State} {P : Addr} {w b j i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hb : 16 * b + 16 ≤ w) (hj : j < 32) (hi : i < 8) :
    InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 128 * b + 8 * (w + 2) * j + 16 * i)) 16 := by
  have he : slot w 8 + 8 * (w + 2) * j = slot w (8 + j) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm j, Nat.add_assoc]
  have hE := VG.Proof.Bignum.CrtWindowFive.ent32_le w hj
  obtain ⟨r, hr, hR⟩ := hc.scrT.region
    (d := slot w 8 + 128 * b + 8 * (w + 2) * j + 16 * i) (n := 16)
    (by omega) (by decide)
  exact ⟨r, List.mem_append_right _ hr, hR⟩

theorem wtile_st {s : State} {P : Addr} {w b i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hb : 16 * b + 16 ≤ w) (hi : i < 8) :
    InRegions s.wr (off P (slot w Crt.aT + 128 * b + 16 * i)) 16 := by
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  exact hc.good.scr.region (by omega) (by decide)

theorem wtile_ok {s : State} {P : Addr} {w b v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 128 * b))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)))
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v)) (h7 : s.gpr .x7 = BitVec.allOnes 64)
    (h8 : s.gpr .x8 = 0)
    (hd : slot w Crt.aT + 128 * b + 128 ≤ 2 ^ 64)
    (hld : ∀ j < 32, ∀ i < 8, InRegions (s.rd ++ s.wr)
      (off P (slot w 8 + 128 * b + 8 * (w + 2) * j + 16 * i)) 16)
    (hw : ∀ i < 8, InRegions s.wr (off P (slot w Crt.aT + 128 * b + 16 * i)) 16) :
    WP isa wtile s fun t =>
      Keep [.x16,.x3,.x14,.x9] s t ∧ Outside P (slot w Crt.aT + 128 * b) 128 s.mem t.mem ∧
      ∀ j < 128, t.mem (off P (slot w Crt.aT + 128 * b + j)) =
        s.mem (off P (slot w 8 + 128 * b + 8 * (w + 2) * v + j)) := by
  unfold wtile
  apply WP.seq
  refine WP.mono (startWide_ok (v := v) hc ht hp) fun u ⟨hu,h0,hm,ku⟩ => ?_
  refine WP.mono (wscan_store_ok hv
    (by rw [ku.gpr .x6 (by decide)]; exact hs)
    (by rw [ku.gpr .x5 (by decide)]; exact h5)
    (by rw [ku.gpr .x7 (by decide)]; exact h7)
    (by rw [ku.gpr .x8 (by decide)]; exact h8) hu h0
    (by rw [ku.gpr .x17 (by decide)]; exact hp) hd
    (fun j hj i hi => by rw [ku.rd,ku.wr]; exact hld j hj i hi)
    (fun i hi => by rw [ku.wr]; exact hw i hi)) fun t ⟨kt,ho,hb⟩ => ?_
  exact ⟨(ku.trans kt).mono (by decide), hm ▸ ho, hm ▸ hb⟩

theorem wtileAdvance_ok (s : State) :
    WP isa (.block [.addImm .x .x17 .x17 128, .subImm .x .x13 .x13 1]) s fun t =>
      (t.gpr .x17 = s.gpr .x17 + BitVec.ofNat 64 128 ∧
       t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.v = s.v) ∧
      Keep [.x17,.x13] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector
