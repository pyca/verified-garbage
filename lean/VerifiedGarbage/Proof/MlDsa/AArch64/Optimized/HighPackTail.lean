import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackShuffle
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTailStore

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def tailGather : List Instr :=
  [.vop (.perm .uzp1 .b16 .v4 .v0 .v1), .vop (.perm .uzp1 .b16 .v5 .v2 .v3),
   .vop (.perm .uzp1 .b16 .v4 .v4 .v4), .vop (.perm .uzp1 .b16 .v5 .v5 .v5),
   .vop (.perm .zip1 .d2 .v6 .v4 .v5), .vop (.perm .uzp1 .b16 .v4 .v6 .v6),
   .vop (.perm .uzp2 .b16 .v5 .v6 .v6)]

/-- Gather the sixteen coefficient bytes and separate even and odd positions. -/
theorem tailGather_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v4,.v5,.v6] s t →
      t.v .v4 = VPermOp.eval .uzp1 .b16
        (gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3))
        (gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3)) →
      t.v .v5 = VPermOp.eval .uzp2 .b16
        (gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3))
        (gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (tailGather ++ rest)) s Q := by
  refine wp_vop (d := .v4) rfl fun s1 h1 => wp_vop (d := .v5) rfl fun s2 h2 =>
    wp_vop (d := .v4) rfl fun s3 h3 => wp_vop (d := .v5) rfl fun s4 h4 =>
    wp_vop (d := .v6) rfl fun s5 h5 => wp_vop (d := .v4) rfl fun s6 h6 =>
    wp_vop (d := .v5) rfl fun t h7 => ?_
  have h := (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg
  have e4 : s3.v .v4 = gatherBytes (s.v .v0) (s.v .v1) := by
    rw [h3.v, h2.get .v4, h1.v]; rfl
  have e5 : s4.v .v5 = gatherBytes (s.v .v2) (s.v .v3) := by
    rw [h4.v, h3.get .v5, h2.v, h1.get .v2, h1.get .v3]; rfl
  have e6 : s5.v .v6 = gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3) := by
    rw [h5.v, h4.get .v4, e4, e5]; rfl
  refine k t (h.mono (by decide)) ?_ ?_
  · rw [h7.get .v4, h6.v, e6]
  · rw [h7.v, h6.get .v6, e6]

def byteShift4 (x : BitVec 128) : BitVec 128 :=
  VArr.b16.map2 (fun w _ y => VShiftOp.eval .shl 4 w 0 y) x x

def pack4Vector (even odd : BitVec 128) : BitVec 128 := even ||| byteShift4 odd

/-- Combine adjacent four-bit values without touching memory or scalar registers. -/
theorem pack4Vector_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v4,.v5] s t → t.v .v4 = pack4Vector (s.v .v4) (s.v .v5) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.vop (.shift .shl .b16 .v5 .v5 4),
      .vop (.logic .orr .v4 .v4 .v5)] : List Instr) ++ rest)) s Q := by
  refine wp_vop (d := .v5) rfl fun u hu => wp_vop (d := .v4) rfl fun t ht => ?_
  refine k t ((hu.chg.trans ht.chg).mono (by decide)) ?_
  rw [ht.v, hu.get .v4, hu.v]
  rfl

def wordShift (n : Nat) (x : BitVec 128) : BitVec 128 :=
  VArr.s4.map2 (fun w _ y => VShiftOp.eval .shl n w 0 y) x x

def tableBytes (x indices : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => if (vbyte indices i).toNat < 16 then vbyte x (vbyte indices i).toNat else 0

def pack6Vector (even odd zero idx24 idx25 idx29 : BitVec 128) : BitVec 128 :=
  let e := VPermOp.eval .zip1 .b16 even zero
  let o := VPermOp.eval .zip1 .b16 odd zero
  let pairs := e ||| wordShift 6 o
  tableBytes (tableBytes pairs idx24 ||| wordShift 12 (tableBytes pairs idx25)) idx29

/-- Six-bit packing joins pairs into 12-bit values, then compacts four-value groups. -/
theorem pack6Vector_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v4,.v5,.v6] s t →
      t.v .v4 = pack6Vector (s.v .v4) (s.v .v5) (s.v .v28) (s.v .v24) (s.v .v25) (s.v .v29) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([
      .vop (.perm .zip1 .b16 .v4 .v4 .v28), .vop (.perm .zip1 .b16 .v5 .v5 .v28),
      .vop (.shift .shl .s4 .v5 .v5 6), .vop (.logic .orr .v4 .v4 .v5),
      .vop (.tbl .v5 .v4 .v24), .vop (.tbl .v6 .v4 .v25),
      .vop (.shift .shl .s4 .v6 .v6 12), .vop (.logic .orr .v5 .v5 .v6),
      .vop (.tbl .v4 .v5 .v29)] : List Instr) ++ rest)) s Q := by
  refine wp_vop (d := .v4) rfl fun s1 h1 => wp_vop (d := .v5) rfl fun s2 h2 =>
    wp_vop (d := .v5) rfl fun s3 h3 => wp_vop (d := .v4) rfl fun s4 h4 =>
    wp_vop (d := .v5) rfl fun s5 h5 => wp_vop (d := .v6) rfl fun s6 h6 =>
    wp_vop (d := .v6) rfl fun s7 h7 => wp_vop (d := .v5) rfl fun s8 h8 =>
    wp_vop (d := .v4) rfl fun t h9 => ?_
  have h := (((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg).trans h9.chg
  refine k t (h.mono (by decide)) ?_
  have e2 : s2.v .v5 = VPermOp.eval .zip1 .b16 (s.v .v5) (s.v .v28) := by
    rw [h2.v, h1.get .v5, h1.get .v28]
  have e4 : s4.v .v4 = VPermOp.eval .zip1 .b16 (s.v .v4) (s.v .v28) |||
      wordShift 6 (VPermOp.eval .zip1 .b16 (s.v .v5) (s.v .v28)) := by
    rw [h4.v, h3.get .v4, h2.get .v4, h1.v, h3.v, e2]; rfl
  rw [h9.v, h8.v, h7.get .v5, h6.get .v5, h5.v, e4,
    h4.get .v24, h3.get .v24, h2.get .v24, h1.get .v24,
    h7.v, h6.v, h5.get .v4, e4, h5.get .v25, h4.get .v25,
    h3.get .v25, h2.get .v25, h1.get .v25,
    h8.get .v29, h7.get .v29, h6.get .v29, h5.get .v29, h4.get .v29,
    h3.get .v29, h2.get .v29, h1.get .v29]
  rfl

def gathered (s : State) : BitVec 128 := gatherSixteen (s.v .v0) (s.v .v1) (s.v .v2) (s.v .v3)
def packed4 (s : State) : BitVec 128 := pack4Vector
  (VPermOp.eval .uzp1 .b16 (gathered s) (gathered s))
  (VPermOp.eval .uzp2 .b16 (gathered s) (gathered s))
def packed6 (s : State) : BitVec 128 := pack6Vector
  (VPermOp.eval .uzp1 .b16 (gathered s) (gathered s))
  (VPermOp.eval .uzp2 .b16 (gathered s) (gathered s)) (s.v .v28) (s.v .v24) (s.v .v25) (s.v .v29)

open VG.Proof.MlKem.AArch64 (Keep)

theorem packTail4_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : InRegions s.wr (s.gpr .x1) 8)
    (k : ∀ t, Keep [.x9] s t → (∀ r, r ∉ [.v4,.v5,.v6] → t.v r = s.v r) →
      t.mem = s.mem.writeW (s.gpr .x1) ((packed4 s).extractLsb' 0 64) →
      WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.HighPack.packTail 4 ++ rest)) s Q := by
  change WP isa (.block (tailGather ++ _)) s Q
  refine tailGather_ok fun u hu he ho => pack4Vector_ok fun v hv he4 => ?_
  have ev : v.v .v4 = packed4 s := by rw [he4, he, ho]; rfl
  refine storeEight_ok (by rw [hv.wr, hu.wr, hv.gpr, hu.gpr]; exact hw) fun t ht htv hm => ?_
  refine k t (((hu.keep.trans hv.keep).trans ht).mono (by decide)) ?_ ?_
  · intro r hr
    rw [htv, (hv.mono (rs' := [.v4,.v5,.v6]) (by decide)).get r hr, hu.get r hr]
  · rw [hm, hv.mem, hu.mem, hv.gpr, hu.gpr, ev]

theorem packTail6_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : InRegions s.wr (s.gpr .x1 + 8) 4)
    (k : ∀ t, Keep [.x9] s t → (∀ r, r ∉ [.v4,.v5,.v6] → t.v r = s.v r) →
      t.mem = (s.mem.writeW (s.gpr .x1) ((packed6 s).extractLsb' 0 64)).writeW
        (s.gpr .x1 + 8) ((packed6 s).extractLsb' 64 32) →
      WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.HighPack.packTail 6 ++ rest)) s Q := by
  change WP isa (.block (tailGather ++ _)) s Q
  refine tailGather_ok fun u hu he ho => pack6Vector_ok fun v hv he6 => ?_
  have ev : v.v .v4 = packed6 s := by
    rw [he6, he, ho, hu.get .v28, hu.get .v24, hu.get .v25, hu.get .v29]; rfl
  refine storeEight_ok (by rw [hv.wr, hu.wr, hv.gpr, hu.gpr]; exact hw8) fun a ha hav ham => ?_
  refine storeFour_ok (by rw [ha.wr, hv.wr, hu.wr, ha.get .x1, hv.gpr, hu.gpr]; exact hw4) fun t ht htv hm => ?_
  refine k t ((((hu.keep.trans hv.keep).trans ha).trans ht).mono (by decide)) ?_ ?_
  · intro r hr
    rw [htv, hav, hv.get r hr, hu.get r hr]
  · rw [hm, ham, hav, ev, hv.mem, hu.mem, ha.get .x1, hv.gpr, hu.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
