module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightOffDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTile
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw

/-! ### `Bignum.AArch64.WindowSparseTail`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

open VG.Proof.Bignum.AArch64.SquareEight

abbrev rowTailRegs : List Reg := [.x13, .x16, .x17, .x8, .x12]

theorem rowTail_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8)
    (hk : k < 2 ^ 56) (hi : i < k) (h8 : s.gpr .x8 = off B (slot (8*k) a+64*i)) :
    WP isa (.block (SquareEightRaw.rowTail a)) s fun t =>
      wv t.mem B (productBase k) (16*(i+1)) + 2 ^ (64*(16*i+15))*t.c.toNat =
        wv s.mem B (productBase k) (16*(i+1)) + 2 ^ (64*(16*i+8))*(s.gpr .x10).toNat ∧
      t.gpr .x8 = off B (slot (8*k) a+64*(i+1)) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
      Outside B (productBase k) (8*(16*(i+1))) s.mem t.mem ∧ Keep rowTailRegs s t := by
  have hP : productBase k+8*(16*(i+1)) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [hZ, hi]
  unfold SquareEightRaw.rowTail
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (outputPtr_ok hs h0 hH hZ ha (by omega_using [hk, hi]) h8 true) fun u ⟨⟨hu16, _, hum⟩, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (finishCarry_full (hs.congr ku.wr) hu16 ((ku.gpr _ (by decide)).trans h7)
    hP (by omega_using [])) fun v ⟨hvv, hvo, kv⟩ => ?_
  have huv := ku.trans kv
  have hp := ProductEight.rowEnd_ok ((huv.gpr _ (by decide)).trans h8)
  refine WP.mono (WP.keep [.x8, .x12] (Q := fun t =>
      t.gpr .x8 = off B (slot (8*k) a+64*i+64) ∧ t.gpr .x12 = v.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = v.mem ∧ t.c = v.c)
    (by brun [(huv.gpr .x8 (by decide)).trans h8]) rfl rfl rfl)
    fun t ⟨⟨ht8, ht12, htm, htc⟩, kt⟩ => ?_
  refine ⟨?_, ht8.trans (congrArg (off B) (by omega_using [])),
    ht12.trans (congrArg (· - BitVec.ofNat 64 1) (huv.gpr _ (by decide))), ?_,
    (huv.trans kt).mono (by decide)⟩
  · rw [htm, htc]
    simpa only [hum, ku.gpr .x10 (by decide)] using hvv
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans
      (((hvo.mono (by omega_using []) (by omega_using [])) x hx).trans (congrArg (fun m : Mem => m x) hum))

end VG.Proof.Bignum.AArch64.WindowSparse

end

end

/-! ### `Bignum.AArch64.WindowSparseHead`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.WindowSparseTile`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.WindowSparseHoles`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem holes_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e+128 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSparse.holes) s fun t =>
      word t.mem B e = 0 ∧ word t.mem B (e+120) = 0 ∧
      Outside B e 128 s.mem t.mem ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = (s.mem.writeW (off B e) (0 : BitVec 64)).writeW (off B (e+120)) (0 : BitVec 64))
    ?_ rfl rfl rfl) fun t ⟨hm,kt⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.WindowSparse.holes
    brun [h16,h7,hs.st (show e+8 ≤ Z by omega_using [he]),hs.st (show e+120+8 ≤ Z by omega_using [he])]
  · refine ⟨?_,?_,?_,kt⟩
    · rw [hm,(writeW_outside (s.mem.writeW (off B e) (0 : BitVec 64)) B
        (d := e+120) (0 : BitVec 64) (by omega_using [he, hn])).word (by omega_using []) (by omega_using [he, hn]),word_writeW_self]
    · rw [hm,word_writeW_self]
    · rw [hm]
      exact (writeW_outside s.mem B (0 : BitVec 64) (by omega_using [he, hn])).mono (by omega_using []) (by omega_using []) |>.trans
        ((writeW_outside (s.mem.writeW (off B e) (0 : BitVec 64)) B (d := e+120)
          (0 : BitVec 64) (by omega_using [he, hn])).mono (by omega_using []) (by omega_using []))

end VG.Proof.Bignum.AArch64.WindowSparse

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem zero_top (m : Mem) (B : Addr) (e n : Nat)
    (h : word m B (e+8*n) = 0) : wv m B e (n+1) = wv m B e n := by
  rw [wv,h,show (0 : BitVec 64).toNat = 0 from rfl,Nat.mul_zero,Nat.add_zero]

/-- A tile overwrites all sixteen words, so the previous contents are irrelevant. -/
theorem tile_ok {s : State} {B : Addr} {Z eA eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h16 : s.gpr .x16 = off B eT)
    (h7 : s.gpr .x7 = 0) (hA : eA+64 ≤ Z) (hT : eT+128 ≤ Z)
    (hsep : eA+64 ≤ eT ∨ eT+128 ≤ eA) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSparse.holes ++ SquareEight.code)) s fun t =>
      wv t.mem B eT 16 = Square.crossValue s.mem B eA 8 ∧
      Outside B eT 128 s.mem t.mem ∧ Keep SquareEight.codeRegs s t := by
  have hn := hs.nowrap
  apply WP.block_append
  refine WP.mono (holes_ok hs h16 h7 hT) fun u ⟨hz,hh,ho,ku⟩ => ?_
  refine WP.mono (SquareEight.code_ok (hs.congr ku.wr)
    ((ku.gpr _ (by decide)).trans h8) ((ku.gpr _ (by decide)).trans h16)
    hA (by omega_using [hT]) ((ku.gpr _ (by decide)).trans h7) (by simp [wv,hz]))
    fun t ⟨hv,ht,kt⟩ => ?_
  have high : word t.mem B (eT+120) = 0 := (ht.word (by omega_using []) (by omega_using [hT, hn])).trans hh
  have inp : Square.crossValue u.mem B eA 8 = Square.crossValue s.mem B eA 8 := by
    apply Square.crossValue_congr
    intro j hj
    exact ho.word (by omega_using [hsep, hj]) (by omega_using [hA, hn, hj])
  refine ⟨?_,ho.trans (ht.mono (by omega_using []) (by omega_using [])),(ku.trans kt).mono (by decide)⟩
  exact (zero_top t.mem B eT 15 (by simpa only [show 8*15=120 from rfl] using high)).trans
    (hv.trans inp)

/-- Extending the initialized prefix by one overwritten tile needs no whole-buffer clear. -/
theorem prefix_ok {s : State} {B : Addr} {Z eA eT i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA)
    (h16 : s.gpr .x16 = off B (eT+128*i)) (h7 : s.gpr .x7 = 0)
    (hA : eA+64 ≤ Z) (hT : eT+128*(i+1) ≤ Z)
    (hsep : eA+64 ≤ eT ∨ eT+128*(i+1) ≤ eA) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSparse.holes ++ SquareEight.code)) s fun t =>
      wv t.mem B eT (16*(i+1)) = wv s.mem B eT (16*i) +
        2^(64*(16*i))*Square.crossValue s.mem B eA 8 ∧
      Outside B eT (128*(i+1)) s.mem t.mem ∧ Keep SquareEight.codeRegs s t := by
  have hn := hs.nowrap
  refine WP.mono (tile_ok hs h8 h16 h7 hA (by omega_using [hT]) (by omega_using [hsep])) fun t ⟨hv,ho,kt⟩ => ?_
  refine ⟨?_,ho.mono (by omega_using []) (by omega_using []),kt⟩
  rw [show 16*(i+1) = 16*i+16 by omega_using [],wv_add,
    ho.wv (d := eT) (k := 16*i) (by omega_using []) (by omega_using [hT, hn]),show eT+8*(16*i)=eT+128*i by omega_using [],hv]

end VG.Proof.Bignum.AArch64.WindowSparse

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

open VG.Proof.Bignum.AArch64.SquareEight

abbrev headRegs := codeRegs ++ [.x13, .x16, .x17, .x15, .x10]

theorem rowHead_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8)
    (hk : k < 2 ^ 56) (hi : i < k)
    (h8 : s.gpr .x8 = off B (slot (8*k) a+64*i))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (k-i))
    (hsep : slot (8*k) a+64*k ≤ productBase k ∨ productBase k+8*(16*k+2) ≤ slot (8*k) a) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSparse.rowHead a)) s fun t =>
      (wv t.mem B (productBase k) (16*(i+1)) = wv s.mem B (productBase k) (16*i) +
        2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 ∧
       t.gpr .x16 = off B (productBase k+64*i) ∧ t.gpr .x17 = off B (slot (8*k) a) ∧
       t.gpr .x15 = BitVec.ofNat 64 i ∧ t.gpr .x10 = 0 ∧
       Outside B (productBase k) (128*(i+1)) s.mem t.mem) ∧ Keep headRegs s t := by
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [hZ]
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega_using [hZ, this]
  unfold VG.Impl.Bignum.AArch64.WindowSparse.rowHead
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (outputPtr_ok hs h0 hH hZ ha (by omega_using [hk, hi]) h8 true) fun u ⟨⟨hu16, _, hum⟩, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (prefix_ok (hs.congr ku.wr) ((ku.gpr _ (by decide)).trans h8) hu16
    ((ku.gpr _ (by decide)).trans h7) (by omega_using [hi, hA]) (by omega_using [hi, hP]) (by omega_using [hi, hsep])) fun v ⟨hvv, hvo, kv⟩ => ?_
  have huv := ku.trans kv
  have ho : Outside B (productBase k) (128*(i+1)) s.mem v.mem := by
    intro x hx
    exact ((hvo.mono (by omega_using []) (by omega_using [])) x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hwide : Outside B (productBase k) (8*(16*k+2)) s.mem v.mem := ho.mono (by omega_using []) (by omega_using [hi])
  have hHv : Hdr v.mem B (8*k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2*(8*k) = 16*k by omega_using []] using hwide)).hdr hH
  have hval : wv v.mem B (productBase k) (16*(i+1)) = wv s.mem B (productBase k) (16*i) +
      2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 := by
    simpa only [hum] using hvv
  apply WP.block_append
  refine WP.mono (clearPending_ok v) fun v' ⟨⟨hv10, hvm⟩, kc⟩ => ?_
  have kvc := huv.trans kc
  apply WP.block_append
  refine WP.mono (outputPtr_ok (hs.congr kvc.wr) ((kvc.gpr _ (by decide)).trans h0)
    (hvm ▸ hHv) hZ ha (by omega_using [hk, hi]) ((kvc.gpr _ (by decide)).trans h8) false)
    fun b ⟨⟨hb16, hb17, hbm⟩, kb⟩ => ?_
  have kab := kvc.trans kb
  have hbH : Hdr b.mem B (8*k) minv := (hbm.trans hvm) ▸ hHv
  refine WP.mono (rowCount_ok (hs.congr kab.wr) ((kab.gpr _ (by decide)).trans h0)
    hbH hZ hk (by omega_using [hi]) ((kab.gpr _ (by decide)).trans h12))
    fun t ⟨⟨ht15, htm⟩, kt⟩ => ?_
  have hm := htm.trans (hbm.trans hvm)
  refine ⟨⟨?_, (kt.gpr _ (by decide)).trans hb16, (kt.gpr _ (by decide)).trans hb17,
    ht15, (kt.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans hv10), ?_⟩,
    (kab.trans kt).mono (by decide)⟩
  · exact (congrArg (fun m : Mem => wv m B (productBase k) (16*(i+1))) hm).trans hval
  · intro x hx
    exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)

end VG.Proof.Bignum.AArch64.WindowSparse

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

open VG.Proof.Bignum.AArch64.SquareEight

abbrev rawRegs := ProductEight.rawRegs

structure RowsInv (s : State) (B : Addr) (Z k a i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep rawRegs s t
  ptr : t.gpr .x8 = off B (slot (8*k) a+64*i)
  frame : Outside B (productBase k) (128*i) s.mem t.mem
  value : wv t.mem B (productBase k) (16*i) = Square.crossValue s.mem B (slot (8*k) a) (8*i)

theorem frame_header {s t : State} {B : Addr} {k : Nat} {minv : BitVec 64}
    (ho : Outside B (productBase k) (8*(16*k+2)) s.mem t.mem)
    (hh : Hdr s.mem B (8*k) minv) : Hdr t.mem B (8*k) minv :=
  (Square.scratch_arrays (by simpa only [productBase, show 2*(8*k) = 16*k by omega_arith] using ho)).hdr hh

/-- A full triangular row adds its internal products and every earlier tile,
then proves that the discarded final carry is zero. -/
theorem row_ok {s t : State} {B : Addr} {Z k a i : Nat} {minv : BitVec 64}
    (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8) (hk : k < 2 ^ 56) (hi : i < k)
    (hA : slot (8*k) a+64*k ≤ productBase k ∨ productBase k+8*(16*k+2) ≤ slot (8*k) a)
    (hI : RowsInv s B Z k a i t) (h12 : t.gpr .x12 = BitVec.ofNat 64 (k-i)) :
    WP isa (.seq (.block (VG.Impl.Bignum.AArch64.WindowSparse.rowHead a))
      (.seq (.ite (.nonzero .x .x15) (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block []))
        (.block (SquareEightRaw.rowTail a)))) t fun u =>
      RowsInv s B Z k a (i+1) u ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_arith
  have hAZ : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega_arith
  refine WP.seq (WP.mono (rowHead_ok hI.scr ((hI.keep.gpr _ (by decide)).trans h0)
    ((hI.keep.gpr _ (by decide)).trans h7) (frame_header (hI.frame.mono (by omega_arith) (by omega_arith)) hH) hZ ha hk hi hI.ptr h12 hA)
    fun v ⟨⟨hvv, hv16, hv17, hv15, hv10, hvo⟩, kv⟩ => ?_)
  have ho1 := (hI.frame.mono (by omega_arith) (by omega_arith)).trans hvo
  have k1 := hI.keep.trans kv
  have hv8 := (kv.gpr _ (by decide)).trans hI.ptr
  have hv7 := (k1.gpr _ (by decide)).trans h7
  have hcInput : Square.crossValue t.mem B (slot (8*k) a+64*i) 8 =
      Square.crossValue s.mem B (slot (8*k) a+64*i) 8 := by
    apply Square.crossValue_congr
    intro j hj
    exact hI.frame.word (by omega_arith) (by omega_arith)
  have h1 := hvv
  rw [hI.value, hcInput] at h1
  refine WP.seq (WP.mono (offDiagonal_full (hI.scr.congr kv.wr) hv8 hv7 hv10 hv16 hv17 hv15
    (by omega_arith) (show productBase k+8*(16*(i+1)) ≤ Z by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun v' ⟨hvv', hvo', kv'⟩ => ?_)
  have ho2 := ho1.trans (hvo'.mono (by omega_arith) (by omega_arith))
  have k2 := k1.trans kv'
  have hq := ho1.wv (d := slot (8*k) a+64*i) (k := 8) (by omega_arith) (by omega_arith)
  have hb := ho1.wv (d := slot (8*k) a) (k := 8*i) (by omega_arith) (by omega_arith)
  have h2 := hvv'
  rw [hq, hb] at h2
  refine WP.mono (rowTail_ok (hI.scr.congr (kv'.wr.trans kv.wr))
    ((k2.gpr _ (by decide)).trans h0) ((k2.gpr _ (by decide)).trans h7)
    (frame_header (ho2.mono (by omega_arith) (by omega_arith)) hH) hZ ha hk hi ((kv'.gpr _ (by decide)).trans hv8))
    fun u ⟨huv, hu8, hu12, huo, ku⟩ => ?_
  have hv := row_finish_value h1 h2 huv
  refine ⟨⟨hI.scr.congr (ku.wr.trans (kv'.wr.trans kv.wr)),
    (k2.trans ku).mono (by decide), hu8, ho2.trans (huo.mono (by omega_arith) (by omega_arith)), hv.1⟩, ?_⟩
  exact hu12.trans (congrArg (· - BitVec.ofNat 64 1)
    ((kv'.gpr _ (by decide)).trans (kv.gpr _ (by decide))))

theorem rows_noVec (a : Nat) :
    (VG.Impl.Bignum.AArch64.WindowSparse.rows a).allInstrs (fun i => (vdstOf i).isNone) = true := by rfl

theorem rows_ok {s : State} {B : Addr} {Z k a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot (8*k) a)) (h12 : s.gpr .x12 = BitVec.ofNat 64 k)
    (ha : a < 8) (hk : 0 < k) (hk' : k < 2 ^ 56)
    (hA : slot (8*k) a+64*k ≤ productBase k ∨ productBase k+8*(16*k+2) ≤ slot (8*k) a) :
    WP isa (VG.Impl.Bignum.AArch64.WindowSparse.rows a) s fun t => RowsInv s B Z k a k t ∧ ∀ v, t.v v = s.v v := by
  have hinit : RowsInv s B Z k a 0 s := by
    refine ⟨hs, Keep.refl _ _, h8, Outside.refl _ _ _ _, ?_⟩
    rfl
  have hp : WP isa (VG.Impl.Bignum.AArch64.WindowSparse.rows a) s (RowsInv s B Z k a k) :=
    wp_countdown (by omega_arith) hk (RowsInv s B Z k a)
      (fun i hi t hI hcount => row_ok h0 h7 hH hZ ha hk' hi hA hI hcount) hinit h12
  obtain ⟨tr, t, he, ht⟩ := hp
  refine ⟨tr, t, he, ht, fun v => Exec.vec ?_ he⟩
  have hc := rows_noVec a
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  intro i hi h
  have hn := hc i hi
  rw [h] at hn
  contradiction

end VG.Proof.Bignum.AArch64.WindowSparse
