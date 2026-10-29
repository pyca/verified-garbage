module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightTile
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

abbrev headRegs := codeRegs ++ [.x13, .x16, .x17, .x15, .x10]

theorem rowHead_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8)
    (hk : k < 2 ^ 56) (hi : i < k)
    (h8 : s.gpr .x8 = off B (slot (8*k) a+64*i))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (k-i))
    (hv : wv s.mem B (productBase k) (16*k+2) < 2 ^ (64*(16*i))) :
    WP isa (.block (SquareEightRaw.rowHead a)) s fun t =>
      (wv t.mem B (productBase k) (16*k+2) = wv s.mem B (productBase k) (16*k+2) +
        2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 ∧
       t.gpr .x16 = off B (productBase k+64*i) ∧ t.gpr .x17 = off B (slot (8*k) a) ∧
       t.gpr .x15 = BitVec.ofNat 64 i ∧ t.gpr .x10 = 0 ∧
       Outside B (productBase k) (8*(16*k+2)) s.mem t.mem) ∧ Keep headRegs s t := by
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega
  unfold SquareEightRaw.rowHead
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (outputPtr_ok hs h0 hH hZ ha (by omega) h8 true) fun u ⟨⟨hu16, _, hum⟩, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (internal_ok (hs.congr ku.wr) ((ku.gpr _ (by decide)).trans h8) hu16
    ((ku.gpr _ (by decide)).trans h7) (by omega) hP (by omega)
    (by simpa only [hum] using hv)) fun v ⟨hvv, hvo, kv⟩ => ?_
  have huv := ku.trans kv
  have ho : Outside B (productBase k) (8*(16*k+2)) s.mem v.mem := by
    intro x hx
    exact ((hvo.mono (by omega) (by omega)) x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8*k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2*(8*k) = 16*k by omega] using ho)).hdr hH
  have hval : wv v.mem B (productBase k) (16*k+2) = wv s.mem B (productBase k) (16*k+2) +
      2 ^ (64*(16*i))*Square.crossValue s.mem B (slot (8*k) a+64*i) 8 := by
    simpa only [hum] using hvv
  apply WP.block_append
  refine WP.mono (clearPending_ok v) fun v' ⟨⟨hv10, hvm⟩, kc⟩ => ?_
  have kvc := huv.trans kc
  apply WP.block_append
  refine WP.mono (outputPtr_ok (hs.congr kvc.wr) ((kvc.gpr _ (by decide)).trans h0)
    (hvm ▸ hHv) hZ ha (by omega) ((kvc.gpr _ (by decide)).trans h8) false)
    fun b ⟨⟨hb16, hb17, hbm⟩, kb⟩ => ?_
  have kab := kvc.trans kb
  have hbH : Hdr b.mem B (8*k) minv := (hbm.trans hvm) ▸ hHv
  refine WP.mono (rowCount_ok (hs.congr kab.wr) ((kab.gpr _ (by decide)).trans h0)
    hbH hZ hk (by omega) ((kab.gpr _ (by decide)).trans h12))
    fun t ⟨⟨ht15, htm⟩, kt⟩ => ?_
  have hm := htm.trans (hbm.trans hvm)
  refine ⟨⟨?_, (kt.gpr _ (by decide)).trans hb16, (kt.gpr _ (by decide)).trans hb17,
    ht15, (kt.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans hv10), ?_⟩,
    (kab.trans kt).mono (by decide)⟩
  · exact (congrArg (fun m : Mem => wv m B (productBase k) (16*k+2)) hm).trans hval
  · intro x hx
    exact (congrArg (fun m : Mem => m x) hm).trans (ho x hx)

end VG.Proof.Bignum.AArch64.SquareEight
