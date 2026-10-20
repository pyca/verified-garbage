module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Extracting the public rejection mask and table address -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- The low halfword determines the mask and count; the second halfword
included by UMOV does not interfere with either extraction. -/
theorem word_mod {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    (vword x 0).toNat % 65536 = packedCount mask := by
  have h := congrArg BitVec.toNat hx
  rw [← vword_lo x 0, ← BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h
  have hb := packedCount_bound hm
  simpa only [Nat.reducePow, Nat.mod_eq_of_lt (show packedCount mask < 65536 by omega)] using h

theorem word_mask {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    ((vword x 0).setWidth 64 &&& 255).toNat = mask := by
  rw [toNat_and_mask _ _ (k := 8) rfl, BitVec.toNat_setWidth]
  have hw := (vword x 0).isLt
  have hl := word_mod hm hx
  have hp := packedCount_mask hm
  omega

theorem word_count {x : BitVec 128} {mask : Nat} (hm : mask < 256)
    (hx : vhalf x 0 = BitVec.ofNat 16 (packedCount mask)) :
    (((vword x 0).setWidth 64 >>> 8) &&& 15).toNat =
      (Impl.MlKem.AArch64.Rej8.acceptedLanes mask).length := by
  rw [toNat_and_mask _ _ (k := 4) rfl, toNat_lsr, BitVec.toNat_setWidth]
  have hw := (vword x 0).isLt
  have hl := word_mod hm hx
  have hp := packedCount_count hm
  have hn := accepted_length mask
  omega

def indexCode : List Instr :=
 [.umov .w .x6 .v1 0,.movz .x .x7 255 0,.logic .and .x .x7 .x6 .x7,
 .lsl .x .x7 .x7 4,.add .x .x7 .x16 .x7]

/-- The public table address is exactly sixteen times the accepted mask. -/
theorem index_basic (s : State) {mask : Nat} (hm : mask < 256)
    (hx : vhalf (s.v .v1) 0 = BitVec.ofNat 16 (packedCount mask)) :
    WP isa (.block indexCode) s fun t =>
      Only [.x6,.x7] s t ∧
      t.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 ∧
      t.gpr .x7 = s.gpr .x16 + BitVec.ofNat 64 (16*mask) := by
  let a := s.write .w .x6 (vword (s.v .v1) 0)
  have ha : Only [.x6] s a := only_write _ _ _ _
  have h6 : a.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 := by
    rfl
  refine WP.cons (s' := a) rfl ?_
  refine wp_movz fun b hb eb => wp_and fun c hc ec => wp_lsl (by decide) fun d hd ed =>
    wp_add fun t ht et => wp_nil ?_
  have h7 : (c.gpr .x7).toNat=mask := by
    rw [ec,hb.get .x6,h6,eb]
    exact word_mask hm hx
  have hs : d.gpr .x7=BitVec.ofNat 64 (16*mask) := by
    apply BitVec.eq_of_toNat_eq
    rw [ed,toNat_lsl_n (by rw [h7]; omega),h7,BitVec.toNat_ofNat]
    omega
  refine ⟨((((ha.trans hb).trans hc).trans hd).trans ht).mono (by decide), ?_, ?_⟩
  · rw [ht.get .x6,hd.get .x6,hc.get .x6,hb.get .x6,h6]
  · rw [et,hs,hd.get .x16,hc.get .x16,hb.get .x16,ha.get .x16]

theorem index_ok (s : State) {mask : Nat} (hm : mask < 256)
    (hx : vhalf (s.v .v1) 0 = BitVec.ofNat 16 (packedCount mask)) :
    WP isa (.block indexCode) s fun t =>
      Only [.x6,.x7] s t ∧ t.v=s.v ∧
      t.gpr .x6 = (vword (s.v .v1) 0).setWidth 64 ∧
      t.gpr .x7 = s.gpr .x16 + BitVec.ofNat 64 (16*mask) := by
  exact WP.mono (WP.keepV (by rfl : indexCode.all (fun i => !writesV i)=true)
    (index_basic s hm hx)) fun _ ⟨⟨hk,h6,h7⟩,hv⟩ => ⟨hk,hv,h6,h7⟩

end VG.Proof.MlKem.AArch64.Rej8
