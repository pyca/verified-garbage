module

public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Decoded lanes implement ByteDecode12 for arbitrary input bytes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem


theorem even_nat (s : State) {g : Nat} (hg : g<128) :
    (Decode12.G s (2*g)).toNat =
      (Decode12.byte s (3*g)+Decode12.byte s (3*g+1)%16*256)%3329 := by
  have hq : q=3329 := rfl
  have h0 : Decode12.byte s (3*g)<256 := byte_lt _
  rw [Decode12.G_even s hg,BitVec.toNat_ofNat,condSub_eq (by omega)]
  have := Nat.mod_lt (Decode12.byte s (3*g)+Decode12.byte s (3*g+1)%16*256) (show 0<q by decide)
  rw [hq] at *
  omega

theorem odd_nat (s : State) {g : Nat} (hg : g<128) :
    (Decode12.G s (2*g+1)).toNat =
      (Decode12.byte s (3*g+1)/16+Decode12.byte s (3*g+2)*16)%3329 := by
  have hq : q=3329 := rfl
  have h1 : Decode12.byte s (3*g+1)<256 := byte_lt _
  have h2 : Decode12.byte s (3*g+2)<256 := byte_lt _
  rw [Decode12.G_odd s hg,BitVec.toNat_ofNat,condSub_eq (by omega)]
  have := Nat.mod_lt (Decode12.byte s (3*g+1)/16+Decode12.byte s (3*g+2)*16) (show 0<q by decide)
  rw [hq] at *
  omega

theorem dec_low_spec (s : State) {k : Nat} (hk : k<32) {x : BitVec 128}
    (hx : ∀ j<12, (vbyte x j).toNat = Decode12.byte s (12*k+j)) :
    Lanes (reduced (low x)) (fun e => (Decode12.G s (8*k+2*e)).toNat) := by
  refine (reduced_lanes (low_lanes x) (fun e _ => by omega)).congr ?_
  intro e he
  rw [hx _ (by omega),hx _ (by omega),hx _ (by omega),
    show 8*k+2*e=2*(4*k+e) by omega,even_nat s (by omega)]
  rw [show 3*(4*k+e)=12*k+3*e by omega]
  simp only [Nat.add_assoc]
  have h0 : Decode12.byte s (12*k+3*e)<256 := byte_lt _
  have h1 : Decode12.byte s (12*k+(3*e+1))<256 := byte_lt _
  congr 1
  omega

theorem dec_high_spec (s : State) {k : Nat} (hk : k<32) {x : BitVec 128}
    (hx : ∀ j<12, (vbyte x j).toNat = Decode12.byte s (12*k+j)) :
    Lanes (reduced (high x)) (fun e => (Decode12.G s (8*k+(2*e+1))).toNat) := by
  have hf : ∀ e<4,
      ((vbyte x (3*e)).toNat+256*(vbyte x (3*e+1)).toNat+65536*(vbyte x (3*e+2)).toNat)/4096 < 6658 := by
    intro e _
    have := (vbyte x (3*e)).isLt
    have := (vbyte x (3*e+1)).isLt
    have := (vbyte x (3*e+2)).isLt
    omega
  refine (reduced_lanes (high_lanes x) hf).congr ?_
  intro e he
  rw [hx _ (by omega),hx _ (by omega),hx _ (by omega),
    show 8*k+(2*e+1)=2*(4*k+e)+1 by omega,odd_nat s (by omega)]
  rw [show 3*(4*k+e)=12*k+3*e by omega]
  simp only [Nat.add_assoc]
  have h0 : Decode12.byte s (12*k+3*e)<256 := byte_lt _
  have h1 : Decode12.byte s (12*k+(3*e+1))<256 := byte_lt _
  congr 1
  omega

end VG.Proof.MlKem.AArch64.Codec16
