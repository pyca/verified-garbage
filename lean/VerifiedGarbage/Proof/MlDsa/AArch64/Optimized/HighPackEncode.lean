import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackDigits
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits take_drop_eq)

private theorem getD_bound {L : List Nat} {d i : Nat}
    (h : ∀ a∈L, a<2^d) (hi : i<L.length) : L.getD i 0<2^d := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact h _ (List.getElem_mem hi)

/-- A four-bit packing byte is exactly one adjacent pair in the bit-level encoding. -/
theorem encode4_byte {L : List Nat} (hlen : L.length=256) (hbound : ∀ a∈L,a<16)
    {s : State} {block i : Nat} (hb : block<16) (hi : i<8)
    (hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8 (L.getD (16*block+j) 0)) :
    vbyte (packed4 s) i=(bitsToBytes (fieldBits 4 L))[8*block+i]! := by
  have h0 : L.getD (16*block+2*i) 0<16 := getD_bound (d := 4) (i := 16*block+2*i) hbound (by rw [hlen]; omega)
  have h1 : L.getD (16*block+(2*i+1)) 0<16 := getD_bound (d := 4) (i := 16*block+(2*i+1)) hbound (by rw [hlen]; omega)
  have n0 : (BitVec.ofNat 8 (L.getD (16*block+2*i) 0)).toNat=L.getD (16*block+2*i) 0 := by
    rw [BitVec.toNat_ofNat]; omega
  have n1 : (BitVec.ofNat 8 (L.getD (16*block+(2*i+1)) 0)).toNat=L.getD (16*block+(2*i+1)) 0 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [packed4_byte s hi,hv (2*i) (by omega),hv (2*i+1) (by omega),
    nibble_digits _ _ (by rw [n0]; exact h0) (by rw [n1]; exact h1),n0,n1]
  have hpack := pack_group (d := 4) (c := 2) (nb := 1) (by decide) (by decide)
    hlen hbound (g := 8*block+i) (t := 0) (by decide) (by omega)
  simp only [Nat.one_mul,Nat.add_zero,Nat.mul_zero,Nat.pow_zero,Nat.div_one] at hpack
  rw [hpack,take_drop_eq _ 0 (by rw [hlen]; omega)]
  simp only [show List.range 2=[0,1] from rfl,List.map_cons,List.map_nil,Nat.add_zero]
  rw [show 2*(8*block+i)=16*block+2*i by omega,
    show 16*block+2*i+1=16*block+(2*i+1) by omega]


/-- A six-bit packing byte agrees with the corresponding four-field group
in the original bit-level encoding. -/
theorem encode6_byte {L : List Nat} (hlen : L.length=256) (hbound : ∀ a∈L,a<64)
    {s : State} {block i : Nat} (hb : block<16) (hi : i<12)
    (hc : PackConstants s)
    (hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8 (L.getD (16*block+j) 0)) :
    vbyte (packed6 s) i=(bitsToBytes (fieldBits 6 L))[12*block+i]! := by
  have bound (k : Nat) (hk : k<4) : L.getD (16*block+(4*(i/3)+k)) 0<64 :=
    getD_bound (d := 6) (i := 16*block+(4*(i/3)+k)) hbound (by rw [hlen]; omega)
  have natv (k : Nat) (hk : k<4) :
      (BitVec.ofNat 8 (L.getD (16*block+(4*(i/3)+k)) 0)).toNat=L.getD (16*block+(4*(i/3)+k)) 0 := by
    rw [BitVec.toNat_ofNat]
    have := bound k hk
    omega
  rw [packed6_byte s hc.zero hc.idx24 hc.idx25 hc.idx29 hi,
    hv (4*(i/3)) (by omega),hv (4*(i/3)+1) (by omega),
    hv (4*(i/3)+2) (by omega),hv (4*(i/3)+3) (by omega)]
  have b0 := bound 0 (by decide)
  have n0 := natv 0 (by decide)
  simp only [Nat.add_zero] at b0 n0
  rw [sixWord_byte_digits _ _ _ _ (by rw [n0]; exact b0)
    (by rw [natv 1 (by decide)]; exact bound 1 (by decide))
    (by rw [natv 2 (by decide)]; exact bound 2 (by decide))
    (by rw [natv 3 (by decide)]; exact bound 3 (by decide)),
    n0,natv 1 (by decide),natv 2 (by decide),natv 3 (by decide)]
  have hpack := pack_group (d := 6) (c := 4) (nb := 3) (by decide) (by decide)
    hlen hbound (g := 4*block+i/3) (t := i%3) (by omega) (by omega)
  rw [show 3*(4*block+i/3)+i%3=12*block+i by omega] at hpack
  rw [hpack,take_drop_eq _ 0 (by rw [hlen]; omega)]
  simp only [show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,Nat.add_zero]
  rw [show 4*(4*block+i/3)=16*block+4*(i/3) by omega,
    show 16*block+4*(i/3)+1=16*block+(4*(i/3)+1) by omega,
    show 16*block+4*(i/3)+2=16*block+(4*(i/3)+2) by omega,
    show 16*block+4*(i/3)+3=16*block+(4*(i/3)+3) by omega]


/-- The selected vector tail encodes exactly the original polynomial's
HighBits at every byte of a sixteen-coefficient block. -/
theorem packedVector_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {s : State} {m : Mem} {a : Addr} (hr : Reduced m a) (hc : PackConstants s)
    {block i : Nat} (hb : block<16) (hi : i<2*packWidth g)
    (h : ∀ j<4, ∀ e<4,
      vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=
        highWord g (vword (m.read ((a+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)) :
    vbyte (packedVector (packWidth g) s) i=(highPacked g (polyAt m a))[(2*packWidth g)*block+i]! := by
  have hv : ∀ j<16, vbyte (gathered s) j=BitVec.ofNat 8
      ((highCoefficients g (polyAt m a)).toList.getD (16*block+j) 0) := by
    intro j hj
    have hjn : 16*block+j<n := by change 16*block+j<256; omega
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hjn),Option.getD_some]
    exact gathered_coefficients hg hr hb h hj
  have hlen : (highCoefficients g (polyAt m a)).toList.length=256 := by simp [n]
  have hbound := highCoefficients_bound hg (polyAt m a)
  rw [highPacked,simpleBitPack_eq,packWidth_eq hg]
  rcases hg with rfl | rfl
  · exact encode4_byte hlen hbound hb hi hv
  · exact encode6_byte hlen (fun x hx => hbound x hx) hb hi hc hv

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
