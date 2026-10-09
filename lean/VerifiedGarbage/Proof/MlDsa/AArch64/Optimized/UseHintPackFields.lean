import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackEncode
import VerifiedGarbage.Spec.MlDsa.UseHintPack

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open HighPack

def fields (g : Nat) (m : Mem) (h a : Addr) : Vector Nat 256 :=
  Vector.ofFn fun i=>(value g (coeffAt m a i.val) (coeffAt m h i.val)).toNat

def packed (g : Nat) (m : Mem) (h a : Addr) : List Byte :=
  simpleBitPack (fields g m h a) ((q-1)/(2*g)-1)

 theorem fields_bound {g : Nat} (hg : IsG g) {m : Mem} {h a : Addr} (ha : Reduced m a)
    (i : Nat) (hi : i<256) : (fields g m h a)[i]'hi<2^packWidth g := by
  simp only [fields,Vector.getElem_ofFn]
  have hv := value_lt hg (h:=coeffAt m h i) (ha i hi)
  have hm : hbM g≤2^packWidth g := by rcases hg with rfl|rfl <;> decide
  exact Nat.lt_of_lt_of_le hv hm

 theorem packed_fields_byte {g : Nat} (hg : IsG g) {s : State} {m : Mem} {h a : Addr}
    (ha : Reduced m a) (hc : PackConstants s) {block i : Nat} (hb : block<16)
    (hi : i<2*packWidth g)
    (hv : ∀j<4,∀e<4,vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=value g
      (vword (m.read ((a+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)
      (vword (m.read ((h+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)) :
    vbyte (packedVector (packWidth g) s) i=(packed g m h a)[2*packWidth g*block+i]! := by
  apply packedVector_fields hg (fields g m h a) (fields_bound hg ha) hc hb hi
  intro j hj e he
  rw [hv j hj e he,VG.AArch64.vword_read16 _ _ he,VG.AArch64.vword_read16 _ _ he,
    Offset.add_add,Offset.add_add,Offset.add_add,Offset.add_add]
  simp only [fields,Vector.getElem_ofFn,coeffAt]
  rw [show 64*block+(16*j+4*e)=4*(16*block+4*j+e) by omega]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
