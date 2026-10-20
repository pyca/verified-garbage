module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arith
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Spec.Sha3 VG.Proof.Sha3

theorem absorbWord_state (m : Mem) (p a : Addr) {j : Nat} (hj : j+8≤200) :
 stateAt (m.writeW (p+BitVec.ofNat 64 j)
   (m.readW a 64 ^^^ m.readW (p+BitVec.ofNat 64 j) 64)) p =
 xorAt (stateAt m p) j (bytesAt m a 8) := by
 apply Proof.Sha3.AArch64.Stream.Absorb.stateAt_write_lane hj (bytesAt_length _ _ _)
 intro d hd
 rw [BitVec.extractLsb'_xor,Mem.readW,Mem.readW,BitVec.setWidth_eq,BitVec.setWidth_eq,
   Mem.extractLsb'_read _ _ (show d<64/8 by omega),
   Mem.extractLsb'_read _ _ (show d<64/8 by omega),BitVec.xor_comm,
   BitVec.add_assoc,←BitVec.ofNat_add]
 congr 1
 simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hd,
   Option.map_some,Option.getD_some]

theorem absorbByte_state (m : Mem) (p a : Addr) {j : Nat} (hj : j<200) :
 stateAt (m.writeW (p+BitVec.ofNat 64 j) (m a ^^^ m (p+BitVec.ofNat 64 j))) p =
 xorByte (stateAt m p) j (m a) := by
 apply stateAt_xorByte hj
 · rw [writeW8_self,BitVec.xor_comm]
 · intro i hi hij
   exact writeW8_other _ _ (Proof.Sha3.ne_of_lt200 hi hj hij)

theorem squeezeWord_bytes (m : Mem) (a p : Addr) :
 bytesAt (m.writeW p (m.readW a 64)) p 8 = bytesAt m a 8 := by
 apply List.ext_getElem
 · simp only [bytesAt_length]
 · intro i hi hj
   have hi' : i<8 := by simpa only [bytesAt_length] using hi
   simp only [bytesAt,List.getElem_map,List.getElem_range]
   rw [writeW64_byte _ _ _ hi',Mem.readW,BitVec.setWidth_eq,
     Mem.extractLsb'_read _ _ (show i<64/8 from hi')]

/-- Aligned chunks use the existing sponge invariant, including permutation
exactly when the rate boundary is reached. -/
theorem absorbWord_rep {m : Mem} {p a : Addr} {rate : Nat} {msg : List Byte}
 (hr : 0<rate) (hr' : rate≤200) (hfit : msg.length%rate+8≤rate)
 (hm : stateAt m p=Rep rate msg) :
 Rep rate (msg++bytesAt m a 8) =
   let A := stateAt (m.writeW (p+BitVec.ofNat 64 (msg.length%rate))
     (m.readW a 64 ^^^ m.readW (p+BitVec.ofNat 64 (msg.length%rate)) 64)) p
   if msg.length%rate+8=rate then keccakF A else A := by
 rw [rep_append hr hr' msg _ (by rw [bytesAt_length]; decide)
   (by rw [bytesAt_length]; exact hfit),bytesAt_length]
 dsimp only
 rw [absorbWord_state m p a (by omega),hm]

end VG.Proof.MlKem.AArch64.FixedHash
