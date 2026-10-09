import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBankField

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

def dotBankValues (s : State) (count : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => ofVWords
    (dotResult s count (16*j.val) 0) (dotResult s count (16*j.val) 1)
    (dotResult s count (16*j.val) 2) (dotResult s count (16*j.val) 3)

theorem dotBankValues_word (s : State) (count : Nat) (j : Fin 8) {e : Nat} (he : e<4) :
    vword (dotBankValues s count)[j.val] e=dotResult s count (16*j.val) e := by
  simp only [dotBankValues,Vector.getElem_ofFn]
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem dotInput_offset {s : State} {r : Reg} {a : Addr} {u j k e : Nat}
    (ha : s.gpr r=a+BitVec.ofNat 64 (128*u)) (he : e<4) :
    dotInput s r (16*j) k e=coeffAt s.mem (a+BitVec.ofNat 64 (1024*k)) (32*u+4*j+e) := by
  unfold dotInput
  rw [ha,vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add]
  congr 3 <;> omega

theorem dotBankValues_bound {s : State} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (hf : ∀k<count,PosPolyIs s.mem (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs s.mem (b+BitVec.ofNat 64 (1024*k)) (g k))
    (j : Fin 8) {e : Nat} (he : e<4) :
    -(q : Int)≤(vword (dotBankValues s count)[j.val] e).toInt ∧
      (vword (dotBankValues s count)[j.val] e).toInt≤(q : Int) := by
  rw [dotBankValues_word s count j he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  have hbnd := centeredDot_bound
    (fun k => dotInput s .x13 (16*j.val) k e) (fun k => dotInput s .x14 (16*j.val) k e) hc
    (fun k hkc => by rw [dotInput_offset ha he]; exact (hf k hkc).bound _ hk)
    (fun k hkc => by rw [dotInput_offset hb he]; exact (hg k hkc).bound _ hk)
  exact ⟨hbnd.1,Int.le_of_lt hbnd.2⟩

theorem dotBankValues_field {s : State} {a b : Addr} {f g : Nat → Poly} {u count : Nat}
    (hu : u<8) (hc : count≤7)
    (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u))
    (hf : ∀k<count,PosPolyIs s.mem (a+BitVec.ofNat 64 (1024*k)) (f k))
    (hg : ∀k<count,PosPolyIs s.mem (b+BitVec.ofNat 64 (1024*k)) (g k))
    (j : Fin 8) {e : Nat} (he : e<4) :
    ofInt (vword (dotBankValues s count)[j.val] e).toInt =
      (Representation.encode true (dotPoly f g count))[32*u+4*j.val+e]! := by
  rw [dotBankValues_word s count j he]
  have hk : 32*u+4*j.val+e<n := by change 32*u+4*j.val+e<256; omega
  refine centeredDot_field _ _ f g hc ?_ ?_ hk ?_ ?_
  · intro k hkc; rw [dotInput_offset ha he]; exact (hf k hkc).bound _ hk
  · intro k hkc; rw [dotInput_offset hb he]; exact (hg k hkc).bound _ hk
  · intro k hkc
    rw [dotInput_offset ha he,ofInt_nat_eq,← polyAt_get _ _ hk,(hf k hkc).value]
  · intro k hkc
    rw [dotInput_offset hb he,ofInt_nat_eq,← polyAt_get _ _ hk,(hg k hkc).value]

end VG.Proof.MlDsa.AArch64.Optimized
