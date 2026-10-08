import VerifiedGarbage.Proof.P256.EcdhJac.BuildInit

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

structure BuildInv (base : Addr) (P : Point C) (k m : Nat) (s : State) : Prop where
  fixed : Fixed base P k s
  table : TblOk base P m s
  selected : JPt base s selectedSlot (mul m P)
  counter : s.gpr .x19=BitVec.ofNat 64 m

structure CoZInv (base : Addr) (P : Point C) (k m : Nat) (s : State) : Prop where
  inv : BuildInv base P k m s
  lt : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p
  d : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P

theorem table_keep {base : Addr} {P : Point C} {n : Nat} {s t : State}
    (h : TblOk base P n s) (hn : n≤16) (hk : Frame base work s t) : TblOk base P n t := by
  intro a ha han
  apply (h a ha han).congr
  intro i hi
  exact hk.unch.wordsVal (by
    have hh : ∀a∈List.range 17,1≤a→∀i<5,∀w∈work,entrySlot a i+32≤w.1 ∨ w.1+w.2≤entrySlot a i := by decide +kernel
    exact hh a (List.mem_range.mpr (by omega)) ha i hi) (by unfold entrySlot; omega)

theorem table_store {base : Addr} {P : Point C} {m : Nat} {s t : State}
    (h : TblOk base P m s) (hm : m<16)
    (ho : Outside base (2816+160*m) 160 s.mem t.mem) : TblOk base P m t := by
  intro a ha ham
  apply (h a ha ham).congr
  intro i hi
  exact ho.wordsVal (by unfold entrySlot; omega) (by unfold entrySlot; omega)

theorem selected_store {base : Addr} {Q : Point C} {m : Nat} {s t : State}
    (h : JPt base s selectedSlot Q) (hm : 1≤m) (hm16 : m≤16)
    (ho : Outside base (2816+160*(m-1)) 160 s.mem t.mem) : JPt base t selectedSlot Q := by
  apply h.congr
  intro i hi
  apply ho.wordsVal
  · unfold selectedSlot; split <;> omega
  · unfold selectedSlot; split <;> omega

 theorem selected_keeps {base : Addr} {Q : Point C} {s t : State} {rs : List Reg}
    (h : JPt base s selectedSlot Q) (hk : VG.Proof.Ed25519.AArch64.Keeps rs s t) :
    JPt base t selectedSlot Q := h.congr (fun _ _ => by rw [hk.mem])

end VG.Proof.P256.EcdhJac
