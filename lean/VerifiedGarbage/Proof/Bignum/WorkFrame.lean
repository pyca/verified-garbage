module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Workspace writes with an additional private stack footprint

The offsets describe workspace writes as in `Frm`. The extra regions
account for a verified callee's stack. Reads inside the workspace remain
protected when it is disjoint from those extra regions.
-/

@[expose] public section

namespace VG.Proof.Bignum

open VG

def WorkFrame (B : Addr) (rs : List (Nat × Nat)) (extra : List Region) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ extra, ¬r.Contains x 1) →
    (∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) → m' x = m x

theorem WorkFrame.refl (B : Addr) (rs : List (Nat × Nat)) (extra : List Region) (m : Mem) :
    WorkFrame B rs extra m m := fun _ _ _ => rfl

theorem WorkFrame.trans {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {m₁ m₂ m₃ : Mem}
    (h₁ : WorkFrame B rs extra m₁ m₂) (h₂ : WorkFrame B rs extra m₂ m₃) :
    WorkFrame B rs extra m₁ m₃ := fun x he hx => (h₂ x he hx).trans (h₁ x he hx)

theorem WorkFrame.mono {B : Addr} {rs rs' : List (Nat × Nat)} {extra : List Region} {m m' : Mem}
    (h : WorkFrame B rs extra m m') (hs : ∀ r ∈ rs, r ∈ rs') :
    WorkFrame B rs' extra m m' := fun x he hx => h x he fun r hr => hx r (hs r hr)

theorem Frm.work {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {m m' : Mem}
    (h : Frm B rs m m') : WorkFrame B rs extra m m' := fun x _ hx => h x hx

theorem WorkFrame.word_eq {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {Z d : Nat} {m m' : Mem}
    (h : WorkFrame B rs extra m m')
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hf : d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64)
    (he : ∀ r ∈ extra, Region.Disjoint ⟨B, Z⟩ r) : word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  have ha : off B d + BitVec.ofNat 64 i = off B (d + i) := by
    rw [off, Offset.add_ofNat_add_ofNat]
  rw [ha]
  apply h
  · intro r hr hc
    exact he r hr _ (Offset.contains_base B (by omega_arith : d + i + 1 ≤ Z) (by omega_arith)) hc
  · intro r hr
    have hsep := hd r hr
    rw [← ha, ofs_off B (by omega_arith)]
    omega_arith

theorem WorkFrame.wv_eq {B : Addr} {rs : List (Nat × Nat)} {extra : List Region} {Z d k : Nat} {m m' : Mem}
    (h : WorkFrame B rs extra m m')
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hf : d + 8 * k ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64)
    (he : ∀ r ∈ extra, Region.Disjoint ⟨B, Z⟩ r) : wv m' B d k = wv m B d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wv, wv, ih (fun r hr => by have := hd r hr; omega_arith) (by omega_arith)]
    rw [h.word_eq (d := d + 8 * k) (fun r hr => by have := hd r hr; omega_arith)
      (by omega_arith) hn he]

end VG.Proof.Bignum
