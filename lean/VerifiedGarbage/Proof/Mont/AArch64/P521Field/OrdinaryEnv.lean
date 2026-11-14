module

public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Cms
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.AArch64.Target


/-! Ordinary field slots retain independent range bounds for weak products. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

/-- A live slot has its own range bound; its field value uses ordinary residue form. -/
structure OrdinaryInv (base : Addr) (p : Nat) [NeZero p] (loc : Nat → Nat) (V : List Nat)
    (E : Nat → Fin p) (caps : Nat → Nat) (s : State) : Prop where
  bound : ∀ x∈V, wordsVal s.mem base (loc x) 9<caps x*p
  value : ∀ x∈V, Fin.ofNat p (wordsVal s.mem base (loc x) 9)=E x

theorem OrdinaryInv.sub {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat} {V V' : List Nat}
    {E : Nat → Fin p} {caps : Nat → Nat} {s : State} (h : OrdinaryInv base p loc V E caps s)
    (hv : ∀x∈V',x∈V) : OrdinaryInv base p loc V' E caps s :=
  ⟨fun x hx => h.bound x (hv x hx),fun x hx => h.value x (hv x hx)⟩

theorem OrdinaryInv.update {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin p} {caps : Nat → Nat} {s t : State} (h : OrdinaryInv base p loc V E caps s)
    {o cap : Nat} {v : Fin p} (outside : Outside base (loc o) 72 s.mem t.mem)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) (fits : ∀x∈V,loc x+72≤2^64)
    (hb : wordsVal t.mem base (loc o) 9<cap*p) (he : Fin.ofNat p (wordsVal t.mem base (loc o) 9)=v) :
    OrdinaryInv base p loc (o::V) (Function.update E o v) (Function.update caps o cap) t := by
  have unchanged (x : Nat) (hx : x∈V) (hxo : x≠o) : wordsVal t.mem base (loc x) 9=wordsVal s.mem base (loc x) 9 :=
    outside.wordsVal (by simpa only [Nat.reduceMul] using apart x hx hxo)
      (by simpa only [Nat.reduceMul] using fits x hx)
  constructor
  · intro x hx
    by_cases hxo : x=o
    · subst x; simpa only [Function.update_self] using hb
    · have hv : x∈V := List.mem_of_ne_of_mem hxo hx
      rw [Function.update_of_ne hxo,unchanged x hv hxo]
      exact h.bound x hv
  · intro x hx
    by_cases hxo : x=o
    · subst x; simpa only [Function.update_self] using he
    · have hv : x∈V := List.mem_of_ne_of_mem hxo hx
      rw [Function.update_of_ne hxo,unchanged x hv hxo]
      exact h.value x hv

theorem ordinary_mul {p : Nat} [NeZero p] (a b : Nat) :
    Fin.ofNat p ((a*b)%p)=Fin.ofNat p a*Fin.ofNat p b := by
  rw [ofNat_mod,ofNat_mul']

theorem ordinary_add {p : Nat} [NeZero p] (a b : Nat) :
    Fin.ofNat p ((a+b)%p)=Fin.ofNat p a+Fin.ofNat p b := by
  rw [ofNat_mod,ofNat_add']

theorem ordinary_sub {p a b : Nat} [NeZero p] (hb : b≤a+p) :
    Fin.ofNat p ((a+p-b)%p)=Fin.ofNat p a-Fin.ofNat p b := by
  have he : Fin.ofNat p (a+p-b)+Fin.ofNat p b=Fin.ofNat p a := by
    rw [←ofNat_add',Nat.sub_add_cancel hb,ofNat_eq_ofNat,Nat.add_mod_right]
  rw [ofNat_mod]
  grind

theorem ordinary_cms {p : Nat} [NeZero p] (C a D b : Nat) (hb : b≤p) :
    Fin.ofNat p ((C*a+D*(p-b))%p)=Cms.smulN C (Fin.ofNat p a)-Cms.smulN D (Fin.ofNat p b) := by
  have he : Fin.ofNat p (D*(p-b))+Fin.ofNat p D*Fin.ofNat p b=0 := by
    rw [←ofNat_mul',←ofNat_add',←Nat.mul_add,Nat.sub_add_cancel hb]
    apply Fin.ext
    rw [Fin.val_ofNat,Nat.mul_mod_left]
    rfl
  rw [Cms.smulN_fin,Cms.smulN_fin,ofNat_mod,ofNat_add',ofNat_mul',ofNat_mul']
  rw [ofNat_mul'] at he
  grind

end VG.Proof.Mont.AArch64.P521Field
