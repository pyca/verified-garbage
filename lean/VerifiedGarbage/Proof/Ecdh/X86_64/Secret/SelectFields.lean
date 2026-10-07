import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.SelectWords
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps

/-! The secret scan produces five canonical field elements and preserves other slots. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

def selectedField {C : Curve} (K : WinCfg) (E : Nat → Fe C) (a i : Nat) : Fe C :=
  if 1≤a then E (K.tbl+160*(a-1)+32*i) else if i=1 then 1 else 0

theorem SecretLay.select_local {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈consecutiveFields K.E.x 5,x∈localWrites K := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  simp only [localWrites,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rw [hL.exy,hL.exz]
  omega

theorem select_fields_ok {K : WinCfg} {C : Curve} {base : Addr} {size a : Nat}
    (hL : SecretLay K size) (ht : K.tbl<2^31) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈tableSlots K 16,x∈V) (ha : a≤16) (h8 : s.gpr .r8=BitVec.ofNat 64 a) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.select K)) s fun t =>
      ProgKeep K.M base (consecutiveFields K.E.x 5) s t ∧
      Inv K.M base size C.p (·∈slots K) (consecutiveFields K.E.x 5++V) (tmv C K.M.n base t) t ∧
      ∀ i<5,tmv C K.M.n base t (K.E.x+32*i)=selectedField K E a i := by
  have he := hL.lay.le (K.E.x+128) (local_slots K _ (by simp [localWrites]))
  rw [hL.n] at he
  have hm := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hI.mod.val,hL.n] at hm
  refine WP.mono (select_words_ok K hI.scr hL.n ht hL.table_le (by omega) hL.exy
    (by omega) ha h8) fun t ⟨vt,ot,kt⟩ => ?_
  have kp := ProgKeep.of_consecutiveFields (n:=5) hL.n kt ot
  have hlt : ∀ x∈consecutiveFields K.E.x 5,wordsVal t.mem base x K.M.n<C.p := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    rw [vt i hi']
    split
    · next h1 => exact hI.lt _ (hV _ (table_mem K h1 ha hi'))
    · split
      · exact hOne
      · omega
  refine ⟨kp,hI.of_progKeep hL.lay kp (fun x hx => local_slots K x (hL.select_local x hx)) hlt,?_⟩
  intro i hi
  unfold tmv selectedField
  rw [vt i hi]
  split
  · next h1 => exact hI.val _ (hV _ (table_mem K h1 ha hi))
  · split
    · exact hOneVal
    · exact toM_zero _ _

end VG.Proof.Ecdh.X86_64.Secret
