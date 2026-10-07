import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Cache
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableFields

/-! Store a computed point with canonical Z² and Z³ and preserve its representation. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem cache_store_ok {K : WinCfg} {C : Curve} {base : Addr} {size j : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hj1 : 1≤j) (hj16 : j≤16) (ht : K.tbl<2^31)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈jacCoords K.R,x∈V) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    {P : Point C} (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (.seq (Impl.Ecdh.X86_64.Window5.cache K)
      (.block (Impl.Ecdh.X86_64.Window5.tableStore K))) s fun t =>
      let p := Impl.Ecdh.X86_64.Window5.tablePt K j
      ProgKeep K.M base (localWrites K++consecutiveFields p.x 5) s t ∧
      Inv K.M base size C.p (·∈slots K) (consecutiveFields p.x 5++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t p.x) (tmv C K.M.n base t p.y) (tmv C K.M.n base t p.z) P ∧
      tmv C K.M.n base t (p.x+96)=tmv C K.M.n base t p.z*tmv C K.M.n base t p.z ∧
      tmv C K.M.n base t (p.x+128)=tmv C K.M.n base t (p.x+96)*tmv C K.M.n base t p.z := by
  have hs : (K.E.x+96)∈slots K ∧ (K.E.x+128)∈slots K :=
    ⟨local_slots K _ (by simp [localWrites]),local_slots K _ (by simp [localWrites])⟩
  have hr := hL.lay.le K.R.z (hI.sl _ (hV _ (by simp [jacCoords])))
  have he := hL.lay.le (K.E.x+128) hs.2
  rw [hL.n,hL.rxz] at hr
  rw [hL.n] at he
  have hd : ∀ x∈consecutiveFields (K.tbl+160*(j-1)) 5,x∈slots K := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_right _ (table_mem K hj1 hj16 (List.mem_range.mp hi))
  apply WP.seq
  refine WP.mono (cache_fields_ok hL.n hL.lay hm hL.cache_apart_r hs hI
    (hV _ (by simp [jacCoords]))) fun u ⟨ku,iu,h2,h3⟩ => ?_
  have cu : u.gpr .rbx=BitVec.ofNat 64 j := (ku.gpr _ (by rw [hL.n]; decide)).trans hc
  have hv : ∀ i<5,tableSource K i∈[K.E.x+96,K.E.x+128]++V := by
    intro i hi
    by_cases hp : i<3
    · apply List.mem_append_right
      apply hV
      simp only [tableSource,hp,ite_true,jacCoords,List.mem_cons,List.not_mem_nil,or_false]
      rw [hL.rxy,hL.rxz]
      omega
    · apply List.mem_append_left
      simp only [tableSource,hp,ite_false,List.mem_cons,List.not_mem_nil,or_false]
      omega
  refine WP.mono (tableStore_fields_ok hL.lay hL.n iu hj1 hj16 cu ht hL.table_le
    (by omega) (by omega) hL.r_table_sep hL.cache_table_sep hd hv)
    fun t ⟨kt,it,vt⟩ => ?_
  have v0 := vt 0 (by decide)
  have v1 := vt 1 (by decide)
  have v2 := vt 2 (by decide)
  have v3 := vt 3 (by decide)
  have v4 := vt 4 (by decide)
  simp only [tableSource,Nat.reduceLT,ite_true,ite_false,Nat.mul_zero,Nat.add_zero,
    Nat.mul_one,Nat.reduceSub,Nat.reduceMul,Nat.add_assoc,Nat.reduceAdd,←hL.rxy,←hL.rxz] at v0 v1 v2 v3 v4
  have kr : ∀ x∈jacCoords K.R,cacheEnv K E x=E x :=
    fun x hx => cacheEnv_readonly K E (hL.cache_apart_coords x hx)
  refine ⟨(ku.mono ?_).trans (kt.mono (fun _ hx => List.mem_append_right _ hx)),it.sub ?_,?_,?_,?_⟩
  · intro x hx
    exact List.mem_append_left _ (by simpa only [localWrites,List.mem_append] using Or.inr hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx)
  · dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    simp only [Nat.add_assoc]
    rw [v0,v1,v2,kr _ (by simp [jacCoords]),kr _ (by simp [jacCoords]),kr _ (by simp [jacCoords])]
    exact hJ
  · dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    simp only [Nat.add_assoc]
    rw [v3,v2]
    exact h2
  · dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    simp only [Nat.add_assoc]
    rw [v4,v3,v2]
    exact h3

end VG.Proof.Ecdh.X86_64.Secret
