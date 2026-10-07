import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Select
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Neg
import VerifiedGarbage.Proof.Weierstrass.Window5

/-! A complete signed five-bit lookup, including extraction, selection and Y reflection. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

def entryWrites (K : WinCfg) : List Nat := consecutiveFields K.E.x 5++[K.neg]

theorem SecretLay.entry_local {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈entryWrites K,x∈localWrites K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact hL.select_local x hx
  · obtain rfl := List.mem_singleton.mp hx
    simp [localWrites,winOther]

theorem entry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : SecretLay K size) (hm : UnitMod C.p (2^(64*K.M.n)))
    (ht : K.tbl<2^31) (hOne : K.one<C.p) (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (·∈slots K) V E s)
    (hV : ∀ x∈tableSlots K 16,x∈V) (hz : K.zero∈V) (h0 : E K.zero=0)
    (hj : j<K.J) (hc : s.gpr .rbx=BitVec.ofNat 64 j) (hb : ScalarBits K base k s)
    {P : Point C}
    (hTable : ∀ a,1≤a → a≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K a
      InvJ C (E p.x) (E p.y) (E p.z) (mul a P))
    (hCache : ∀ a,1≤a → a≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K a
      E (p.x+96)=E p.z*E p.z ∧ E (p.x+128)=E (p.x+96)*E p.z) :
    WP isa (.block ((digitCfg K).digit ++ Impl.Ecdh.X86_64.Window5.select K ++ (digitCfg K).negY)) s fun t =>
      ProgKeep K.M base (entryWrites K) s t ∧
      Inv K.M base size C.p (·∈slots K) (entryWrites K++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) (Window5.winPt C P k j) ∧
      tmv C K.M.n base t (K.E.x+96)=tmv C K.M.n base t K.E.z*tmv C K.M.n base t K.E.z ∧
      tmv C K.M.n base t (K.E.x+128)=tmv C K.M.n base t (K.E.x+96)*tmv C K.M.n base t K.E.z := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (digit_ok (digitCfg K) hI.scr (k:=k) (j:=j) (N:=5*K.J)
    (by change 1≤5; decide) (by change 5<9; decide) (by change 5*j+5≤5*K.J; omega)
    hL.bits hc hb) fun a ⟨_,va,ka⟩ => ?_
  have ia := hI.of_keeps ka (by decide)
  have ca : a.gpr .rbx=BitVec.ofNat 64 j := (ka.1 _ (by decide)).trans hc
  have ba : ScalarBits K base k a := by intro i hi; rw [ka.2.1]; exact hb i hi
  have ka' : ProgKeep K.M base [] s a := by
    refine ⟨fun r hr => ka.1 r ?_,ka.2.2.1,ka.2.2.2,fun x _ _ => congrFun ka.2.1 x⟩
    intro hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl <;> exact hr (by rw [hL.n]; decide)
  have hmag : magH 16 (combWin 5 k j)≤16 := magH_le (by
    rw [Window5.combWin_five]
    exact Nat.mod_lt _ (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (select_ok hL ht hOne hOneVal ia hV hmag va hTable hCache)
    fun b ⟨kb,ib,jb,b2,b3⟩ => ?_
  have cb : b.gpr .rbx=BitVec.ofNat 64 j := (kb.gpr _ (by rw [hL.n]; decide)).trans ca
  have bb := ba.keep hL ia.scr (CounterKeep.of_progKeep kb)
    (fun x hx => List.mem_append_left _ (hL.select_local x hx))
  have bz : tmv C K.M.n base b K.zero=0 := by
    rw [(CounterKeep.of_progKeep kb).field_eq hL.lay ia ib
      (fun x hx => local_slots K x (hL.select_local x hx)) hz (List.mem_append_right _ hz)
      (fun hh => hL.ro K.zero (by simp [winRo]) (hL.select_local K.zero hh)),h0]
  have vs : ∀ i<5,K.E.x+32*i∈consecutiveFields K.E.x 5 :=
    fun i hi => List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have vy : K.E.y∈consecutiveFields K.E.x 5 := by simpa only [Nat.mul_one,←hL.exy] using vs 1 (by decide)
  refine WP.mono (neg_fields_ok hL hm ib (List.mem_append_left _ vy)
    (List.mem_append_right _ hz) bz hj cb bb) fun t ⟨kt,it⟩ => ?_
  have jp := negEnv_point hL jb (k:=k) (j:=j)
  have jc := negEnv_cache hL b2 b3 (k:=k) (j:=j)
  have hr : ∀ x∈entryWrites K++V,x∈K.E.y::K.neg::(consecutiveFields K.E.x 5++V) := by
    intro x hx
    simp only [entryWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have vt : ∀ i<5,tmv C K.M.n base t (K.E.x+32*i)=negEnv K (tmv C K.M.n base b) k j (K.E.x+32*i) :=
    fun i hi => it.val _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (vs i hi))))
  have v0 := vt 0 (by decide)
  have v1 := vt 1 (by decide)
  have v2 := vt 2 (by decide)
  have v3 := vt 3 (by decide)
  have v4 := vt 4 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,←hL.exy,←hL.exz] at v0 v1 v2 v3 v4
  refine ⟨(ka'.mono (by simp)).trans ((kb.mono (fun _ hx => List.mem_append_left _ hx)).trans
    (kt.mono ?_)),it.to_tmv.sub hr,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact List.mem_append_left _ vy
    · exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [v0,v1,v2]
    simpa only [Window5.winPt_mag,Window5.combWin_five,decide_eq_true_eq] using jp
  · rw [v3,v4,v2]
    exact jc

end VG.Proof.Ecdh.X86_64.Secret
