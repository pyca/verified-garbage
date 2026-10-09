import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Round

def csub (m a : BitVec 32) : BitVec 32 := if a.toNat≤(a-m).toNat then a else a-m

def before (g : Nat) (a h : BitVec 32) : BitVec 32 :=
  let f := HighPack.raw g a
  let delta := ((f*BitVec.ofNat 32 (2*g)-a) >>> 31 <<< 1)-1
  f+(if h=0 then 0 else delta)+BitVec.ofNat 32 (dMod g)

def value (g : Nat) (a h : BitVec 32) : BitVec 32 :=
  csub (BitVec.ofNat 32 (dMod g)) (csub (BitVec.ofNat 32 (dMod g)) (before g a h))

 theorem csub_toNat {m a : BitVec 32} (hm : m.toNat<2^31) (ha : a.toNat<2^31) :
    (csub m a).toNat=if a.toNat<m.toNat then a.toNat else a.toNat-m.toNat := by
  by_cases hz : m=0
  · subst m; simp [csub]
  have hmpos : 0<m.toNat := by bv_omega
  unfold csub
  by_cases h : a.toNat<m.toNat
  · rw [ite_eq_left (by bv_omega),ite_eq_left h]
  · rw [ite_eq_right (by bv_omega),ite_eq_right h,BitVec.toNat_sub]
    omega

 theorem sub_sign {x y : BitVec 32} (hx : x.toNat<2^31) (hy : y.toNat<2^31) :
    (x-y) >>> 31=if x.toNat<y.toNat then 1 else 0 := by
  by_cases h : x.toNat<y.toNat
  · rw [ite_eq_left h]; bv_omega
  · rw [ite_eq_right h]; bv_omega

 theorem signed_adjust {f m : BitVec 32} (hf : f.toNat≤44) (hm : m.toNat≤44)
    (hpos : 0<m.toNat) (b : Bool) :
    ((f+((if b then (1 : BitVec 32) else 0) <<< 1)-1)+m).toNat=
      if b then f.toNat+m.toNat+1 else f.toNat+m.toNat-1 := by
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · bv_omega
  · bv_omega

 theorem before_toNat {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (before g a h).toNat =
      if h≠0 then (if hbF g a.toNat*(2*g)<a.toNat then hbF g a.toNat+hbM g+1
        else hbF g a.toNat+hbM g-1) else hbF g a.toNat+hbM g := by
  have hf := HighPack.raw_toNat hg ha
  have hb := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm16 : 16≤hbM g := by rcases hg with rfl|rfl <;> decide
  have hm44 : hbM g≤44 := by rcases hg with rfl|rfl <;> decide
  have hg2 : 2*g≤523776 := by rcases hg with rfl|rfl <;> decide
  have hd : (BitVec.ofNat 32 (dMod g)).toNat=hbM g := by
    rw [BitVec.toNat_ofNat,dMod_eq hg]; omega
  have hp : (HighPack.raw g a * BitVec.ofNat 32 (2*g)).toNat=hbF g a.toNat*(2*g) := by
    rw [BitVec.toNat_mul,hf,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 2*g<2^32 by omega)]
    have := Nat.mul_le_mul (Nat.le_trans hb hm44) hg2
    exact Nat.mod_eq_of_lt (by omega)
  have hq : q=8380417 := rfl
  have hpbound := Nat.mul_le_mul (Nat.le_trans hb hm44) hg2
  dsimp only [before]
  by_cases hh : h=0
  · rw [ite_eq_left hh,ite_eq_right (by exact not_not_intro hh),BitVec.toNat_add,BitVec.toNat_add,hf,hd]
    change ((hbF g a.toNat+0)%2^32+hbM g)%2^32=_
    omega
  · rw [ite_eq_right hh,ite_eq_left hh]
    have hsign := sub_sign (x:=HighPack.raw g a * BitVec.ofNat 32 (2*g)) (y:=a)
      (by rw [hp]; omega) (by omega)
    rw [hp] at hsign
    rw [hsign]
    have hh := signed_adjust (f:=HighPack.raw g a) (m:=BitVec.ofNat 32 (dMod g))
      (by rw [hf]; omega) (by rw [hd]; omega) (by rw [hd]; omega)
      (decide (hbF g a.toNat*(2*g)<a.toNat))
    simp only [decide_eq_true_eq] at hh
    rw [hf,hd] at hh
    have he (f d : BitVec 32) : f+(d-1)=f+d-1 := by bv_omega
    rw [he]
    exact hh

 theorem value_toNat {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat =
      (if h≠0 then (if hbF g a.toNat*(2*g)<a.toNat then hbF g a.toNat+hbM g+1
        else hbF g a.toNat+hbM g-1) else hbF g a.toNat+hbM g)%hbM g := by
  have hv := before_toNat hg (h:=h) ha
  have hf := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm16 : 16≤hbM g := by rcases hg with rfl|rfl <;> decide
  have hm44 : hbM g≤44 := by rcases hg with rfl|rfl <;> decide
  have hd : (BitVec.ofNat 32 (dMod g)).toNat=hbM g := by
    rw [BitVec.toNat_ofNat,dMod_eq hg]; omega
  have hb : (before g a h).toNat<3*hbM g := by rw [hv]; (repeat' split) <;> omega
  have hc := csub_toNat (m:=BitVec.ofNat 32 (dMod g)) (a:=before g a h)
    (by rw [hd]; omega) (by omega)
  rw [hd] at hc
  have hc2 := csub_toNat (m:=BitVec.ofNat 32 (dMod g))
    (a:=csub (BitVec.ofNat 32 (dMod g)) (before g a h))
    (by rw [hd]; omega) (by rw [hc]; split <;> omega)
  rw [hd,hc] at hc2
  change (csub _ (csub _ _)).toNat=_
  rw [hc2,←hv]
  by_cases h1 : (before g a h).toNat<hbM g
  · simp only [ite_eq_left h1,Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right h1,Nat.mod_eq_sub_mod (by omega)]
    by_cases h2 : (before g a h).toNat-hbM g<hbM g
    · rw [ite_eq_left h2,Nat.mod_eq_of_lt h2]
    · rw [ite_eq_right h2,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]

 theorem value_spec {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat=(useHint g (decide (h≠0)) ⟨a.toNat,ha⟩).toNat := by
  rw [value_toNat hg ha,useHint_eq (mem_of_isG hg)]
  simp only [decide_eq_true_eq]
  rfl

 theorem value_lt {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat<hbM g := by
  rw [value_toNat hg ha]
  exact Nat.mod_lt _ (hbM_pos hg)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
