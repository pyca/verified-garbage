import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableState
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.LayoutOps

/-! Extending a table prefix preserves every earlier point and its cached powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

def tableStepWrites (K : WinCfg) (m : Nat) : List Nat :=
  localWrites K++consecutiveFields (K.tbl+160*m) 5

theorem tableStepWrites_writes (K : WinCfg) {m : Nat} (hm : m<16) :
    ∀ x∈tableStepWrites K m,x∈writes K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact List.mem_append_right _ (by simpa only [Nat.add_sub_cancel] using
      (table_mem K (a:=m+1) (by omega) (by omega) (List.mem_range.mp hi)))

theorem tableStepWrites_slots (K : WinCfg) {m : Nat} (hm : m<16) :
    ∀ x∈tableStepWrites K m,x∈slots K := by
  intro x hx
  rcases List.mem_append.mp (tableStepWrites_writes K hm x hx) with hx|hx
  · exact local_slots K x hx
  · exact List.mem_append_right _ hx

theorem SecretLay.live_not_step {K : WinCfg} {size m : Nat}
    (hL : SecretLay K size) (hm : m<16) :
    ∀ x∈tableLive K m,x∉tableStepWrites K m := by
  intro x hx hw
  rcases List.mem_append.mp hx with hr|ht
  · rcases List.mem_append.mp hw with hl|he
    · exact hL.ro x hr hl
    · have hb := hL.tbl x (List.mem_append_left _ hr)
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
      have := List.mem_range.mp hi
      omega
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    have hi' := List.mem_range.mp hi
    rcases List.mem_append.mp hw with hl|he
    · have hb := hL.tbl _ (List.mem_append_right _ hl)
      omega
    · obtain ⟨j,hj,he⟩ := List.mem_map.mp he
      have := List.mem_range.mp hj
      omega

theorem tableLive_mono (K : WinCfg) {m n : Nat} (hm : m≤n) :
    ∀ x∈tableLive K m,x∈tableLive K n := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (table_slots_mono K hm x hx)

theorem TableInv.extend {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    {P : Point C} {s₀ s t : State} (hL : SecretLay K size) (hm : m<16)
    (hI : TableInv K C base size P s₀ s m)
    (hk : CounterKeep K.M base (tableStepWrites K m) s t)
    (ht : Inv K.M base size C.p (·∈slots K) (tableLive K (m+1)) (tmv C K.M.n base t) t)
    (hj : let p := Impl.Ecdh.X86_64.Window5.tablePt K (m+1)
      InvJ C (tmv C K.M.n base t p.x) (tmv C K.M.n base t p.y)
        (tmv C K.M.n base t p.z) (mul (m+1) P))
    (hz : let p := Impl.Ecdh.X86_64.Window5.tablePt K (m+1)
      tmv C K.M.n base t (p.x+96)=tmv C K.M.n base t p.z*tmv C K.M.n base t p.z ∧
      tmv C K.M.n base t (p.x+128)=tmv C K.M.n base t (p.x+96)*tmv C K.M.n base t p.z)
    (hc : t.gpr .rbx=BitVec.ofNat 64 (m+1+1)) : TableInv K C base size P s₀ t (m+1) := by
  have hv : ∀ x∈tableLive K m,tmv C K.M.n base t x=tmv C K.M.n base s x :=
    fun x hx => hk.field_eq hL.lay hI.field ht (tableStepWrites_slots K hm)
      hx (tableLive_mono K (by omega) x hx) (hL.live_not_step hm x hx)
  have hr : ∀ x∈winRo K,tmv C K.M.n base t x=tmv C K.M.n base s x :=
    fun x hx => hv x (List.mem_append_left _ hx)
  refine ⟨ht,?_,?_,?_,?_,hc,hI.keep.trans (hk.mono (tableStepWrites_writes K hm))⟩
  · rw [hr _ (by simp [winRo]),hr _ (by simp [winRo]),hr _ (by simp [winRo])]
    exact hI.peer
  · rw [hr _ (by simp [winRo])]
    exact hI.affine
  · intro a ha ham
    by_cases he : a=m+1
    · subst a; exact hj
    · have ham' : a≤m := by omega
      have hq := hI.table a ha ham'
      dsimp only [Impl.Ecdh.X86_64.Window5.tablePt] at hq ⊢
      have h0 := hv _ (tableLive_entry K ha ham' (i:=0) (by decide))
      simp only [Nat.mul_zero,Nat.add_zero] at h0
      rw [h0,
        hv _ (tableLive_entry K ha ham' (i:=1) (by decide)),
        hv _ (tableLive_entry K ha ham' (i:=2) (by decide))]
      exact hq
  · intro a ha ham
    by_cases he : a=m+1
    · subst a; exact hz
    · have ham' : a≤m := by omega
      have hq := hI.cache a ha ham'
      dsimp only [Impl.Ecdh.X86_64.Window5.tablePt] at hq ⊢
      rw [hv _ (tableLive_entry K ha ham' (i:=3) (by decide)),
        hv _ (tableLive_entry K ha ham' (i:=2) (by decide)),
        hv _ (tableLive_entry K ha ham' (i:=4) (by decide))]
      exact hq

end VG.Proof.Ecdh.X86_64.Secret
