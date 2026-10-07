import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTransfer

/-! Scratch layout for sixteen Jacobian points with two cached powers per point. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def localWrites (K : WinCfg) : List Nat := winOther K++[K.E.x+96,K.E.x+128]
def tableSlots (K : WinCfg) (m : Nat) : List Nat := consecutiveFields K.tbl (5*m)
def slots (K : WinCfg) : List Nat := winRo K++localWrites K++tableSlots K 16
def writes (K : WinCfg) : List Nat := localWrites K++tableSlots K 16

structure SecretLay (K : WinCfg) (size : Nat) : Prop where
  n : K.M.n=4
  lay : Lay K.M size (·∈slots K)
  ro : ∀ x∈winRo K,x∉localWrites K
  nodup : (localWrites K).Nodup
  tbl : ∀ x∈winRo K++localWrites K,x+32≤K.tbl ∨ K.tbl+2560≤x
  J : 1≤K.J ∧ K.J≤4096
  bits : K.bits+5*K.J≤size
  bits_w : ∀ x∈writes K,K.bits+5*K.J≤x ∨ x+32≤K.bits
  bits_tmp : K.bits+5*K.J≤K.M.tmp ∨ K.M.tmp+32≤K.bits
  exy : K.E.y=K.E.x+32
  exz : K.E.z=K.E.x+64
  rxy : K.R.y=K.R.x+32
  rxz : K.R.z=K.R.x+64
  dxy : K.D.y=K.D.x+32
  dxz : K.D.z=K.D.x+64

theorem table_mem (K : WinCfg) {a i m : Nat} (ha : 1≤a) (ham : a≤m) (hi : i<5) :
    K.tbl+160*(a-1)+32*i∈tableSlots K m := by
  apply List.mem_map.mpr
  refine ⟨5*(a-1)+i,List.mem_range.mpr (by omega),?_⟩
  omega

theorem table_slots_mono (K : WinCfg) {m n : Nat} (hmn : m≤n) :
    ∀ x∈tableSlots K m,x∈tableSlots K n := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),rfl⟩

theorem SecretLay.table_le {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    K.tbl+2560≤size := by
  have h := hL.lay.le (K.tbl+32*79) (List.mem_append_right _
    (List.mem_map.mpr ⟨79,by decide,rfl⟩))
  rw [hL.n] at h
  omega

theorem SecretLay.old_slots {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈winSlots K,x∈slots K := by
  intro x hx
  simp only [winSlots,slots,List.mem_append] at hx ⊢
  rcases hx with (hx|hx)|hx
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr (List.mem_append_left _ hx))
  · right
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    rw [hL.n]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),rfl⟩

theorem SecretLay.old_writes {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈winWs K,x∈writes K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ (List.mem_append_left _ hx)
  · apply List.mem_append_right
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    rw [hL.n]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by have := List.mem_range.mp hi; omega),rfl⟩

theorem SecretLay.toWinLay {K : WinCfg} {size : Nat} (hL : SecretLay K size) : WinLay K size := by
  refine ⟨?_,?_,?_,?_,by rw [hL.n]; decide,hL.J,by have := hL.bits; omega,?_⟩
  · exact { le := fun x hx => hL.lay.le x (hL.old_slots x hx)
            mo := fun x hx => hL.lay.mo x (hL.old_slots x hx)
            tmp := fun x hx => hL.lay.tmp x (hL.old_slots x hx)
            apart := fun x y hx hy hxy => hL.lay.apart x y (hL.old_slots x hx) (hL.old_slots y hy) hxy }
  · exact fun x hx hy => hL.ro x hx (List.mem_append_left _ hy)
  · have h := hL.nodup
    rw [localWrites,List.nodup_append] at h
    exact h.1
  · intro x hx
    have h := hL.tbl x (by
      rcases List.mem_append.mp hx with hx|hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_left _ hx))
    rw [hL.n]
    omega
  · intro w hw
    simp only [winW,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩|rfl
    · have h := hL.bits_w x (hL.old_writes x hx)
      rw [hL.n]
      omega
    · have h := hL.bits_tmp
      rw [hL.n]
      omega

end VG.Proof.Ecdh.X86_64.Secret
