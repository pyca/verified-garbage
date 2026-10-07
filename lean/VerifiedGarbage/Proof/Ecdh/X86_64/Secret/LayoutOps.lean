import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Layout
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalf

/-! Point-operation separation facts derived from the secret window's layout. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.P256.X86_64

theorem local_slots (K : WinCfg) : ∀ x∈localWrites K,x∈slots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

theorem ro_slots (K : WinCfg) : ∀ x∈winRo K,x∈slots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

theorem r_local (K : WinCfg) : ∀ x∈jacCoords K.R,x∈localWrites K := by
  intro x hx
  simp only [jacCoords,localWrites,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem d_local (K : WinCfg) : ∀ x∈jacCoords K.D,x∈localWrites K := by
  intro x hx
  simp only [jacCoords,localWrites,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem double_local (K : WinCfg) : ∀ x∈doubleSlots K.S K.R,x∈localWrites K := by
  intro x hx
  simp only [doubleSlots,localWrites,winOther,rcbW,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem rcb_local (K : WinCfg) : ∀ x∈rcbW K.S K.D,x∈localWrites K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

theorem SecretLay.double_nodup {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    (doubleSlots K.S K.R).Nodup := by
  have h := hL.nodup
  simp only [localWrites,winOther,rcbW,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  simp only [doubleSlots,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,and_true]
  grind

theorem SecretLay.rcbApart_RP {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    RcbApart K.S K.R K.P K.D := by
  have h := hL.toWinLay.rcbApart_D (Or.inl rfl)
  refine ⟨h.nodup,fun x hx hw => ?_⟩
  have hr : x∈rcbR K.S K.R K.R ∨ x∈winRo K := by
    simp only [rcbR,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  exact hr.elim (fun hh => h.apart x hh hw) (fun hh => hL.ro x hh (rcb_local K x hw))

theorem SecretLay.copy_DR {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈jacCoords K.D,∀ y∈jacCoords K.R,x≠y := by
  have h := hL.toWinLay.rcbApart_D (Or.inl rfl)
  intro x hx y hy he
  apply h.apart y
  · simp only [jacCoords,rcbR,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
    grind
  · rw [←he]
    simp only [jacCoords,rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind

theorem SecretLay.r_table_sep {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    K.R.x+96≤K.tbl ∨ K.tbl+2560≤K.R.x := by
  have hx := hL.tbl K.R.x (List.mem_append_right _ (r_local K _ (by simp [jacCoords])))
  have hz := hL.tbl K.R.z (List.mem_append_right _ (r_local K _ (by simp [jacCoords])))
  rw [hL.rxz] at hz
  omega

theorem SecretLay.cache_table_sep {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    K.E.x+160≤K.tbl ∨ K.tbl+2560≤K.E.x+96 := by
  have hx := hL.tbl (K.E.x+96) (by simp [localWrites])
  have hz := hL.tbl (K.E.x+128) (by simp [localWrites])
  omega

theorem SecretLay.cache_apart_coords {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈jacCoords K.R,x∉[K.E.x+96,K.E.x+128] := by
  have h := hL.nodup
  simp only [localWrites,winOther,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  intro x hx
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_or] at hx ⊢
  grind

theorem SecretLay.cache_apart_r {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    K.R.z∉[K.E.x+96,K.E.x+128] := by
  have h := hL.nodup
  simp only [localWrites,winOther,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at h ⊢
  grind

end VG.Proof.Ecdh.X86_64.Secret
