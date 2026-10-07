import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Layout

/-! Concrete separation of the measured P-256 candidate's 8192-byte scratch allocation. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Mont VG.Proof.Weierstrass

private theorem field_lay : Lay (cfg p256).M 8192 (·∈slots (cfg p256)) := by
  refine ⟨by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  have h : ∀ x∈slots (cfg p256),∀ y∈slots (cfg p256),x≠y →
      x+8*(cfg p256).M.n≤y ∨ y+8*(cfg p256).M.n≤x := by decide +kernel
  exact fun x y hx hy => h x hx y hy

theorem p256_layout : SecretLay (cfg p256) 8192 :=
  ⟨rfl,field_lay,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide,by decide,by decide +kernel,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem p256_adx_layout : SecretLay (cfg p256x) 8192 :=
  ⟨rfl,⟨field_lay.le,field_lay.apart,field_lay.mo,field_lay.tmp⟩,
    p256_layout.ro,p256_layout.nodup,p256_layout.tbl,p256_layout.J,p256_layout.bits,
    p256_layout.bits_w,p256_layout.bits_tmp,rfl,rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.Ecdh.X86_64.Secret
