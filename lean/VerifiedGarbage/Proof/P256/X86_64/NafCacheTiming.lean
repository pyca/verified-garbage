import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCache
import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! Building the cache uses fixed addresses; lookup depends only on the public digit. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64

private def cacheWin := p256.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP
private def cacheWinAdx := p256x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

theorem nafCachedEntry_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (.block (Naf.cachedEntry cacheWin 4000 5408)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCachedEntry_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (.block (Naf.cachedEntry cacheWinAdx 4000 5408)) := nafCachedEntry_ct

theorem nafSignedCachedEntry_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (Naf.signedCachedEntry cacheWin 4000 5408) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafSignedCachedEntry_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.r8]))
      (Naf.signedCachedEntry cacheWinAdx 4000 5408) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.r8])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (Naf.cacheTable cacheWin.M cacheWin.tbl 4000 8) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem nafCacheTable_adx_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rdi]))
      (Naf.cacheTable cacheWinAdx.M cacheWinAdx.tbl 4000 8) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
