module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.Lane0
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# Interleaved counter mode and GHASH in AVX: clearing the product

`zero_ok`: `zero` clears the product (`Prod.zero`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs batch gq group ordE ordD first body dbody ghLoad lastG)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost kp nr cp yp dp nb pp kR cR yR dR pR sch ciph cb hk y₀ bAddr
  blk ctb in_sub in_sub_int in_rdwr addr_eq ghash_append16 nextE_ok nextD_ok store16_ok blocks_ctr32
  blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## A group -/

/-- Clear the product. -/
theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' => prod (s'.proj 0) = Prod.zero ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl (Pclmul.zero_ok (s.proj 0)))
    fun s' ⟨⟨z, o⟩, hi, hg⟩ => ⟨z, hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr,
      fun r hr l hl => ?_⟩
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · refine hi r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h9, h10⟩ := hr
    simp [Impl.Gcm.X86_64.StitchAvx.zero, vdst, h8, h9, h10]

end VG.Proof.Gcm.X86_64.StitchAvx
