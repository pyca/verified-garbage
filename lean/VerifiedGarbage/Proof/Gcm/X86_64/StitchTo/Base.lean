module

import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The 256-bit VAES loops: lanes of 32-byte loads and stores

Untrusted: everything here is checked by Lean. The lanes of a 32-byte load,
store and register, which the loops' XOR into the output
(`Stitch.xorDataKM_ok`) reads and writes.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx blockAt_writeW_out)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi)
open VG.Proof.Aes.X86_64.AesNi (ofInt_natCast blockAt_frame eval_pxor)
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- Lane `l` of a 32-byte store, as a block. -/
theorem blockAt_writeW_lane2 (m : Mem) (a : Addr) (v : BitVec 256) {l : Nat} (hl : l < 2) :
    blockAt (m.writeW a v) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (v.extractLsb' (128 * l) 128) revMask := by
  have e := readW_writeW_inside m a v (k := 16 * l) (n := 16) (by omega) (by decide)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  rw [blockAt_eq, e]

/-- Lane `l` of a 32-byte load. -/
theorem load256_lane (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    (m.readW a 256).extractLsb' (128 * l) 128 = m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using load256_lo m a
  · simpa using load256_hi m a

/-- Lane `l` of a register's 256 bits. -/
theorem ymm_lane2 (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (128 * l) 128 = s.lane r l := by
  rw [State.ymm_eq]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact VG.Proof.Aes.X86_64.Vaes.extract_lo _ _
  · exact VG.Proof.Aes.X86_64.Vaes.extract_hi _ _

end VG.Proof.Gcm.X86_64.StitchTo
