module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Proof.Rsa.X86_64.Loops
public import VerifiedGarbage.Proof.RsaOaep.Scan
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-! # Return the primality result to the persistent generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.RsaOaep.X86_64

theorem primeResult_ok {s : State} {B F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {used status : BitVec 64} (L : Lay s F S) (R : Rep s.mem F S V W)
    (hdi : s.gpr .rdi = B)
    (hrused : InRegions (s.rd ++ s.wr) (off B 200) 8)
    (hrstatus : InRegions (s.rd ++ s.wr) (off B 232) 8)
    (hu : word s.mem B 200 = used) (hs : word s.mem B 232 = status)
    (hsep : Mem.Sep (off B 232) 8 (off F 128) 8) :
    WP isa (.block Impl.Dsa.X86_64.Generation.primeResult) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 used) 19 status) ∧
      Outside F 128 32 s.mem t.mem ∧ Keep [.rax] s t := by
  have hread : (s.mem.writeW (off F 128) used).readW (off B 232) 64 = status := by
    rw [Mem.readW_writeW_sep hsep (by decide)]
    exact hs
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off F 128) used).writeW (off F 152) status) (by
    xrun [Impl.Dsa.X86_64.Generation.primeResult, ea_sp, L.rsp, State.ea,
      Impl.Mgf1.X86_64.sp, BitVec.ofInt_natCast, hdr, hdrOff, hdi,
      hrused, hrstatus, hu, hread, L.st (d := 128) (by decide), L.st (d := 152) (by decide)]) rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd W 16 used) 19 status) := by
    rw [hm]
    exact (R.wf L.geo (by decide : 16 < nW) used).wf
      L.geo (by decide : 19 < nW) status
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]
  exact ((writeW_outside _ F _ (d := 128) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 152) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64.Generation
