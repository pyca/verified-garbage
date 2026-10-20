module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Scan
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
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
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-! # Frame arguments for a complete p-candidate attempt -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.RsaOaep.X86_64

theorem pAttemptArgs_ok {s : State} {B F S op : Addr} {V : Nat → Byte}
    {W : Nat → BitVec 64} {offset : BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hdi : s.gpr .rdi = B)
    (hread : InRegions (s.rd ++ s.wr) (off B 8) 8)
    (hoff : word s.mem B 8 = offset)
    (hop : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped = op) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 27 (W 3)) ∧
      Outside F 0 224 s.mem t.mem ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hst0 : InRegions s.wr F 8 := by simpa [off] using L.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
      t.mem = ((s.mem.writeW (off F 0) op).writeW (off F 16) offset).writeW
        (off F 216) (W 3)) (by
    xrun [Impl.Dsa.X86_64.Generation.pAttemptArgs, ea_sp, L.rsp, State.ea,
      Impl.Mgf1.X86_64.sp, BitVec.ofInt_natCast, hdr, hdrOff, hdi, hread, hoff,
      L.ld (d := 40) (by decide), L.ld (d := 24) (by decide),
      hst0, L.st (d := 16) (by decide), L.st (d := 216) (by decide),
      R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      R.slot (d := 24) (k := 3) rfl (by decide) rfl,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.shaped < 2 ^ 31), hop]) rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 27 (W 3)) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) op).wf L.geo
      (by decide : 2 < nW) offset).wf L.geo (by decide : 27 < nW) (W 3)
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]
  exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 16) (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ F _ (d := 216) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64.Generation
