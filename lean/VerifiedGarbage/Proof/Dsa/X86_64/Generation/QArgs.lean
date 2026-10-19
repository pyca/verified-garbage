module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QShape
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prepare the shared candidate shaper's arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem qArgs_ok {s : State} {F S op : Addr} {len : Nat} (L : Lay s F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hop : W 0 = op) (hll : W 28 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.X86_64.Generation.qArgs) s fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off S oDig ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rdi, .rsi, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off S oDig ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩
  have hs := L.slot
  simp only [VG.Proof.Bignum.word] at hs
  have hld0 : InRegions (s.rd ++ s.wr) F 8 := by simpa [off] using L.ld (d := 0) (by decide)
  have hv0 : s.mem.readW F 64 = op := by
    simpa [off] using R.slot (d := 0) (k := 0) rfl (by decide) hop
  xrun [Impl.Dsa.X86_64.Generation.qArgs, ea_sp, L.rsp,
    hld0, hv0, L.ld (d := sScr) (by decide), L.ld (d := sLabLen) (by decide), hs,
    R.slot (d := sLabLen) (k := 28) rfl (by decide) hll, sx_ofNat]
  constructor
  · exact congrArg (fun x : BitVec 64 => S + x) (by decide)
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 len * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * len)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Dsa.X86_64.Generation
