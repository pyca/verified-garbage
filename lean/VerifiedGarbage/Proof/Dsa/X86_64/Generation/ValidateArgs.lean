module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # Set the packed-domain checker's arguments from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem validateArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {pLen qLen : Nat}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.validateArgs pLen qLen)) s fun t =>
      t.gpr .rdi = off (W 5) packed ∧ t.gpr .r8 = off (W 5) domainCheck ∧
      t.gpr .rdx = BitVec.ofNat 64 pLen ∧ t.gpr .rcx = BitVec.ofNat 64 qLen ∧
      t.mem = s.mem ∧ Keep [.rdi, .r8, .rdx, .rcx] s t := by
  have cast (n : Nat) (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine WP.mono (WP.keep [.rdi, .r8, .rdx, .rcx] (Q := fun t =>
      t.gpr .rdi = off (W 5) packed ∧ t.gpr .r8 = off (W 5) domainCheck ∧
      t.gpr .rdx = BitVec.ofNat 64 pLen ∧ t.gpr .rcx = BitVec.ofNat 64 qLen ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.validateArgs, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      sx_ofNat (by decide : packed < 2 ^ 31), sx_ofNat (by decide : domainCheck < 2 ^ 31),
      cast pLen hp, cast qLen hq]) rfl)
    fun t ⟨⟨hdi, h8, hdx, hcx, hm⟩, hk⟩ => ⟨hdi, h8, hdx, hcx, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
