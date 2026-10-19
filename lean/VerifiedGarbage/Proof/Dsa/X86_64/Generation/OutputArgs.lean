module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prepare output copying and the existing verified zero-output loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem outputArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hlen : W 7 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.X86_64.Generation.outputArgs) s fun t =>
      t.gpr .rsi = off (W 5) packed ∧ t.gpr .rdi = W 6 ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rsi = off (W 5) packed ∧ t.gpr .rdi = W 6 ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.outputArgs, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      L.ld (d := 48) (by decide), R.slot (d := 48) (k := 6) rfl (by decide) rfl,
      L.ld (d := 56) (by decide), R.slot (d := 56) (k := 7) rfl (by decide) hlen,
      sx_ofNat (by decide : packed < 2 ^ 31)]
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 len * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * len)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]) rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩

theorem zeroArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.X86_64.Generation.zeroArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 21 (W 6)) 23 (W 7)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have read : (s.mem.writeW (off F 168) (W 6)).readW (off F 56) 64 = W 7 :=
    (R.wf L.geo (by decide : 21 < nW) _).slot (d := 56) (k := 7) rfl (by decide) (by simp [upd])
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off F 168) (W 6)).writeW (off F 184) (W 7)) (by
    xrun [Impl.Dsa.X86_64.Generation.zeroArgs, ea_sp, L.rsp,
      L.ld (d := 48) (by decide), R.slot (d := 48) (k := 6) rfl (by decide) rfl,
      L.ld (d := 56) (by decide), L.st (d := 168) (by decide), L.st (d := 184) (by decide), read]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd W 21 (W 6)) 23 (W 7)) := by
    rw [hm]
    exact (R.wf L.geo (by decide : 21 < nW) _).wf L.geo (by decide : 23 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  rw [hm]
  exact ((Frame.refl [⟨F, frameBytes⟩] s.mem).writeW (r := ⟨F, frameBytes⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))).writeW (r := ⟨F, frameBytes⟩)
    (by simp) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Dsa.X86_64.Generation
