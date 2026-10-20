module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Status handling and termination test of the native p search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchStatus_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.pSearchStatus status)) s fun t =>
      SearchControl B counter stride t ∧ word t.mem B 16 = BitVec.ofNat 64 status ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.x3] s t := by
  have hst := h.scr.st (d := 16) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off B 16) (BitVec.ofNat 64 status)) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatus, h.x0,
      hdr_enc (by decide : 2 < 32), hst]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 16 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ⟨⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, ?_, ?_⟩,
    by rw [hm, word_writeW_self], ho, hk⟩
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.count
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.offset

theorem searchStatusCmp_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3)
    (hstat : word s.mem B 16 = BitVec.ofNat 64 status) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchStatusCmp) s fun t =>
      eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatusCmp, h.x0,
      hdr_enc (by decide : 2 < 32), h.scr.ld (d := 16) (by decide), hstat, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    change BitVec.ofNat 64 status = (3#64) ↔ status = 3
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      change status % 2 ^ 64 = 3 at hn
      rwa [Nat.mod_eq_of_lt (by omega : status < 2 ^ 64)] at hn
    · intro he; subst status; rfl) rfl rfl rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation
