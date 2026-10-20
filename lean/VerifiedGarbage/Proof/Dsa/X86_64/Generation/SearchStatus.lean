module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Status handling and termination test of the native p search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem searchStatus_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.pSearchStatus status)) s fun t =>
      SearchControl B counter stride t ∧ word t.mem B 16 = BitVec.ofNat 64 status ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.rax] s t := by
  have hst := h.scr.st (d := 16) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B 16) (BitVec.ofNat 64 status)) (by
    xrun [Impl.Dsa.X86_64.Generation.pSearchStatus, State.ea, hdr, hdrOff, h.rdi, hst]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : status < 2 ^ 32)]) rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 16 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ⟨⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, ?_, ?_⟩,
    by rw [hm, word_writeW_self], ho, hk⟩
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.count
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.offset

theorem searchStatusCmp_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3)
    (hstat : word s.mem B 16 = BitVec.ofNat 64 status) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pSearchStatusCmp) s fun t =>
      t.zf = some (decide (status = 3)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (status = 3)) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.pSearchStatusCmp, State.ea, hdr, hdrOff, h.rdi,
      h.scr.ld (d := 16) (by decide), hstat]
    rw [sub_beq_zero]
    congr 1
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      change status % 2 ^ 64 = 3 at hn
      rwa [Nat.mod_eq_of_lt (by omega : status < 2 ^ 64)] at hn
    · intro he; subst status; rfl) rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
