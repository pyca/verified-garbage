module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Initialize and test native seed and generator tape cursors -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem tapeReset_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots)
    (hu : slots.used < 37) (hu14 : slots.used ≠ 14) :
    WP isa (.block (tapeReset slots)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W slots.used 0) ∧
      Outside F (8 * slots.used) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off F (8 * slots.used)) (0 : BitVec 64)) (by
    xrun [tapeReset, ea_sp, L.rsp,
      L.st (d := 8 * slots.used) (by unfold frameBytes; omega)]
    rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W slots.used 0) := by
    rw [hm]; exact R.wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu14])
    (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]
  exact writeW_outside _ _ _ (by omega)

theorem tapeStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block tapeStatus) s fun t =>
      t.zf = some (W 19 == 3) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (W 19 == 3) ∧ t.mem = s.mem) (by
    xrun [tapeStatus, ea_sp, L.rsp, L.ld (d := 152) (by decide),
      R.slot (d := 152) (k := 19) rfl (by decide) rfl]
    rw [sub_beq_zero]) rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem tapeExhausted_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block (stackStatus 3 ++ ([.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)] : List Instr))) s fun t =>
      t.zf = some false ∧ Lay t F S ∧ Rep t.mem F S V (upd W 19 3) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some false ∧ t.mem = s.mem.writeW (off F 152) (3 : BitVec 64)) (by
    xrun [stackStatus, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.st (d := 152) (by decide)]
    rfl) rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 19 3) := by
    rw [hm]; exact R.wf L.geo (by decide : 19 < nW) _
  refine ⟨hz, lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86_64.Generation
