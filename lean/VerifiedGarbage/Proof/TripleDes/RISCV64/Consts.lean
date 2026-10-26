module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Feistel
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Storing the round function's constants

`storeConsts_wp`: `storeConsts vs off` leaves the words `vs` at `off(sb)` on
(`constMem`), writing only them, `t0` and `t1`.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64

/-- The memory `m` with the words `vs` written at `B + off` on. -/
def constMem (m : Mem) (B : Addr) : List (BitVec 64) → Nat → Mem
  | [], _ => m
  | v :: vs, off => constMem (m.writeW (B + BitVec.ofNat 64 off) v) B vs (off + 8)

theorem constMem_frame (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 →
      Frame [⟨B + BitVec.ofNat 64 off, 8 * vs.length⟩] m (constMem m B vs off) := by
  induction vs with
  | nil => intro m off _; exact Frame.refl _ _
  | cons v vs ih =>
    intro m off h
    simp only [List.length_cons] at h
    have h1 : Frame [⟨B + BitVec.ofNat 64 off, 8 * (vs.length + 1)⟩] m
        (m.writeW (B + BitVec.ofNat 64 off) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) v (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    have h2 := ih (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega)
    refine h1.trans (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.sub B (by omega) (by omega)

theorem constMem_read (B : Addr) (vs : List (BitVec 64)) :
    ∀ (m : Mem) (off : Nat), off + 8 * vs.length ≤ 2048 → ∀ c < vs.length,
      (constMem m B vs off).readW (B + BitVec.ofNat 64 (off + 8 * c)) 64 = vs.getD c 0 := by
  induction vs with
  | nil => intro _ _ _ c hc; simp at hc
  | cons v vs ih =>
    intro m off h c hc
    simp only [List.length_cons] at h hc
    rcases c with _ | c
    · have hf := constMem_frame B vs (m.writeW (B + BitVec.ofNat 64 off) v) (off + 8) (by omega)
      simp only [constMem, Nat.mul_zero, Nat.add_zero, List.getD_cons_zero]
      rw [hf.readW (r := ⟨B + BitVec.ofNat 64 off, 8⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint B (Or.inl (Nat.le_refl _)) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · simp only [constMem, List.getD_cons_succ]
      rw [show off + 8 * (c + 1) = off + 8 + 8 * c by omega]
      exact ih _ (off + 8) (by omega) c (by omega)

theorem storeConsts_wp (vs : List (BitVec 64)) :
    ∀ (off : Nat) (s : State) (Q : State → Prop), (s.gpr sb).toNat % 8 = 0 → off % 8 = 0 →
      off + 8 * vs.length ≤ 2048 →
      (∀ c < vs.length, InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (off + 8 * c)) 8) →
      (∀ t : State, t.mem = constMem s.mem (s.gpr sb) vs off → t.rd = s.rd → t.wr = s.wr →
        t.sp = s.sp → (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r) → Q t) →
      WP isa (.block (storeConsts vs off)) s Q := by
  induction vs with
  | nil =>
    intro off s Q _ _ _ _ hQ
    exact WP.block_nil (hQ s rfl rfl rfl rfl fun _ _ _ => rfl)
  | cons v vs ih =>
    intro off s Q hal hoff hlim hin hQ
    simp only [List.length_cons] at hlim
    rw [storeConsts, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (ByteLoad.li64_ok (s := s) (by decide) v) fun s₁ hs₁ => ?_
    subst hs₁
    have hb₁ : ((s.write .t1 (sext32 (v.setWidth 32))).write .t0 v).gpr sb = s.gpr sb := by
      simp only [gpr_write, sb, reduceCtorEq, ite_false]
    let s₂ : State := { (s.write .t1 (sext32 (v.setWidth 32))).write .t0 v with
      mem := s.mem.writeW (s.gpr sb + BitVec.ofNat 64 off) v }
    refine WP.of_runBlock ⟨s₂, ?_, ?_⟩
    · have h0 := hin 0 (by simp)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      rw [runBlock_cons, exec_store_d (by omega) (by rw [hb₁]; exact Spill.al8 hal hoff)
        (by rw [hb₁]; exact h0), runStep_some, runBlock_nil]
      simp only [hb₁, gpr_write_self, s₂]
      rfl
    · have hb₂ : s₂.gpr sb = s.gpr sb := hb₁
      refine ih (off + 8) s₂ Q (by rw [hb₂]; exact hal) (by omega) (by omega) (fun c hc => ?_)
        fun t hm hrd hwr hsp hg => hQ t ?_ hrd hwr hsp fun r h0 h1 => ?_
      · rw [hb₂, show off + 8 + 8 * c = off + 8 * (c + 1) by omega]
        exact hin (c + 1) (by simp only [List.length_cons]; omega)
      · rw [hm, hb₂]; rfl
      · rw [hg r h0 h1]
        simp only [s₂, gpr_write, h0, h1, ite_false]

end VG.Proof.TripleDes.RISCV64
