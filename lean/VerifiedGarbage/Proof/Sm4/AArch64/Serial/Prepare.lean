module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
public import VerifiedGarbage.Proof.Sm4.AArch64.Round
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Preparing the constant S-box and raw SM4 schedule -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial

theorem tableWord_byte : ∀ h < 32, ∀ j < 8,
    (tableWord h).extractLsb' (8*j) 8 = Spec.Sm4.sbox.getD (8*h+j) 0 := by
  decide +kernel

theorem preparedTable_run {s : State} {B : Addr}
    (hb : s.gpr .x5 = B)
    (hw : (⟨B, 8*396⟩ : Region) ∈ s.wr) :
    ∃ t, runBlock isa preparedTable s = some t ∧
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  have hrange : tableEntries.map (·.1) = List.range 32 := by
    simp [tableEntries,List.map_map,Function.comp_def]
  obtain ⟨t,he,hv,_,hg,hd,hw',hf⟩ := VG.Proof.Sm4.AArch64.setSlotsN_ok 32
    (by decide) tableEntries (s := s) hb hw
    (fun kv hk => by
      simp only [tableEntries,List.mem_map,List.mem_range] at hk
      obtain ⟨i,hi,rfl⟩ := hk
      exact hi)
    (by rw [hrange]; exact List.nodup_range)
  have hbt : t.gpr .x5 = B := (hg _ (by decide)).trans hb
  refine ⟨t,he,?_,hg,hd,hw',hf⟩
  intro j hj
  have hjmem : (j,tableWord j) ∈ tableEntries :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  have h := hv (j,tableWord j) hjmem
  simp only [VG.Proof.Sm4.AArch64.slotW,VG.AArch64.Straight.wordAddr,VG.Impl.Aes.AArch64.sb,hbt] at h
  exact h

theorem preparedTable_bytes {m : Mem} {B : Addr}
    (h : ∀ j < 32, m.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) :
    ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Sm4.sbox.getD j 0 := by
  intro j hj
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) (h (j/8) (by omega))
  change (m.read (B + BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at e
  rw [Mem.extractLsb'_read _ _ (by omega),tableWord_byte _ (by omega) _ (by omega),
    VG.Offset.add_add,show 8*(j/8)+j%8 = j by omega] at e
  exact e

/-- The same table setup under any permissions covering its scratch space. -/
theorem preparedTable_wp {s : State} {B : Addr}
    (hb : s.gpr .x5 = B) (hw : InRegions s.wr B (8*396)) :
    WP isa (.block preparedTable) s fun t =>
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  let u := s.withRegions [] [⟨B,8*396⟩]
  obtain ⟨t,he,hv,hg,hd,hw',hf⟩ := preparedTable_run (s := u) hb List.mem_cons_self
  obtain ⟨tr,t',hex,heq⟩ := (WP.of_runBlock ⟨t,he,rfl⟩ :
    WP isa (.block preparedTable) u (fun t' => t' = t))
  subst t'
  have hcov : Covers u.wr s.wr := Covers.one hw
  have hread : Covers (u.rd ++ u.wr) (s.rd ++ s.wr) := Covers.right hcov
  have ew := VG.AArch64.Exec.widen (s := u) (s' := t) (rd := s.rd) (wr := s.wr) hex hread hcov
  refine ⟨tr,t.withRegions s.rd s.wr,?_,hv,hg,rfl,rfl,hf⟩
  simpa only [u,State.withRegions_withRegions,State.withRegions_self] using ew

end VG.Proof.Sm4.AArch64.Serial
