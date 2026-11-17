module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
import VerifiedGarbage.Proof.Camellia.AArch64.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
public import VerifiedGarbage.Proof.Sm4.AArch64.Round
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Camellia.AArch64.Serial.Prepare`, which only this module used -/

section

/-! # Preparing the constant S-box and raw Camellia schedule -/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

theorem tableWord_byte : ∀ h < 32, ∀ j < 8,
    (tableWord h).extractLsb' (8*j) 8 = Spec.Camellia.sbox1Table.getD (8*h+j) 0 := fun h _ j hj => by
  have r8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  unfold tableWord
  rw [r8, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons, List.foldl_cons, List.foldl_nil]
  exact VG.Proof.Sm4.AArch64.pack8_byte (fun j => Spec.Camellia.sbox1Table.getD (8 * h + j) 0) hj

theorem table_run {s : State} {B : Addr}
    (hb : s.gpr .x5 = B)
    (hw : (⟨B, 8*396⟩ : Region) ∈ s.wr) :
    ∃ t, runBlock isa table s = some t ∧
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

theorem table_bytes {m : Mem} {B : Addr}
    (h : ∀ j < 32, m.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) :
    ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
  intro j hj
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) (h (j/8) (by omega_using [hj]))
  change (m.read (B + BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at e
  rw [Mem.extractLsb'_read _ _ (by omega_using []),tableWord_byte _ (by omega_using [hj]) _ (by omega_using []),
    VG.Offset.add_add,show 8*(j/8)+j%8 = j by omega_using []] at e
  exact e

/-- The same table setup under any permissions covering its scratch space. -/
theorem table_wp {s : State} {B : Addr}
    (hb : s.gpr .x5 = B) (hw : InRegions s.wr B (8*396)) :
    WP isa (.block table) s fun t =>
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  let u := s.withRegions [] [⟨B,8*396⟩]
  obtain ⟨t,he,hv,hg,hd,hw',hf⟩ := table_run (s := u) hb List.mem_cons_self
  obtain ⟨tr,t',hex,heq⟩ := (WP.of_runBlock ⟨t,he,rfl⟩ :
    WP isa (.block table) u (fun t' => t' = t))
  subst t'
  have hcov : Covers u.wr s.wr := Covers.one hw
  have hread : Covers (u.rd ++ u.wr) (s.rd ++ s.wr) := Covers.right hcov
  have ew := VG.AArch64.Exec.widen (s := u) (s' := t) (rd := s.rd) (wr := s.wr) hex hread hcov
  refine ⟨tr,t.withRegions s.rd s.wr,?_,hv,hg,rfl,rfl,hf⟩
  simpa only [u,State.withRegions_withRegions,State.withRegions_self] using ew

end VG.Proof.Camellia.AArch64.Serial

end

end

/-! ### `Camellia.AArch64.Serial.Copy`, which only this module used -/

section

/-! # Copy the expanded schedule using the existing checked block copier -/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.AArch64 (CopyInv copyBlocks_bounded_wp)

theorem copySchedule_wp {s : State}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 272)
    (hw : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 256) 272)
    (hsep : Region.Disjoint ⟨s.gpr .x0,272⟩ ⟨s.gpr .x5 + BitVec.ofNat 64 256,272⟩) :
    WP isa copySchedule s fun t =>
      (∀ j < 272, t.mem (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 j) =
        s.mem (s.gpr .x0 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 256,272⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  let a := s.write .x .x14 (s.gpr .x0)
  let b := a.write .x .x15 (a.gpr .x5 + BitVec.ofNat 64 256)
  let c := b.write .x .x17 17
  have regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → c.gpr r = s.gpr r := by
    intro r h14 h15 h17
    simp only [c,b,a,gpr_write_of_ne _ _ _ h14,gpr_write_of_ne _ _ _ h15,gpr_write_of_ne _ _ _ h17]
  have c14 : c.gpr .x14 = s.gpr .x0 := by simp [c,b,a,State.write]
  have c15 : c.gpr .x15 = s.gpr .x5 + BitVec.ofNat 64 256 := by simp [c,b,a,State.write]
  have c17 : c.gpr .x17 = 17 := by simp [c,State.write]
  unfold copySchedule
  refine WP.seq (WP.of_runBlock ⟨c,?_,?_⟩)
  · have ea : exec (VG.Impl.Aes.AArch64.movR .x14 .x0) s = some a := by
      simp [VG.Impl.Aes.AArch64.movR,exec,State.read,a]
    have eb : exec (.addImm .x .x15 .x5 256) a = some b := by
      rw [exec_addImm_x (by decide)]
      simp [State.read,b]
    have ec : exec (.movz .x .x17 17 0) b = some c := rfl
    rw [runBlock_cons,ea,runStep_some,runBlock_cons,eb,runStep_some,
      runBlock_cons,ec,runStep_some,runBlock_nil]
  · have hA : ∀ j < 34, InRegions (c.rd ++ c.wr) (s.gpr .x0 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hr (by omega_using [hj]) (by decide)
    have hB : ∀ j < 34, InRegions c.wr (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hw (by omega_using [hj]) (by decide)
    have inv : CopyInv (s.gpr .x0) (s.gpr .x5+ BitVec.ofNat 64 256) 17 c 0 c := by
      refine ⟨?_,?_,?_,fun _ h => absurd h (by omega_using []),Frame.refl _ _,fun _ _ _ _ _ => rfl,rfl,rfl⟩
      · simpa using c14
      · simpa using c15
      · simpa using c17
    refine WP.mono (copyBlocks_bounded_wp (by decide) (by decide) hA hB hsep inv) fun t ht =>
      ⟨ht.copied,ht.frame,fun r h14 h15 h17 h21 =>
        (ht.regs r h14 h15 h17 h21).trans (regs r h14 h15 h17),ht.rd,ht.wr⟩

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Preparing the serial core under the existing Camellia key contract -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion)
open VG.Proof.Camellia.AArch64 (KeyArgs)

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total)
    (hR : (⟨B,8*core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun t => Ready t.mem B k ∧ t.gpr .x1 = BitVec.ofNat 64 k.1 ∧
      t.gpr .x5 = B ∧ t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Frame [⟨B,528⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨p,hp,hx1,hrounds,hws,hin,hfit,hdis⟩ := hk
  have hw : InRegions s.wr B (8*396) :=
    ⟨_,hs.wr,by change (⟨B,3344⟩ : Region).Contains B 3168; simp [Region.Contains]⟩
  have hkey : Region.Disjoint ⟨p,272⟩ ⟨B,8*core.total⟩ := hdis _ hR
  change WP isa (.seq (.block table) copySchedule) s _
  refine WP.seq (WP.mono (table_wp hB hw) fun a ⟨aw,ag,ard,awr,af⟩ => ?_)
  have ab : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ap : a.gpr .x0 = p := (ag _ (by decide)).trans hp
  have preserved : ∀ j < 272, a.mem (p+BitVec.ofNat 64 j) = s.mem (p+BitVec.ofNat 64 j) := by
    intro j hj
    exact af.bytes (R := ⟨p,272⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hkey.sub_right (Region.sub_prefix (by decide))) (by decide : 272 ≤ 2^64) hj
  have readKey : InRegions (a.rd ++ a.wr) (a.gpr .x0) 272 := by
    rw [ard,awr,ap]
    exact ⟨_,List.mem_append_left _ hin,Region.contains_self _ _⟩
  have writeKey : InRegions a.wr (a.gpr .x5+BitVec.ofNat 64 256) 272 := by
    rw [awr,ab]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 256+272 ≤ 3344) (by decide)⟩
  have sepKey : Region.Disjoint ⟨a.gpr .x0,272⟩ ⟨a.gpr .x5+BitVec.ofNat 64 256,272⟩ := by
    rw [ap,ab]
    exact hkey.sub_right (VG.Offset.sub_base B (by decide : 256+272 ≤ 3344))
  refine WP.mono (copySchedule_wp readKey writeKey sepKey) fun t ⟨tc,tf,tg,trd,twr⟩ => ?_
  have tab : ∀ j < 256, t.mem (B+BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
    intro j hj
    have tf' : Frame [⟨B+BitVec.ofNat 64 256,272⟩] a.mem t.mem := by simpa only [ab] using tf
    rw [tf'.bytes (R := ⟨B,256⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact VG.Offset.base_disjoint B (by decide : 256 ≤ 256) (by decide : 256+272 ≤ 2^64))
      (by decide : 256 ≤ 2^64) hj]
    exact table_bytes aw j hj
  have keyWords : ∀ i < Spec.Camellia.scheduleLength k.1,
      Spec.Camellia.wordAt t.mem (B+BitVec.ofNat 64 (256+8*i)) = k.2.getD i 0 := by
    intro i hi
    have hi34 : i < 34 := by
      simp only [Spec.Camellia.scheduleLength] at hi
      omega_using [hrounds, hi]
    rw [hws,VG.Proof.Camellia.schedWords_getD _ _ hi]
    unfold Spec.Camellia.wordAt Spec.Camellia.bytesAt
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj8 : j < 8 := List.mem_range.mp hj
    rw [VG.Offset.add_add,VG.Offset.add_add]
    have e := tc (8*i+j) (by omega_using [hi34, hj8])
    rw [ab,ap,preserved _ (by omega_using [hi34, hj8]),VG.Offset.add_add] at e
    simpa only [show 256+8*i+j = 256+(8*i+j) by omega_using []] using e
  refine ⟨⟨hrounds,tab,keyWords⟩,?_,?_,?_,?_,?_,trd.trans ard,twr.trans awr⟩
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans
      ((ag _ (by decide)).trans hx1)
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans ab
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · refine (af.sub (fun r hr => ?_)).trans (tf.sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,Region.sub_prefix (by decide : 256 ≤ 528)⟩
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,by rw [ab]; exact VG.Offset.sub_base B (by decide : 256+272 ≤ 528)⟩

end VG.Proof.Camellia.AArch64.Serial
