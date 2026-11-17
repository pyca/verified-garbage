module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillABI
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.Generation.EntrySpill`, which this module and modules that import it used -/

section

/-! Store the AAPCS64 preserved registers outside the generation frame words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def vectorSlots : List (Reg × Nat) :=
  [⟨.x0, 384⟩, ⟨.x1, 392⟩, ⟨.x2, 400⟩, ⟨.x3, 408⟩,
   ⟨.x4, 416⟩, ⟨.x5, 424⟩, ⟨.x6, 432⟩, ⟨.x7, 440⟩]

def vectorValues (s : State) : Reg → BitVec 64
  | .x0 => laneOf s .v8 0 | .x1 => laneOf s .v9 0
  | .x2 => laneOf s .v10 0 | .x3 => laneOf s .v11 0
  | .x4 => laneOf s .v12 0 | .x5 => laneOf s .v13 0
  | .x6 => laneOf s .v14 0 | _ => laneOf s .v15 0

def savedAbiMem (s : State) : Mem :=
  Spill.saveMem (Spill.saveMem s.mem (Refill.refillBase s) s.gpr abiGprs)
    (Refill.refillBase s) (vectorValues s) vectorSlots

def linkRegion (s : State) : Region := ⟨off (Refill.refillBase s) 296, 152⟩

def linkState (s : State) : State :=
  { allocState 480 s with
    gpr := fun r => if r = .x9 then laneOf s .v15 0 else s.gpr r
    mem := (savedAbiMem s).writeW (linkRegion s).base (s.gpr .x30) }

theorem entrySave_ok (s : State) :
    WP isa (.block entrySave) (allocState 480 s) (fun t => t = linkState s) := by
  have hw (d : Nat) (hd : d + 8 ≤ 480) :
      InRegions (allocState 480 s).wr ((allocState 480 s).sp + BitVec.ofNat 64 d) 8 :=
    ⟨⟨Refill.refillBase s, 480⟩, List.mem_cons_self .., Offset.contains_base _ hd (by omega_using [hd])⟩
  simp only [entrySave, abiGprs, abiVectors, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append]
  brun [exec_storeSp (off := 304) (by decide), exec_storeSp (off := 312) (by decide), exec_storeSp (off := 320) (by decide), exec_storeSp (off := 328) (by decide), exec_storeSp (off := 336) (by decide), exec_storeSp (off := 344) (by decide), exec_storeSp (off := 352) (by decide), exec_storeSp (off := 360) (by decide), exec_storeSp (off := 368) (by decide), exec_storeSp (off := 376) (by decide), exec_storeSp (off := 384) (by decide), exec_storeSp (off := 392) (by decide), exec_storeSp (off := 400) (by decide), exec_storeSp (off := 408) (by decide), exec_storeSp (off := 416) (by decide), exec_storeSp (off := 424) (by decide), exec_storeSp (off := 432) (by decide), exec_storeSp (off := 440) (by decide), exec_storeSp (off := 296) (by decide), hw 304 (by decide), hw 312 (by decide), hw 320 (by decide), hw 328 (by decide), hw 336 (by decide), hw 344 (by decide), hw 352 (by decide), hw 360 (by decide), hw 368 (by decide), hw 376 (by decide), hw 384 (by decide), hw 392 (by decide), hw 400 (by decide), hw 408 (by decide), hw 416 (by decide), hw 424 (by decide), hw 432 (by decide), hw 440 (by decide), hw 296 (by decide), exec_umov (by decide : 0 < 2), savedAbiMem, Spill.saveMem,
    abiGprs, vectorSlots, vectorValues, linkState, linkRegion, laneOf, State.write]
  congr 1
  funext r
  by_cases h : r = .x9 <;> simp only [h, ite_true, ite_false] <;> rfl

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.EntrySavedAbi`, which only this module used -/

section

/-! The generation phases preserve the saved AAPCS64 registers. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem link_gprs (s : State) : Spill.Saved (Refill.refillBase s) s.gpr abiGprs (linkState s).mem := by
  have g := Spill.saveMem_saved (l := abiGprs) (by decide) s.mem (Refill.refillBase s) s.gpr
  have vf := Spill.saveMem_frame (l := vectorSlots) (lo := 384) (n := 64) (by decide) (by decide)
    (Spill.saveMem s.mem (Refill.refillBase s) s.gpr abiGprs) (Refill.refillBase s) (vectorValues s)
  have gv := g.frame_in (lo := 304) (n := 80) (by decide) vf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (Refill.refillBase s) (by decide) (by decide) (by decide))
  have lf : Frame [⟨off (Refill.refillBase s) 296, 8⟩] (savedAbiMem s) (linkState s).mem :=
    by
      change Frame [⟨off (Refill.refillBase s) 296, 8⟩] (savedAbiMem s)
        ((savedAbiMem s).writeW (off (Refill.refillBase s) 296) (s.gpr .x30))
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact gv.frame_in (lo := 304) (n := 80) (by decide) lf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (Refill.refillBase s) (by decide) (by decide) (by decide))

theorem link_vectors (s : State) :
    Spill.Saved (Refill.refillBase s) (vectorValues s) vectorSlots (linkState s).mem := by
  have v := Spill.saveMem_saved (l := vectorSlots) (by decide)
    (Spill.saveMem s.mem (Refill.refillBase s) s.gpr abiGprs) (Refill.refillBase s) (vectorValues s)
  have lf : Frame [⟨off (Refill.refillBase s) 296, 8⟩] (savedAbiMem s) (linkState s).mem :=
    by
      change Frame [⟨off (Refill.refillBase s) 296, 8⟩] (savedAbiMem s)
        ((savedAbiMem s).writeW (off (Refill.refillBase s) 296) (s.gpr .x30))
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact v.frame_in (lo := 384) (n := 64) (by decide) lf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (Refill.refillBase s) (by decide) (by decide) (by decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.EntryRestore`, which only this module used -/

section

/-! Restore every AAPCS64 preserved register from its protected slot. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure RestoredEntry (s t u : State) : Prop where
  gprs : ∀ r ∈ preserved, u.gpr r = s.gpr r
  vectors : ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64
  memory : u.mem = t.mem
  stack : u.sp = t.sp
  read : u.rd = t.rd
  write : u.wr = t.wr
  result : u.gpr .x0 = t.gpr .x0

theorem entryRestore_ok {s t : State}
    (sp : t.sp = Refill.refillBase s)
    (read : ∀ d, d + 8 ≤ 480 → InRegions (t.rd ++ t.wr) (Refill.refillBase s + BitVec.ofNat 64 d) 8)
    (g : Spill.Saved (Refill.refillBase s) s.gpr abiGprs t.mem)
    (v : Spill.Saved (Refill.refillBase s) (vectorValues s) vectorSlots t.mem)
    (lr : t.mem.readW (Refill.refillBase s + BitVec.ofNat 64 296) 64 = s.gpr .x30) :
    WP isa (.block entryRestore) t (RestoredEntry s t) := by
  simp only [entryRestore, abiGprs, abiVectors, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append]
  brun [exec_ldrSp (off := 304) (by decide),
    exec_ldrSp (off := 312) (by decide),
    exec_ldrSp (off := 320) (by decide),
    exec_ldrSp (off := 328) (by decide),
    exec_ldrSp (off := 336) (by decide),
    exec_ldrSp (off := 344) (by decide),
    exec_ldrSp (off := 352) (by decide),
    exec_ldrSp (off := 360) (by decide),
    exec_ldrSp (off := 368) (by decide),
    exec_ldrSp (off := 376) (by decide),
    exec_ldrSp (off := 384) (by decide),
    exec_ldrSp (off := 392) (by decide),
    exec_ldrSp (off := 400) (by decide),
    exec_ldrSp (off := 408) (by decide),
    exec_ldrSp (off := 416) (by decide),
    exec_ldrSp (off := 424) (by decide),
    exec_ldrSp (off := 432) (by decide),
    exec_ldrSp (off := 440) (by decide),
    exec_ldrSp (off := 296) (by decide),
    exec_ins (by decide : 0 < 2),
    sp,
    read 304 (by decide),
    read 312 (by decide),
    read 320 (by decide),
    read 328 (by decide),
    read 336 (by decide),
    read 344 (by decide),
    read 352 (by decide),
    read 360 (by decide),
    read 368 (by decide),
    read 376 (by decide),
    read 384 (by decide),
    read 392 (by decide),
    read 400 (by decide),
    read 408 (by decide),
    read 416 (by decide),
    read 424 (by decide),
    read 432 (by decide),
    read 440 (by decide),
    read 296 (by decide),
    g ⟨.x19, 304⟩ (by decide),
    g ⟨.x20, 312⟩ (by decide),
    g ⟨.x21, 320⟩ (by decide),
    g ⟨.x22, 328⟩ (by decide),
    g ⟨.x23, 336⟩ (by decide),
    g ⟨.x24, 344⟩ (by decide),
    g ⟨.x25, 352⟩ (by decide),
    g ⟨.x26, 360⟩ (by decide),
    g ⟨.x27, 368⟩ (by decide),
    g ⟨.x28, 376⟩ (by decide),
    v ⟨.x0, 384⟩ (by decide),
    v ⟨.x1, 392⟩ (by decide),
    v ⟨.x2, 400⟩ (by decide),
    v ⟨.x3, 408⟩ (by decide),
    v ⟨.x4, 416⟩ (by decide),
    v ⟨.x5, 424⟩ (by decide),
    v ⟨.x6, 432⟩ (by decide),
    v ⟨.x7, 440⟩ (by decide),
    lr,
    vectorValues,
    laneOf,
    State.write,
    State.setV]
  refine ⟨?_, ?_, rfl, sp.symm, rfl, rfl, rfl⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    all_goals exact extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.EntryLink`, which only this module used -/

section

/-! Save the incoming link register outside the persistent generation words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem link_frame (s : State) : Frame [linkRegion s] s.mem (linkState s).mem := by
  have gp := Spill.saveMem_frame (l := Impl.Dsa.AArch64.Generation.abiGprs) (lo := 296) (n := 152)
    (by decide) (by decide) s.mem (Refill.refillBase s) s.gpr
  have vp := Spill.saveMem_frame (l := vectorSlots) (lo := 296) (n := 152)
    (by decide) (by decide)
    (Spill.saveMem s.mem (Refill.refillBase s) s.gpr Impl.Dsa.AArch64.Generation.abiGprs)
    (Refill.refillBase s) (vectorValues s)
  have ff : Frame [linkRegion s] s.mem (savedAbiMem s) := gp.trans vp
  have hc : (linkRegion s).Contains (linkRegion s).base 8 := by
    have hc := Offset.contains_base (off (Refill.refillBase s) 296) (d := 0) (n := 8) (k := 152)
      (by decide) (by decide)
    simpa only [linkRegion, off, BitVec.add_zero] using hc
  exact ff.writeW (r := linkRegion s) (by simp) (s.gpr .x30) hc

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The refillable-tape search on AArch64 meets its contract's functional part

The entry, the search for the width in `state[1]` (the controller and its
end), and the restored registers (`refill_correct`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Proof.Dsa.AArch64.Generation

/-! ## The words written -/

theorem written_state (m : Mem) {St U : Addr} (hd : (⟨U, 8⟩ : Region).Disjoint ⟨St, 32⟩) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) St 4 =
      [r0, m.readW (St + BitVec.ofNat 64 8) 64, m.readW (St + BitVec.ofNat 64 16) 64, r3] := by
  have hf : Frame [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m (written m St U r0 r3 uv) := by
    unfold written
    exact (((Frame.refl [⟨St, 8⟩, ⟨off St 24, 8⟩, ⟨U, 8⟩] m).writeW (List.mem_cons_self ..) r0
      (Region.contains_self St 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) r3 (Region.contains_self (off St 24) 8)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) uv (Region.contains_self U 8)
  have mid : ∀ d, 8 ≤ d → d + 8 ≤ 24 → (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 d) 64 =
      m.readW (St + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base St h₁ (by omega_using [h₂])
      · exact Offset.disjoint St (d := d) (e := 24) (by omega_using [h₂]) (by omega_using [h₂]) (by omega_using [])
      · exact (hd.symm.sub_left (Offset.sub_base St (by omega_using [h₂]))) ) (by decide)
  have uSt : Mem.Sep St 8 U 8 := hd.symm.sep (contains_head _ (by decide)) (contains_head _ (by decide))
  have uSt24 : Mem.Sep (off St 24) 8 U 8 := hd.symm.sep (Offset.contains_base _ (by decide) (by decide))
    (contains_head _ (by decide))
  change [(written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 0) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 8) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 16) 64,
    (written m St U r0 r3 uv).readW (St + BitVec.ofNat 64 24) 64] = _
  rw [mid 8 (by decide) (by decide), mid 16 (by decide) (by decide), show St + BitVec.ofNat 64 0 = St from BitVec.add_zero St]
  unfold written
  rw [Mem.readW_writeW_sep uSt (by decide), Mem.readW_writeW_sep (Offset.sep_base St (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64, show St + BitVec.ofNat 64 24 = off St 24 from rfl, Mem.readW_writeW_sep uSt24 (by decide),
    Mem.readW_writeW_self64]

theorem written_used (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) :
    Spec.Rsa.wordsAt (written m St U r0 r3 uv) U 1 = [uv] := by
  change [(written m St U r0 r3 uv).readW (U + BitVec.ofNat 64 0) 64] = _
  rw [show U + BitVec.ofNat 64 0 = U from BitVec.add_zero U]
  exact congrArg (· :: []) (Mem.readW_writeW_self64 _ _ _)

theorem wordsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) (hn : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (d := 8 * i) (n := 8) (k := 8 * n) (by omega_using [hi]) (by omega_using [hn, hi])) hd (by decide)

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- The saved registers' slots. -/
def savedRegion : Region := ⟨off (refillBase s₀) 296, 152⟩

/-- What the entry and the search may write. -/
def bodyRegions : List Region :=
  ⟨refillBase s₀, frameBytes⟩ :: ctlRegion (refillBase s₀) :: (refillContext h).changed ++ [inState s₀, inUsed s₀, inOut s₀]

theorem saved_body : ∀ r ∈ bodyRegions h, (savedRegion (s₀ := s₀)).Disjoint r := by
  intro r hr
  simp only [bodyRegions, GenerationContext.changed, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  have st : ∀ {q : Region}, (q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inRand s₀ ∨ q = inScr s₀ ∨ q = inState s₀) →
      (savedRegion (s₀ := s₀)).Disjoint q := fun hq => (h.frame_disjoint hq (by decide)).symm
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base (refillBase s₀) (by decide) (by have := refillBase_bound h; omega_using [])
  · exact Offset.disjoint (refillBase s₀) (d := 296) (e := 448) (by omega_using []) (by omega_using []) (by omega_using [])
  · exact (st (by simp)).sub_right h.arena_sub
  · exact Offset.disjoint_base (refillBase s₀) (by decide) (by have := refillBase_bound h; omega_using [])
  · exact Offset.disjoint_below (refillBase s₀) (by omega_using [])
  · exact st (by simp)
  · exact st (by simp)
  · exact st (by simp)

/-- The search's results. -/
def SearchPost (u t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (s₀.gpr .x1).toNat 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 8) 64, s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h))] ∧
  Frame (bodyRegions h) u.mem t.mem ∧ t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr

/-- What the entry and the controller may write. -/
def priorRegions : List Region :=
  savedRegion (s₀ := s₀) :: ⟨refillBase s₀, frameBytes⟩ :: ctlRegion (refillBase s₀) :: (refillContext h).changed

theorem buffer_prior {q : Region} (hq : q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inState s₀) :
    ∀ r ∈ priorRegions h, q.Disjoint r := by
  have hq' : q = inOut s₀ ∨ q = inUsed s₀ ∨ q = inRand s₀ ∨ q = inScr s₀ ∨ q = inState s₀ := by
    rcases hq with e | e | e <;> simp [e]
  have scr : q.Disjoint (inScr s₀) := by
    rcases hq with rfl | rfl | rfl
    · exact h.outScr
    · exact h.usedScr
    · exact h.scrState.symm
  intro r hr
  simp only [priorRegions, savedRegion, GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.frame_disjoint hq' (by decide)
  · simpa only [off, BitVec.add_zero] using h.frame_disjoint hq' (d := 0) (n := frameBytes) (by decide)
  · exact h.frame_disjoint hq' (by decide)
  · exact scr.sub_right h.arena_sub
  · show q.Disjoint ⟨refillBase s₀, frameBytes⟩
    simpa only [off, BitVec.add_zero] using h.frame_disjoint hq' (d := 0) (n := frameBytes) (by decide)
  · change q.Disjoint (below (refillBase s₀) 272)
    rw [refillBase_below s₀ (by decide)]
    exact (h.stack_disjoint (by decide) hq').symm

theorem search_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {W : Nat → BitVec 64} {u : State}
    (E : EntryDone h W u)
    (fs : Frame [savedRegion (s₀ := s₀), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem u.mem) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.search H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) u (SearchPost h u) := by
  have hA : AttemptOk h (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) :=
    fun hs W t seed hin hm hlen hseed h1 used h16 hu => refillAttempt_ok H G T hm hin seed hlen hseed h1 h16 hu
  simp only [Impl.Dsa.AArch64.Generation.Refill.search, Impl.Dsa.AArch64.Generation.Refill.controller,
    VG.Impl.Bignum.AArch64.seqs]
  apply WP.seq
  refine WP.mono (widthHeader_ok E rfl) fun v ⟨hm, h16, h10, c0, c1, c2, fv, kv⟩ => ?_
  have wv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kv.wr.trans E.wr
  apply WP.seq
  refine WP.mono (controller_ok h hA (by rw [wv]; exact List.mem_cons_self ..) _ _ v
    (loop_initial h hm (by simpa [upd] using h16) (by simpa [upd] using h10) c0 c1 c2)) fun t ⟨_, _, hd⟩ => ?_
  refine WP.mono (finish_ok h wv hd) fun t' F' => ?_
  obtain ⟨m₁, r0, r3, uv, fm₁, e0, e3, eu, ft, x0, bytes, sp', rd', wr'⟩ := F'
  have fs₁ : Frame (priorRegions h) s₀.mem m₁ := by
    have a : Frame (priorRegions h) s₀.mem u.mem := fs.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have b : Frame (priorRegions h) u.mem v.mem := fv.mono fun r hr => by
      rcases List.mem_singleton.mp hr with rfl
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have c : Frame (priorRegions h) v.mem m₁ := fm₁.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
    exact (a.trans b).trans c
  have stateM : ∀ d, d + 8 ≤ 32 → m₁.readW (s₀.gpr .x7 + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 d) 64 := fun d hd8 =>
    fs₁.readW (r := inState s₀) (Offset.contains_base _ (d := d) (n := 8) (k := 32) hd8 (by omega_using [hd8]))
      (buffer_prior h (by simp)) (by decide)
  have finalD : ∀ {q : Region}, (q = inUsed s₀ ∨ q = inState s₀) →
      ∀ r ∈ [(⟨refillBase s₀, frameBytes⟩ : Region), inOut s₀], q.Disjoint r := by
    intro q hq r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact buffer_prior h (by rcases hq with e | e <;> simp [e]) _ (by simp [priorRegions])
    · rcases hq with rfl | rfl
      · exact h.outUsed.symm
      · exact h.outState.symm
  have ctlState : ∀ {q : Region}, (q = inUsed s₀ ∨ q = inState s₀) → q.Disjoint ⟨off (refillBase s₀) 472, 8⟩ :=
    fun hq => h.frame_disjoint (by rcases hq with e | e <;> simp [e]) (by decide)
  have usedState : (⟨s₀.gpr .x2, 8⟩ : Region).Disjoint ⟨s₀.gpr .x7, 32⟩ := h.usedState
  refine ⟨x0, bytes, ?_, ?_, ?_, sp'.trans E.layout.sp.symm, rd'.trans kv.rd, wr'.trans kv.wr⟩
  · rw [wordsAt_frame ft (n := 1) (finalD (Or.inl rfl)) (by decide)]
    rw [show ∀ m x, Spec.Rsa.wordsAt (Mem.writeW m (off (refillBase s₀) 472) x) (s₀.gpr .x2) 1 =
        Spec.Rsa.wordsAt m (s₀.gpr .x2) 1 from fun m x =>
      wordsAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) x (Region.contains_self _ _))
        (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctlState (Or.inl rfl)) (by decide)]
    rw [written_used, eu]
  · rw [wordsAt_frame ft (n := 4) (finalD (Or.inr rfl)) (by decide)]
    rw [show ∀ m x, Spec.Rsa.wordsAt (Mem.writeW m (off (refillBase s₀) 472) x) (s₀.gpr .x7) 4 =
        Spec.Rsa.wordsAt m (s₀.gpr .x7) 4 from fun m x =>
      wordsAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) x (Region.contains_self _ _))
        (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctlState (Or.inr rfl)) (by decide)]
    rw [written_state _ usedState, e0, e3, stateM 8 (by decide), stateM 16 (by decide)]
  · have b : Frame (bodyRegions h) u.mem v.mem := fv.mono fun r hr => by
      rcases List.mem_singleton.mp hr with rfl
      exact List.mem_cons_self ..
    have c : Frame (bodyRegions h) v.mem m₁ := fm₁.mono fun r hr => by
      simp only [bodyRegions, List.cons_append]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hr)
    have d : Frame (bodyRegions h) m₁ t'.mem := by
      refine ((results_frame m₁ _ _ _ _ _ _ _).mono ?_).trans (ft.mono ?_)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [bodyRegions, List.cons_append]
        rcases hr with rfl | rfl | rfl
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..)))
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [bodyRegions, List.cons_append]
        rcases hr with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    exact (b.trans c).trans d
end

theorem EntryDone.congr {pBytes : Nat} {s₀ : State} {h : RefillABI pBytes s₀} {W : Nat → BitVec 64} {v t : State}
    (E : EntryDone h W v) (hm : t.mem = v.mem) (hk : Keep [.x3, .x4] v t) : EntryDone h W t := by
  obtain ⟨V, R⟩ := E.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W := hm ▸ R
  exact ⟨lay_of_rep E.layout R Rt rfl hk.sp hk.wr, ⟨V, Rt⟩, E.slots, E.w16, E.w10, E.scratch.congr hk.wr,
    ⟨by rw [hk.rd, hk.wr]; exact E.rand.cover, by rw [hm]; exact E.rand.bytes⟩,
    hk.wr.trans E.wr, hk.rd.trans E.rd, by rw [hm]; exact E.c0, by rw [hm]; exact E.c1, by rw [hm]; exact E.c2⟩

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem linkAllocated : RefillAllocated h (linkState s₀) where
  sp := rfl
  wr := rfl
  rd := rfl
  regs := fun r hr => by
    have : r ≠ .x9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [linkState, this]
  mem := link_frame s₀

/-- The body's results, with the saved registers restored. -/
def BodyPost (t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
  Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (s₀.gpr .x1).toNat 0) ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
  Spec.Rsa.wordsAt t.mem (s₀.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
    s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 8) 64, s₀.mem.readW (s₀.gpr .x7 + BitVec.ofNat 64 16) 64,
    BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h))] ∧
  (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧
  (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
  t.sp = refillBase s₀ ∧ t.rd = s₀.rd ∧ t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr

theorem body_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    WP isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 s₀) (BodyPost h) := by
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  unfold Impl.Dsa.AArch64.Generation.entryBody
  refine WP.seq (WP.mono (entrySave_ok s₀) fun u hu => ?_)
  subst hu
  have a := linkAllocated h
  refine WP.seq (WP.mono (entry_ok h a) fun v ⟨W, E, fE, kE⟩ => ?_)
  have h17 : W 17 = BitVec.ofNat 64 pBytes := E.slots 17 (by simp [generationSlots]) (by decide) (by decide)
  obtain ⟨V, R⟩ := E.rep
  apply WP.seq
  refine dispatch_ok H.sha1 H.sha256 G.run T.run E.layout R hp3 h17 fun t hm hk => ?_
  have E' := E.congr hm hk
  have fs : Frame [savedRegion (s₀ := s₀), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem t.mem := by
    rw [hm]
    exact (a.mem.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..).trans
      (fE.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.mono (search_ok h H G T E' fs) fun t₁ ⟨x0, bytes, used, words, ft, sp₁, rd₁, wr₁⟩ => ?_
  -- the saved registers
  have fl : Frame (bodyRegions h) (linkState s₀).mem t₁.mem := by
    refine (fE.mono fun r hr => ?_).trans (hm ▸ ft)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have sep := saved_body h
  have g := (link_gprs s₀).frame_in (lo := 296) (n := 152) (by decide) fl sep
  have vv := (link_vectors s₀).frame_in (lo := 296) (n := 152) (by decide) fl sep
  have lr : t₁.mem.readW (refillBase s₀ + BitVec.ofNat 64 296) 64 = s₀.gpr .x30 := by
    have hc : (savedRegion (s₀ := s₀)).Contains (off (refillBase s₀) 296) 8 := by
      have := Offset.contains_base (off (refillBase s₀) 296) (d := 0) (n := 8) (k := 152) (by decide) (by decide)
      simpa only [savedRegion, off, BitVec.add_zero] using this
    rw [fl.readW hc sep (by decide)]
    exact word_writeW_self (savedAbiMem s₀) (refillBase s₀) 296 (s₀.gpr .x30)
  have sp₁' : t₁.sp = refillBase s₀ := sp₁.trans (hk.sp.trans E.layout.sp)
  have wr₁' : t₁.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := wr₁.trans (hk.wr.trans E.wr)
  have perm (d : Nat) (hd : d + 8 ≤ 480) : InRegions (t₁.rd ++ t₁.wr) (refillBase s₀ + BitVec.ofNat 64 d) 8 := by
    rw [wr₁']
    exact ⟨⟨refillBase s₀, 480⟩, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ hd (by omega_using [hd])⟩
  refine WP.mono (entryRestore_ok sp₁' perm g vv lr) fun t₂ hv => ?_
  refine ⟨hv.result.trans x0, hv.memory ▸ bytes, hv.memory ▸ used, hv.memory ▸ words, hv.gprs, hv.vectors,
    hv.stack.trans sp₁', hv.read.trans (rd₁.trans (hk.rd.trans E.rd)), hv.write.trans wr₁'⟩

end

/-! ## Correctness -/

theorem refill_correct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (s : State) (pre : (Spec.Dsa.parameterSearchContract abi refillStack).pre s) :
    ∃ tr t, Exec isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) s tr t ∧
      abiPreserved s t ∧ (Spec.Dsa.parameterSearchContract abi refillStack).post s t := by
  have h := refillABI_of pre
  obtain ⟨tr, t, he, x0, bytes, used, words, gp, vp, tsp⟩ :
      WP isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) s fun t =>
        t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
          ((expectedOf (total h)).map (Spec.Dsa.encodeParams (refillPLen s)
            (Spec.Dsa.generationQLen (refillPLen s)))).getD (List.replicate (s.gpr .x1).toNat 0) ∧
        Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
        Spec.Rsa.wordsAt t.mem (s.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
          s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64, s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 16) 64,
          BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested (refillPLen s) (total h))] ∧
        (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
        (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ t.sp = s.sp := by
    unfold Impl.Dsa.AArch64.Generation.code
    apply alloc_frame_ok (bytes := 480) (by decide) (by have := h.stackLower; unfold refillStack at this; omega_using [this])
    refine WP.mono (body_ok h H G T) ?_
    intro t ⟨x0, bytes, used, words, gp, vp, sp, _, wr⟩
    refine ⟨by simp only [allocState]; exact sp, by simp only [allocState]; exact wr, ?_⟩
    simp only [freeState]
    refine ⟨x0, bytes, used, words, gp, vp, ?_⟩
    change t.sp + BitVec.ofNat 64 480 = s.sp
    rw [sp]; exact BitVec.sub_add_cancel ..
  refine ⟨tr, t, he, ⟨gp, tsp, vp⟩, ?_⟩
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  have ht : Spec.Dsa.parameterSearch (refillPLen s) (s.mem.readW (s.gpr .x7) 64).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = total h := rfl
  have w8 : s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (refillPLen s) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  have w16 : s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 16) 64 =
      BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s)) := h.budget
  have hp : 0 < refillPLen s := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  change (BitVec.setWidth 32 (t.gpr .x0)).toNat = (total h).status ∧
    (Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat = match (total h).outcome with
      | .accepted a => Spec.Dsa.encodeParams (refillPLen s) (Spec.Dsa.generationQLen (refillPLen s)) a
      | _ => List.replicate (s.gpr .x1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 (total h).used] ∧
      ∃ requested, Spec.Rsa.wordsAt t.mem (s.gpr .x7) 4 = [BitVec.ofNat 64 (total h).remaining,
        BitVec.ofNat 64 (refillPLen s), BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s)),
        BitVec.ofNat 64 requested] ∧ (total h).Requests (Spec.Dsa.parameterEntropy (refillPLen s)) requested
  refine ⟨?_, ?_, used, VG.Proof.Dsa.Generation.requested (refillPLen s) (total h), ?_,
    VG.Proof.Dsa.Generation.requested_requests hp _ _⟩
  · have hs : (total h).status < 4 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    rw [x0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hs]), Nat.mod_eq_of_lt (by omega_using [hs])]
  · rw [bytes]
    unfold expectedOf
    generalize (total h).outcome = o
    cases o <;> rfl
  · rw [words, w8, w16]

end VG.Proof.Dsa.AArch64.Generation.Refill
