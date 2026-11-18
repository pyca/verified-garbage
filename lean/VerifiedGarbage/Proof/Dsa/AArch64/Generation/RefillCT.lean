module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTFinish
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCTFinish
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Dsa.ParameterSearch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillEntry
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.StackStore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Spec.Dsa.ParameterSearch

/-! ### `Dsa.AArch64.Generation.RefillCorrect`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.Dispatch`, which this module and modules that import it used -/

section

/-! # The search for the width in `W 17`, one of the three the specification allows -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem lengthTest_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128]) s fun t =>
      t.gpr .x3 = W 17 ∧ eval (.zero .x .x4) t = some (W 17 == 128#64) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hw : s.mem.readW (F + BitVec.ofNat 64 136) 64 = W 17 := R.fr 17 (by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = W 17 ∧ eval (.zero .x .x4) t = some (W 17 == 128#64) ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (off := 136) (by decide), L.sp, L.ld (d := 136) (n := 8) (by decide), hw, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change W 17 = (128#64) ↔ W 17 = (128#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨ha, hz, hm⟩, hk⟩ => ⟨ha, hz, hm, hk⟩

theorem lengthTest256_ok {s : State} :
    WP isa (.block [.subImm .x .x4 .x3 256]) s fun t =>
      eval (.zero .x .x4) t = some (s.gpr .x3 == 256#64) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    eval (.zero .x .x4) t = some (s.gpr .x3 == 256#64) ∧ t.mem = s.mem) (by
    brun [eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change s.gpr .x3 = (256#64) ↔ s.gpr .x3 = (256#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem dispatch_ok (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (gen : Nat → Prog isa) (round : Nat → Prog isa)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {Q : State → Prop}
    (L : Lay s F S) (R : Rep s.mem F S V W) {pBytes : Nat} (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384)
    (h17 : W 17 = BitVec.ofNat 64 pBytes)
    (run : ∀ t, t.mem = s.mem → Keep [.x3, .x4] s t →
      WP isa (Impl.Dsa.AArch64.Generation.Refill.search G1 G256 gen round pBytes (Spec.Dsa.generationQLen pBytes)) t Q) :
    WP isa (Impl.Dsa.AArch64.Generation.dispatch G1 G256 gen round) s Q := by
  unfold Impl.Dsa.AArch64.Generation.dispatch
  refine WP.seq (WP.mono (lengthTest_ok L R) fun u ⟨ha, hz, hm, ku⟩ => ?_)
  rw [h17] at ha hz
  rcases hp with rfl | rfl | rfl
  · refine WP.ite true (by apply hz.trans; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    exact run u hm ku
  · refine WP.ite false (by apply hz.trans; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite true (by apply hzv.trans; rw [ha]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    exact run v (hmv.trans hm) ((ku.trans kv).mono (by decide))
  · refine WP.ite false (by apply hz.trans; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono lengthTest256_ok fun v ⟨hzv, hmv, kv⟩ => ?_)
    refine WP.ite false (by apply hzv.trans; rw [ha]; rfl) (fun he => Bool.noConfusion he) (fun _ => ?_)
    exact run v (hmv.trans hm) ((ku.trans kv).mono (by decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

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
    intro t ⟨x0, bytes, used, words, gp, vp, sp, _, wr⟩ m u f
    -- The frame's bytes are lost; the outputs are apart from them.
    have hA : Region.Sub ⟨s.sp - BitVec.ofNat 64 480, 480⟩ (below s.sp refillStack) :=
      below_sub (by decide) (by decide)
    have eW : ∀ {R : Region} {n : Nat}, (below s.sp refillStack).Disjoint R → 8 * n ≤ R.len → R.len < 2 ^ 64 →
        Spec.Rsa.wordsAt m R.base n = Spec.Rsa.wordsAt t.mem R.base n := by
      intro R n hd hk hk2
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      exact f.readW (r := R) (Offset.contains_base _ (by omega_using [hi, hk]) (by omega_using [hi, hk, hk2]))
        (fun R' hR' => by obtain rfl := List.mem_singleton.mp hR'; exact hd.symm.sub_right hA) (by decide)
    refine ⟨x0, (List.map_congr_left fun i hi => lost_byte f (h.stackOut.symm.sub_right hA)
        (List.mem_range.mp hi)).trans bytes,
      (eW (R := inUsed s) h.stackUsed (by simp only [inUsed]; decide) (by simp only [inUsed]; decide)).trans used,
      (eW (R := inState s) h.stackState (by simp only [inState]; decide) (by simp only [inState]; decide)).trans words, gp, vp, ?_⟩
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

end

end

-- separate module: its proofs build in parallel with the correctness ones, `RefillCorrect`

/-! # The refillable-tape search on AArch64 is constant time

`refill_ct`: two runs from states whose public data agree (the arguments
in registers, the stack pointer, `state`'s four words and the whole tape
`rand`) leak the same trace. The search's public state on entry
(`EntryPub`) is a function of that data (`entryPub_eq`); the entry, the
dispatch on the width, the controller (`controller_ct`) and the end
(`finish_ct`) keep the two runs' states related. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (upd)
open VG.Proof.Dsa.AArch64.Generation

/-! ## Public data -/

/-- What two runs' public data agree on. -/
structure RefillAgree (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s.gpr r = t.gpr r
  seeds : (s.mem.readW (s.gpr .x7) 64).toNat = (t.mem.readW (t.gpr .x7) 64).toNat
  width : refillPLen s = refillPLen t
  rand : Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat

theorem refill_wordsAt_four (m : Mem) (p : Addr) : (Spec.Rsa.wordsAt m p 4).map (·.toNat) =
    [(m.readW (p + BitVec.ofNat 64 0) 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat,
      (m.readW (p + 24) 64).toNat] := rfl

theorem refill_agree {s t : State} (h : (Spec.Dsa.parameterSearchContract abi refillStack).pub s t) :
    RefillAgree s t := by
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [refill_wordsAt_four, refill_wordsAt_four] at hl
  have hp := List.append_inj hl (by simp only [List.length_cons, List.length_nil])
  simp only [List.cons.injEq] at hp
  refine ⟨hsp, ?_, by simpa only [BitVec.add_zero] using hp.1.1, hp.1.2.1,
    (List.map_inj_right fun a b e => BitVec.eq_of_toNat_eq e).mp hp.2⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem GenerationTape.heq_of {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg; cases a; cases b; cases hp; cases hb; rfl

theorem GenerationContext.ext' {a b : GenerationContext} (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds)
    (hh : HEq a.hs b.hs) (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a; cases b; cases hg; cases hs; cases hh; cases hr; cases hw; rfl

theorem refillContext_eq {pBytes : Nat} {s t : State} (hs : RefillABI pBytes s) (ht : RefillABI pBytes t)
    (a : RefillAgree s t) : refillContext hs = refillContext ht := by
  have hg : refillGeometry hs = refillGeometry ht := by
    have ext : ∀ {x y : GenerationGeometry}, x.B = y.B → x.F = y.F → x.pLen = y.pLen → x.qLen = y.qLen → x = y := by
      intro x y hB hF hp hq
      cases x; cases y
      dsimp only at hB hF hp hq
      subst hB; subst hF; subst hp; subst hq; rfl
    exact ext (a.regs .x5 (by simp)) (by simp only [refillGeometry, refillBase, a.sp]) rfl rfl
  have tape : HEq (randTape hs) (randTape ht) :=
    GenerationTape.heq_of hg (a.regs .x3 (by simp)) a.rand
  refine GenerationContext.ext' hg tape ?_ tape ?_
  · refine GenerationTape.heq_of hg ?_ ?_
    · show off (s.gpr .x3) 0 = off (t.gpr .x3) 0
      rw [a.regs .x3 (by simp)]
    · show ((randTape hs).bytes.drop 0).take 0 = ((randTape ht).bytes.drop 0).take 0
      simp only [List.take_zero]
  · funext k
    show refillWords pBytes s k = refillWords pBytes t k
    unfold refillWords
    split <;> simp only [a.regs .x0 (by simp), a.regs .x1 (by simp), a.regs .x3 (by simp),
      a.regs .x4 (by simp), a.regs .x5 (by simp)]

/-! ## The entry -/

/-- The search's public state on entry. -/
structure EntryPub where
  pBytes : Nat
  ctx : GenerationContext
  n₀ : Nat
  st : BitVec 64
  us : BitVec 64

def entryPub {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) : EntryPub :=
  ⟨pBytes, refillContext h, (s₀.mem.readW (s₀.gpr .x7) 64).toNat, s₀.gpr .x7, s₀.gpr .x2⟩

def EntryAt (E : EntryPub) (u : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI E.pBytes s₀), RefillAllocated h u ∧ refillContext h = E.ctx ∧
    s₀.gpr .x7 = E.st ∧ s₀.gpr .x2 = E.us ∧ (s₀.mem.readW (s₀.gpr .x7) 64).toNat = E.n₀

def Entered (E : EntryPub) (v : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI E.pBytes s₀) (W : Nat → BitVec 64), EntryDone h W v ∧ refillContext h = E.ctx ∧
    s₀.gpr .x7 = E.st ∧ s₀.gpr .x2 = E.us ∧ (s₀.mem.readW (s₀.gpr .x7) 64).toNat = E.n₀

theorem entered_wp {E : EntryPub} {u : State} (hi : EntryAt E u) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived)) u
      (Entered E) := by
  obtain ⟨s₀, h, a, hc, p7, p2, hn⟩ := hi
  exact WP.mono (entry_ok h a) fun v ⟨W, D, _, _⟩ => ⟨s₀, h, W, D, hc, p7, p2, hn⟩

/-- The width's search, from the entry's words. -/
theorem search_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pLen : Nat)
    (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun E v => Entered E v ∧ E.pBytes = pLen)
      (Impl.Dsa.AArch64.Generation.Refill.search H.sha1 H.sha256 G.run T.run pLen (Spec.Dsa.generationQLen pLen))
      (Two fun (_ : Unit) (_ : State) => True) := by
  have sizes : GenerationSizes pLen (Spec.Dsa.generationQLen pLen) := by
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have header : ∀ (E : EntryPub) (v : State), Entered E v ∧ E.pBytes = pLen →
      WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader (Spec.Dsa.generationQLen pLen))) v
        (LoopAt pLen ⟨E.ctx, E.n₀, 0, E.st, E.us⟩) := by
    rintro ⟨pB, ctx, n₀, st, us⟩ v ⟨⟨s₀, h, W, D, hc, p7, p2, hn⟩, hpl⟩
    change pB = pLen at hpl
    subst hpl
    refine WP.mono (widthHeader_ok D rfl) fun w ⟨hm, h16, h10, c0, c1, c2, _, kw⟩ => ?_
    have l := loop_initial h hm (v := w) (by simpa [upd] using h16) (by simpa [upd] using h10) c0 c1 c2
    change (s₀.mem.readW (s₀.gpr .x7) 64).toNat = n₀ at hn
    rw [hn] at l
    exact ⟨s₀, h, w, hc, ⟨p7, p2⟩, kw.wr.trans D.wr, l⟩
  unfold Impl.Dsa.AArch64.Generation.Refill.search
  simp only [VG.Impl.Bignum.AArch64.seqs]
  have hq : Spec.Dsa.generationQLen pLen = 20 ∨ Spec.Dsa.generationQLen pLen = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have ht : ∃ hc, (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader (Spec.Dsa.generationQLen pLen))) hc).isSome = true := by
    rcases hq with hq | hq <;> rw [hq] <;> exact ⟨_, by taint_decide⟩
  refine RelCT.seq (two_map (fun E : EntryPub => (⟨E.ctx, E.n₀, 0, E.st, E.us⟩ : LoopPub)) (Φ' := fun P v => ∃ E,
      (⟨E.ctx, E.n₀, 0, E.st, E.us⟩ : LoopPub) = P ∧ Entered E v ∧ E.pBytes = pLen) (fun E v h => ⟨E, rfl, h⟩) ?_)
    (RelCT.seq (controller_ct H G T pLen sizes) (two_sp (finish_ct pLen hp)))
  exact two_piece [] (nopin _) ht.choose_spec fun P v ⟨E, e, hE⟩ => e ▸ header E v hE

/-- After the width test against `len`. -/
def Tested (len : Nat) (E : EntryPub) (t : State) : Prop :=
  Entered E t ∧ isa.eval (.zero .x .x4) t = some (BitVec.ofNat 64 E.pBytes == BitVec.ofNat 64 len)

theorem Entered.congr {E : EntryPub} {v t : State} (he : Entered E v) (hm : t.mem = v.mem)
    (hk : Keep [.x3, .x4] v t) : Entered E t := by
  obtain ⟨s₀, h, W, D, rest⟩ := he
  exact ⟨s₀, h, W, D.congr hm hk, rest⟩

theorem Entered.lengths {E : EntryPub} {v : State} (he : Entered E v) :
    E.pBytes = 128 ∨ E.pBytes = 256 ∨ E.pBytes = 384 := by
  obtain ⟨s₀, h, -⟩ := he
  have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]

theorem tested128_wp {E : EntryPub} {u : State} (he : Entered E u) :
    WP isa (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128]) u fun t =>
      Tested 128 E t ∧ t.gpr .x3 = BitVec.ofNat 64 E.pBytes := by
  have he' := he
  obtain ⟨s₀, h, W, D, -⟩ := he
  obtain ⟨V, R⟩ := D.rep
  have h17 : W 17 = BitVec.ofNat 64 E.pBytes := D.slots 17 (by simp [generationSlots]) (by decide) (by decide)
  exact WP.mono (lengthTest_ok D.layout R) fun t ⟨x3, ev, hm, hk⟩ =>
    ⟨⟨he'.congr hm hk, ev.trans (by rw [h17])⟩, x3.trans h17⟩

theorem tested_ne {len : Nat} {E : EntryPub} {t : State} (h : Tested len E t)
    (hb : isa.eval (.zero .x .x4) t = some false) : E.pBytes ≠ len := by
  intro e
  have e' := Option.some.inj (h.2.symm.trans hb)
  rw [e] at e'
  simp at e'

theorem tested256_wp {E : EntryPub} {u : State}
    (he : (Tested 128 E u ∧ u.gpr .x3 = BitVec.ofNat 64 E.pBytes) ∧ isa.eval (.zero .x .x4) u = some false) :
    WP isa (.block [.subImm .x .x4 .x3 256]) u fun t => Tested 256 E t ∧ E.pBytes ≠ 128 := by
  have n := tested_ne he.1.1 he.2
  obtain ⟨⟨⟨e, -⟩, x3⟩, -⟩ := he
  exact WP.mono lengthTest256_ok fun t ⟨ev, hm, hk⟩ =>
    ⟨⟨e.congr hm hk, ev.trans (by rw [x3])⟩, n⟩

theorem tested_eq {len : Nat} {E : EntryPub} {t : State} (h : Tested len E t)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (hb : isa.eval (.zero .x .x4) t = some true) : E.pBytes = len := by
  have e := Option.some.inj (h.2.symm.trans hb)
  have hp := h.1.lengths
  rw [beq_iff_eq] at e
  rcases hp with h₁ | h₁ | h₁ <;> rcases hl with h₂ | h₂ | h₂ <;> rw [h₁, h₂] at e ⊢ <;> first | rfl | cases e

theorem dispatch_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    RelCT isa (Two Entered) (Impl.Dsa.AArch64.Generation.dispatch H.sha1 H.sha256 G.run T.run)
      (Two fun (_ : Unit) (_ : State) => True) := by
  unfold Impl.Dsa.AArch64.Generation.dispatch
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested128_wp h)
    (two_ite (fun _ _ _ hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_)
  · exact two_map id (fun E v h => ⟨h.1.1.1, tested_eq h.1.1 (Or.inl rfl) h.2⟩) (search_ct H G T 128 (Or.inl rfl))
  · refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested256_wp h)
      (two_ite (fun _ _ _ hs ht => hs.1.2.trans ht.1.2.symm) ?_ ?_)
    · exact two_map id (fun E v h => ⟨h.1.1.1, tested_eq h.1.1 (Or.inr (Or.inl rfl)) h.2⟩)
        (search_ct H G T 256 (Or.inr (Or.inl rfl)))
    · refine two_map id (fun E v h => ⟨h.1.1.1, ?_⟩) (search_ct H G T 384 (Or.inr (Or.inr rfl)))
      have n256 := tested_ne h.1.1 h.2
      rcases h.1.1.1.lengths with e | e | e
      · exact absurd e h.1.2
      · exact absurd e n256
      · exact e

/-! ## The function -/

theorem saves_ct : RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Dsa.AArch64.Generation.entrySave)
    (fun _ _ => True) := by
  apply (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] (nopin _) (by taint_decide)).mono
  · intro s t h
    exact ⟨(), True.intro, True.intro, h⟩
  · exact fun _ _ _ => True.intro

theorem tail_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    RelCT isa (Two EntryAt)
      (.seq (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived))
        (.seq (Impl.Dsa.AArch64.Generation.dispatch H.sha1 H.sha256 G.run T.run)
          (.block Impl.Dsa.AArch64.Generation.entryRestore))) (fun _ _ => True) :=
  RelCT.seq (two_piece [.x7] (fun E s t ⟨_, _, a, _, p, _⟩ ⟨_, _, a', _, p', _⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [a.regs .x7 (by simp), a'.regs .x7 (by simp), p, p']) (by taint_decide) fun _ _ h => entered_wp h)
    (RelCT.seq (dispatch_ct H G T) (two_taint [] (nopin _) (by taint_decide)))

theorem saved_state {s t : State} {tr : List Leak}
    (h : Exec isa (.block Impl.Dsa.AArch64.Generation.entrySave) (allocState 480 s) tr t) : t = linkState s := by
  obtain ⟨_, u, e, hu⟩ := entrySave_ok s
  obtain ⟨_, rfl⟩ := Exec.det h e
  exact hu

theorem body_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {s t u v : State}
    (hs : (Spec.Dsa.parameterSearchContract abi refillStack).pre s)
    (ht : (Spec.Dsa.parameterSearchContract abi refillStack).pre t) (agree : RefillAgree s t) {xs ys : List Leak}
    (es : Exec isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 s) xs u)
    (et : Exec isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 G.run T.run) (allocState 480 t) ys v) :
    xs = ys := by
  have ha := refillABI_of hs
  have hb : RefillABI (refillPLen s) t := by rw [agree.width]; exact refillABI_of ht
  have hsp : s.sp - BitVec.ofNat 64 480 = t.sp - BitVec.ofNat 64 480 := by rw [agree.sp]
  cases es with
  | seq sa ba =>
    cases et with
    | seq sb bb =>
      have saves := (saves_ct _ _ _ _ _ _ hsp sa sb).1
      obtain rfl := saved_state sa
      obtain rfl := saved_state sb
      have E₁ : EntryAt (entryPub ha) (linkState s) := ⟨s, ha, linkAllocated ha, rfl, rfl, rfl, rfl⟩
      have E₂ : EntryAt (entryPub ha) (linkState t) :=
        ⟨t, hb, linkAllocated hb, (refillContext_eq ha hb agree).symm, (agree.regs .x7 (by simp)).symm,
          (agree.regs .x2 (by simp)).symm, agree.seeds.symm⟩
      have tail := (tail_ct H G T _ _ _ _ _ _ ⟨entryPub ha, E₁, E₂, hsp⟩ ba bb).1
      exact congrArg₂ List.append saves tail

theorem refill_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) :
    ConstantTime isa (Spec.Dsa.parameterSearchContract abi refillStack).pre
      (Spec.Dsa.parameterSearchContract abi refillStack).pub
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (Spec.Dsa.parameterSearchContract abi refillStack).pre s ∧
      (Spec.Dsa.parameterSearchContract abi refillStack).pre t ∧ RefillAgree s t)
      (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 G.run T.run) (fun _ _ => True) := by
    apply RelCT.alloc
    rintro a b xa xb u v ⟨s, t, ⟨hs, ht, hp⟩, rfl, rfl⟩ ea eb
    exact ⟨body_ct H G T hs ht hp ea eb, True.intro⟩
  exact (ct _ _ _ _ _ _ ⟨hs, ht, refill_agree hp⟩ es et).1

end VG.Proof.Dsa.AArch64.Generation.Refill
