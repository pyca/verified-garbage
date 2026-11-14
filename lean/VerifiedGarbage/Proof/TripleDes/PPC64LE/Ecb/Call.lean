module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Block
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit

/-! ### `TripleDes.PPC64LE.Pre`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 384⟩
    let data : Region := ⟨s.gpr .r4, 8⟩
    let scratch : Region := ⟨s.gpr .r5, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d (Spec.TripleDes.blockAt s.mem (s.gpr .r4))
  pub := PublicRegs [.r3, .r4, .r5]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`x2` writable, the schedule at `x0` readable and the block at `x1`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .r4) 8)
    (keySep : Region.Disjoint ⟨s.gpr .r3, 384⟩ ⟨s.gpr .r5, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .r4, 8⟩ ⟨s.gpr .r5, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have scratch : Ok scratchCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .r3) c) direction j, 8⟩ ⟨s.gpr .r3, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .r5, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .r5, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨scratch, rfl, (fun i hi => inRd (scratchWrites i (by omega_using [hi]))),
    (fun i hi => scratchWrites i (by omega_using [hi])), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .r3) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)))
      (s.gpr .r3) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  refine headPre_of s (fun i hi => ?_) (fun i hi => ?_) ?_ keySep dataSep
  · rw [hwr]
    exact ⟨⟨s.gpr .r5, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .r3, 384⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hwr]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩


end VG.Proof.TripleDes.PPC64LE

end

end


/-! # A call of the block function from the modes and CMAC on PPC64LE -/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Ecb

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

/-- The argument registers the block functions keep. -/
def kept : List Reg := [.r3, .r4, .r5]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have hwrite : InRegions s.wr (s.gpr .r4) 8 := by
    rw [hs.2.1]
    exact ⟨⟨s.gpr .r4, 8⟩, by simp, Region.contains_self _ _⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3))
    (s.gpr .r3) d s hp hwrite
  have hlr : s'.lr = s.lr := by
    cases d
    · exact Exec.lr (c := encryptBlock) he (by lit_decide) (by lit_decide)
    · exact Exec.lr (c := decryptBlock) he (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨?_, Exec.sp he, hlr⟩, post.result, ?_⟩
  · intro r hr
    have hkeep : ∀ q ∈ preserved, q ∈ savedRegs ∨ q ∈ loadKept := by decide
    rcases hkeep r hr with h | h
    · exact post.saved r h
    · exact post.regs r h
  · intro r hr
    exact post.regs r (by revert hr; decide +revert)

/-- The name of the block function of the direction `d`. -/
def blockName : Spec.TripleDes.Direction → String
  | .encrypt => "vg_triple_des_encrypt_block"
  | .decrypt => "vg_triple_des_decrypt_block"

theorem blockCall_eq (d : Spec.TripleDes.Direction) :
    Impl.TripleDes.PPC64LE.Ecb.blockCall d = .call (blockName d) (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .r3, 384⟩, ⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.wr
  keyScratch : (Region.mk (s.gpr .r3) 384).Disjoint ⟨s.gpr .r5, 512⟩
  dataScratch : (Region.mk (s.gpr .r4) 8).Disjoint ⟨s.gpr .r5, 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (s.gpr .r4) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .r3)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .r4))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.PPC64LE.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  have c3 := State.callEntry_gpr s (r := .r3) (by decide)
  have c4 := State.callEntry_gpr s (r := .r4) (by decide)
  have c5 := State.callEntry_gpr s (r := .r5) (by decide)
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨s.gpr .r3, 384⟩])
    (wr := [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch⟩
  · intro s' rd wr _ frame callee _ out
    refine ⟨?_, callee, rd, wr, frame, ?_⟩
    · intro r hr
      have h := out.2 r hr
      have hl : ∀ r ∈ kept, r ∉ linkRegs := by decide
      have hl := hl r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ hl] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4] at h
      exact h

end VG.Proof.TripleDes.PPC64LE.Ecb
