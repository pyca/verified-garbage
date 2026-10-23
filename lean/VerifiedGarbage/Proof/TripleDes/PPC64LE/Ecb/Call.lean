module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.TripleDes.PPC64LE.VerifiedBlock
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Ecb
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Pre

/-! # A call of the block function from ECB on PPC64LE -/

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
