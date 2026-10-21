module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry


public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryCache
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.CacheTiming
import VerifiedGarbage.Proof.Mont.X86.Compact.ConstantTime
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import Init.Core
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa

/-! # Public entry inputs determine the complete prepared-square trace -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Spec.Rsa.Mont hiding Keeps
open VG.Proof.Dsa.X86

def BodyPair (s t : State) : Prop :=
  Compact.Entry s ∧ Compact.Entry t ∧ arg s 3 = arg s 4 ∧ (mulContract abi 16).pub s t

def CachedPair (u v : State) : Prop := ∃ s t, BodyPair s t ∧ Cached s u ∧ Cached t v

theorem entry_args_out {s : State} (A : Compact.Entry s) : ArgsOut 5 s := by
  refine ⟨A.stackBound, ?_⟩
  intro r hr
  rw [A.wr] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact VG.X86.Taint.frame_disjoint (n := 20) (by have := A.stackBound; omega) A.returnSeparate A.argSeparate.symm

theorem cache_relCT : RelCT isa BodyPair (.block VG.Impl.Mont.X86.PreparedSquare.cache) CachedPair := by
  intro s t ls lt u v H ES ET
  obtain ⟨A, B, same, pub⟩ := H
  obtain ⟨sp, args, width⟩ := Compact.publicInputs pub
  have geo := Compact.geometry_eq args width
  have agree : VG.X86.Taint.Agree (argTaint [] 24) s t :=
    agree_argTaint (k := 5) (by intro r hr; cases hr) sp (entry_args_out A) (entry_args_out B) args
  have M := Compact.layout_metadata (A := arg s) A.layout A.left.1 A.right.1
  have T := Compact.layout_metadata (A := arg t) B.layout B.left.1 B.right.1
  have bw : Ws t (Compact.geometry s).W (Compact.geometry s).L := by
    rw [geo]
    exact raw_ws B
  have bt : (arg t 0).toNat = (Compact.wsOf s).toNat := by
    rw [← args 0 (by decide)]
    exact A.ws_toNat.symm
  have tscratch : w32 t.mem (Compact.geometry s).W 80 =
      ((Compact.geometry s).W.toNat + (Compact.geometry s).S) % 2 ^ 32 := by
    rw [geo]
    exact T.scratch
  have ba : RawArgs t (Compact.geometry s).W (Compact.geometry s).L (arg t) := by
    rw [geo]
    exact raw_args B
  obtain ⟨trace, _⟩ := cache_trace (raw_ws A) bw (raw_args A) ba A.ws_toNat.symm bt M.scratch tscratch
    (by have := A.headerFit; omega) agree ES ET
  exact ⟨trace, s, t, ⟨A, B, same, pub⟩, wp_result (entry_cache A) ES, wp_result (entry_cache B) ET⟩

theorem cached_sp {u v : State} (H : CachedPair u v) : u.gpr .esp = v.gpr .esp := by
  obtain ⟨s, t, ⟨_, _, _, pub⟩, C, D⟩ := H
  rw [C.keeps.1 .esp (by decide), D.keeps.1 .esp (by decide)]
  exact (Compact.publicInputs pub).1

theorem body_trace : RelCT isa BodyPair VG.Impl.Mont.X86.PreparedSquare.body (fun _ _ => True) := by
  unfold VG.Impl.Mont.X86.PreparedSquare.body
  refine RelCT.seq cache_relCT (VG.X86.RelCT.frame (rs := cacheRegisters) (R := fun _ _ => True)
    (fun _ _ H => cached_sp H) ?_)
  rintro a b ls lt u v ⟨x, y, ⟨s, t, ⟨A, B, same, pub⟩, C, D⟩, rfl, rfl⟩ ES ET
  have pair := cached_pair A B same pub C D
  exact ⟨(inner_trace A.geometry_valid _ _ _ _ _ _ pair ES ET).1, True.intro⟩

end VG.Proof.Mont.X86.PreparedSquare
