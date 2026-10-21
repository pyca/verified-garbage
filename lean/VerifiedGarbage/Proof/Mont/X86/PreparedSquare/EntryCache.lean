module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Cache
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryColumns
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.EntryContext
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.TimingCore
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.ConstantTime
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Narrow
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingGeometry
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

/-! # Cache correctness supplies the public context for both timed runs -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Spec.Rsa.Mont hiding Keeps

structure Cached (s t : State) : Prop where
  eax : t.gpr .eax = arg s 0
  ebx : t.gpr .ebx = s.mem.readW (off (Compact.wsOf s) 48) 32
  esi : t.gpr .esi = arg s 0 + BitVec.ofNat 32 (arrAt (wOf s.mem (Compact.wsOf s)) (arg s 3).toNat)
  ebp : t.gpr .ebp = arg s 0 + BitVec.ofNat 32 256
  edi : PtrAt t (Compact.wsOf s) .edi (arrAt (wOf s.mem (Compact.wsOf s)) 2)
  saved : SavedAt t.mem (Compact.wsOf s) (arrAt (wOf s.mem (Compact.wsOf s)) 2) s.gpr
  outside : Outside (Compact.wsOf s) (arrAt (wOf s.mem (Compact.wsOf s)) 2) 16 s.mem t.mem
  keeps : Keeps clob7 s t

theorem entry_cache {s : State} (A : Compact.Entry s) :
    WP isa (.block VG.Impl.Mont.X86.PreparedSquare.cache) s (Cached s) := by
  have fit : arrAt (wOf s.mem (Compact.wsOf s)) 8 ≤ Compact.lenOf s := by
    simpa only [Compact.lenOf, Nat.mul_comm] using A.layout.2.2.1
  have M := Compact.layout_metadata (A := arg s) A.layout A.left.1 A.right.1
  have modulus : arrAt (wOf s.mem (Compact.wsOf s)) 0 = 256 := by simp [arrAt, hdrBytes]
  rw [modulus] at M
  refine WP.mono (cache_ok (raw_ws A) (raw_args A) A.ws_toNat.symm M
    (by unfold arrAt hdrBytes; omega) (by unfold arrAt hdrBytes at *; omega)) ?_
  rintro t ⟨eax, ebx, esi, ebp, edi, saved, O, K⟩
  exact ⟨eax, ebx, esi, ebp, edi, saved, O, K⟩

theorem cached_side {s t : State} (A : Compact.Entry s) (same : arg s 3 = arg s 4) (C : Cached s t) :
    Compact.Context (Compact.geometry s) (entered t) ∧
      ∃ B, ColumnReady (entered t) (Compact.geometry s).W (Compact.geometry s).L
        (Compact.geometry s).N (Compact.geometry s).S (Compact.geometry s).o (Compact.geometry s).a B := by
  exact ⟨entry_context A C.keeps C.outside, _,
    entry_columns A same C.keeps C.outside C.eax C.ebx C.esi C.ebp C.edi⟩

theorem cached_pair {s t u v : State} (A : Compact.Entry s) (B : Compact.Entry t)
    (same : arg s 3 = arg s 4) (pub : (mulContract abi 16).pub s t)
    (C : Cached s u) (D : Cached t v) : SquarePair (Compact.geometry s) (entered u) (entered v) := by
  obtain ⟨sp, args, width⟩ := Compact.publicInputs pub
  have tsame : arg t 3 = arg t 4 := by rw [← args 3 (by decide), ← args 4 (by decide)]; exact same
  have geo := Compact.geometry_eq args width
  obtain ⟨CS, R⟩ := cached_side A same C
  obtain ⟨CT, T⟩ := cached_side B tsame D
  rw [← geo] at CT T
  refine ⟨CS, CT, R, T, ?_⟩
  rw [entered, entered, pushed_esp, pushed_esp, C.keeps.1 .esp (by decide), D.keeps.1 .esp (by decide), sp]

end VG.Proof.Mont.X86.PreparedSquare
