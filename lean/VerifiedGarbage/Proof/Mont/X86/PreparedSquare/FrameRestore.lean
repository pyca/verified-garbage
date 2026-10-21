module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Saved

public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Restore
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The public cache is discarded after restoring the caller's registers -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem inner_noSp : NoSp (.seq VG.Impl.Mont.X86.PreparedSquare.core (.block VG.Impl.Mont.X86.PreparedSquare.restore)) :=
  .of_all (by decide +kernel)

theorem frame_restore {s : State} {W : Addr} {L N S o : Nat} {A : Nat → BitVec 32}
    {g : Reg → BitVec 32} {Q : Mem → Prop}
    (fit : 16 ≤ (s.gpr .esp).toNat)
    (hw : Ws (entered s) W L) (ha : Compact.Args (entered s) W L A)
    (base : (A 0).toNat = W.toNat)
    (scratch : w32 (entered s).mem W 80 = (W.toNat + S) % 2 ^ 32)
    (header : 128 ≤ S) (outHeader : 128 ≤ o)
    (span : S + 8 * N + 32 ≤ L) (outFit : o + 4 * N ≤ L)
    (apart : o + 4 * N ≤ S ∨ S + 8 * N + 32 ≤ o)
    (saved : SavedAt (entered s).mem W S g)
    (core : WP isa VG.Impl.Mont.X86.PreparedSquare.core (entered s) fun t =>
      Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] (entered s).mem t.mem ∧
      Q t.mem ∧ Keeps clob7 (entered s) t) :
    WP isa (.frame (.push cacheRegisters)
      (.seq VG.Impl.Mont.X86.PreparedSquare.core (.block VG.Impl.Mont.X86.PreparedSquare.restore)) (.pop .eax 4)) s fun t =>
      t.gpr .ebx = g .ebx ∧ t.gpr .esi = g .esi ∧ t.gpr .ebp = g .ebp ∧ t.gpr .edi = g .edi ∧
      t.gpr .esp = s.gpr .esp ∧
      Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] (entered s).mem t.mem ∧ Q t.mem := by
  refine WP.frame (rs := cacheRegisters) (by decide) (by decide) (by decide) fit inner_noSp ?_
  refine WP.seq (WP.mono core ?_)
  rintro t ⟨O, H, K⟩
  have savedt := saved.of_outs O (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega) (by have := hw.nowrap; omega)
  have Oall : Outs W [(0, L)] (entered s).mem t.mem := O.cover (by
    intro r hr
    refine ⟨(0, L), by simp, by omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega)
  have scratcht : w32 t.mem W 80 = (W.toNat + S) % 2 ^ 32 := by
    apply Eq.trans _ scratch
    unfold w32
    apply congrArg BitVec.toNat
    apply Mem.readW_congr
    intro i hi
    apply O
    intro r hr
    rw [ofs_off W (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  refine WP.mono (restore_ok (hw.of_keeps K) (ha.of_keeps K (by decide) Oall) base scratcht
    (by omega) (by omega) savedt) ?_
  rintro u ⟨ebx, esi, ebp, edi, mem, Ku⟩
  have sp : u.gpr .esp = (entered s).gpr .esp := (Ku.1 .esp (by decide)).trans (K.1 .esp (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebx
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
  · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
  · rw [popped_esp, sp, entered, pushed_esp]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]; exact O
  · rw [popped_mem, mem]; exact H

end VG.Proof.Mont.X86.PreparedSquare
