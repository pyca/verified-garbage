module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.SelectLoop
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer

/-! # Each table selection preserves the prepared header and other arrays -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem selectEntry_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) (k : Bool)
    (mask : s.mem.readW (off g.W sEq1) 32 = if k then BitVec.allOnes 32 else 0#32) :
    WP isa (selectEntry j) s fun t =>
      val32 t.mem g.W (g.array aX) g.words =
        val32 s.mem g.W (g.array (if k then aTable + j else aX)) g.words ∧
      Outside g.W (g.array aX) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  unfold selectEntry
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v (aTable + j) (by unfold aTable; omega)
    .ebp (by decide) (by decide)) fun a ⟨P, M, K⟩ => ?_))
  have Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Ca.ptr v aX (by decide) .ebx (by decide) (by decide))
    fun b ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_)
  have Cc := Cb.keepMem Kc (by decide) Mc
  refine wp_movS (readSrc_ptr Cc.ws Cc.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega))
    fun d D _ => WP.block_nil ?_
  have keep : Keeps [.ebx, .ecx, .edx, .ebp, .esi] s d :=
    (((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))).widen D.keeps
  have mem : d.mem = s.mem := D.mem.trans (Mc.trans (Mb.trans M))
  have bp : PtrAt d g.W .ebp (g.array (aTable + j)) := by
    rw [PtrAt, D.other .ebp (by decide), Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have bx : PtrAt d g.W .ebx (g.array aX) := by
    rw [PtrAt, D.other .ebx (by decide), Kc.1 .ebx (by decide)]; exact Pb
  have apart : g.array aX + 4 * g.words ≤ g.array (aTable + j) ∨
      g.array (aTable + j) + 4 * g.words ≤ g.array aX := by
    have sep := g.arraysApart aX (aTable + j)
    have neq : g.array aX ≠ g.array (aTable + j) := by
      have step := Nat.mul_le_mul_right (8 * (g.w + 2)) (show 6 ≤ 11 + j by omega)
      unfold Geometry.array VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes aX aTable
      omega
    exact sep.resolve_left neq
  refine WP.mono (selectLoop_ok (C.ws.of_keeps keep)
    (by have := v.minWidth; unfold Geometry.words; omega) (v.arrayFit (by decide))
    (v.arrayFit (by unfold aTable; omega)) apart bx bp
    (by rw [D.other .esi (by decide)]; exact Count) k
    (by rw [D.gpr, Mc, Mb, M, Nat.zero_add]; exact mask)) ?_
  rintro t ⟨O, V, Kt⟩
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (keep.mono (by decide)).trans (Kt.mono (by decide))
  rw [mem] at O V
  refine ⟨?_, O, Kall, C.keepOutside Kall (by decide) O (v.arrayHeader aX)⟩
  cases k <;> exact V

end VG.Proof.MillerRabin.X86
