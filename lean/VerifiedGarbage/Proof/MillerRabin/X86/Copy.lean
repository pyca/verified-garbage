module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.CopyLoop
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer

/-! # Runtime-width prepared array copies on i686 -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem words_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block words) s fun t => (t.gpr .esi).toNat = g.words ∧ t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold words
  refine wp_movS (readSrc_ptr C.ws C.base (d := 48) (by have := v.headerFit; omega)) fun a A _ => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ⟨?_, T.mem.trans A.mem, A.keeps.trans T.keeps⟩
  rw [T.gpr, A.gpr, BitVec.toNat_add, Nat.zero_add]
  change (w32 s.mem g.W 48 + w32 s.mem g.W 48) % 2 ^ 32 = g.words
  rw [C.width]
  have bound := v.maxWidth
  unfold Geometry.words
  omega

theorem copy_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (dst src : Nat) (dstIndex : dst < 28) (srcIndex : src < 28) :
    WP isa (copy dst src) s fun t =>
      val32 t.mem g.W (g.array dst) g.words = val32 s.mem g.W (g.array src) g.words ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t ∧ Context g t := by
  unfold copy
  rw [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v dst dstIndex .ebp (by decide) (by decide))
    fun a ⟨P, M, K⟩ => ?_))
  have Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Ca.ptr v src srcIndex .ebx (by decide) (by decide))
    fun b ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_
  have keep : Keeps [.ebx, .edx, .ebp, .esi] s c :=
    ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))
  have mem : c.mem = s.mem := Mc.trans (Mb.trans M)
  have bp : PtrAt c g.W .ebp (g.array dst) := by
    rw [PtrAt, Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have bx : PtrAt c g.W .ebx (g.array src) := by
    rw [PtrAt, Kc.1 .ebx (by decide)]; exact Pb
  refine WP.mono (copyLoop_ok (C.ws.of_keeps keep) (by have := v.minWidth; unfold Geometry.words; omega)
    (v.arrayFit dstIndex) (v.arrayFit srcIndex) (g.arraysApart dst src) bp bx Count) ?_
  rintro t ⟨O, V, Kt⟩
  have Kall : Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := (keep.mono (by decide)).trans (Kt.mono (by decide))
  rw [mem] at O V
  exact ⟨V, O, Kall, C.keepOutside Kall (by decide) O (v.arrayHeader dst)⟩

end VG.Proof.MillerRabin.X86
