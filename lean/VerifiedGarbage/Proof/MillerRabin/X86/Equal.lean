module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.EqualLoop
import VerifiedGarbage.Proof.MillerRabin.X86.EqualFinish
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer

/-! # Full runtime-width equality of two prepared arrays -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equal_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (result a b : Nat) (resultFit : result + 4 ≤ g.L) (aIndex : a < 28) (bIndex : b < 28) :
    WP isa (equal result a b) s fun t =>
      w32 t.mem g.W result =
        (decide (val32 s.mem g.W (g.array a) g.words = val32 s.mem g.W (g.array b) g.words)).toNat ∧
      Outside g.W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold equal
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v a aIndex .ebp (by decide) (by decide))
    fun u ⟨P, M, K⟩ => ?_))
  have Cu := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Cu.ptr v b bIndex .ecx (by decide) (by decide))
    fun b₁ ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Cu.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d D _ => WP.block_nil ?_
  have keep : Keeps [.ebx, .ecx, .edx, .ebp, .esi] s d :=
    (((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))).widen D.keeps
  have mem : d.mem = s.mem := D.mem.trans (Mc.trans (Mb.trans M))
  have bp : PtrAt d g.W .ebp (g.array a) := by
    rw [PtrAt, D.other .ebp (by decide), Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have cx : PtrAt d g.W .ecx (g.array b) := by
    rw [PtrAt, D.other .ecx (by decide), Kc.1 .ecx (by decide)]; exact Pb
  refine WP.seq (WP.mono (equalLoop_ok (C.ws.of_keeps keep)
    (by have := v.minWidth; unfold Geometry.words; omega) (v.arrayFit aIndex) (v.arrayFit bIndex)
    bp cx (by rw [D.other .esi (by decide)]; exact Count) D.gpr) fun e ⟨Me, V, Ke⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s e :=
    (keep.mono (by decide)).trans (Ke.mono (by decide))
  have Ce := C.keepMem Kall (by decide) (Me.trans mem)
  refine WP.mono (equalFinish_ok Ce.ws Ce.base resultFit) fun t ⟨Value, O, Kt⟩ => ?_
  simp only [V, mem, xorWords_zero] at Value
  rw [Me, mem] at O
  exact ⟨Value, O, Kall.widen Kt⟩

end VG.Proof.MillerRabin.X86
