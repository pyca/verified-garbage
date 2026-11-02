module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer

/-! # The exponent marker is addressed using only the prepared public width -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem Geometry.Valid.markerFit {g : Geometry} (v : g.Valid) :
    g.array aExponent + 4 * g.words + 8 ≤ g.L := by
  have fit := v.arraysFit
  unfold Geometry.array Geometry.words aExponent Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at *
  omega

theorem markerPointer_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block markerPointer) s fun t =>
      PtrAt t g.W .ebp (g.array aExponent + 4 * g.words) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp, .esi] s t := by
  unfold markerPointer
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun a ⟨P, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (words_ok v Ca) fun b ⟨Count, Mb, Kb⟩ => ?_)
  refine wp_movS rfl fun c D _ => wp_addS rfl fun d H _ => wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp, .esi] s e :=
    (((((Ka.mono (by decide)).trans (Kb.mono (by decide))).widen D.keeps).widen H.keeps).widen I.keeps)
  have bp : PtrAt e g.W .ebp (g.array aExponent) := by
    rw [PtrAt, I.other .ebp (by decide), H.other .ebp (by decide), D.other .ebp (by decide),
      Kb.1 .ebp (by decide)]; exact P
  have width : (e.gpr .eax).toNat = 4 * g.words := by
    rw [I.gpr, H.gpr, D.gpr]
    simp only [BitVec.toNat_add, Count]
    have bound := v.maxWidth
    unfold Geometry.words
    omega
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, Ke.widen T.keeps⟩
  · rw [PtrAt, T.gpr, ptr_add bp, width]
  · rw [T.mem, I.mem, H.mem, D.mem, Mb, Ma]

end VG.Proof.MillerRabin.X86
