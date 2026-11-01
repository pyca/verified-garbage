module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame

import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
/-! # The shared round retains candidate preparation and the caller's capacity slot -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CallerFrame.lean`, which only this module imported.
section

/-! # Retain a candidate's capacity slot across the larger shared-round stack -/

section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Caller.keepSizedFrame {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (C : Caller g capacity p s) {rs : List Reg} {n : Nat} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (lengthFar : (lengthRegion p).Disjoint (below p n))
    (F : Frame ([⟨g.W, g.L⟩] ++ [below p n]) s.mem t.mem) : Caller g capacity p t := by
  have spT : t.gpr .esp = p := (K.1 .esp sp).trans C.sp
  refine ⟨spT, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  have same : readSrc t (.mem (at_ .esp 24)) = readSrc s (.mem (at_ .esp 24)) := by
    show t.load32 (t.ea (at_ .esp 24)) = s.load32 (s.ea (at_ .esp 24))
    have eaS : s.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [C.sp]
      rfl
    have eaT : t.ea (at_ .esp 24) = (lengthRegion p).base := by
      change (t.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = _
      rw [spT]
      rfl
    simp only [State.load32, eaT, eaS, K.2.1, K.2.2]
    congr 1
    apply congrArg some
    apply F.readW (r := lengthRegion p) (Region.contains_self _ _) ?_ (by decide)
    intro r mem
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact C.lengthFar
    · exact lengthFar
  exact same.trans C.readLen

end VG.Proof.RsaKeyGen.X86
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.RoundCall
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem Context.keepRound {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    (K : Keeps [.eax, .ecx, .edx] s t)
    (F : WorkspaceFrame g (roundWrites g) s.mem t.mem) : Context g t := by
  have read {d : Nat} (fit : d + 4 ≤ g.L)
      (apart : d + 4 ≤ 8 ∨ 16 ≤ d ∧ d + 4 ≤ 184 ∨ 224 ≤ d ∧ d + 4 ≤ 232) :
      w32 t.mem g.W d = w32 s.mem g.W d := by
    apply congrArg BitVec.toNat
    apply F.read32 fit
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Mont.X86.Rt.PtrAt, K.1 .edi (by decide)]; exact C.base
  · rw [read (by have := v.headerFit; omega) (by decide)]; exact C.width
  · rw [read (by have := v.headerFit; omega) (by decide)]; exact C.stride
  · intro j hj
    rw [read (by have := v.headerFit; omega) (by omega)]; exact C.pointers j hj

theorem data_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) (K : Keeps [.eax, .ecx, .edx] s t)
    (F : WorkspaceFrame g (roundWrites g) s.mem t.mem)
    (G : Frame ([⟨g.W, g.L⟩] ++ [below p 108]) s.mem t.mem)
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) : Prepare.Data g c capacity p t := by
  have arrays {j : Nat} (index : j = 0 ∨ j = 4 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
      ∀ r ∈ roundWrites g, g.array j + 4 * g.words ≤ r.1 ∨ r.1 + r.2 ≤ g.array j := by
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl | rfl <;>
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega
  have header {d : Nat} (lo : 16 ≤ d) (hi : d + 8 ≤ 184) :
      ∀ r ∈ roundWrites g, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro r mem
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega
  have M := S.ready.modulus.keep v F (fun r mem => by
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega)
    (arrays (Or.inl rfl))
  refine ⟨⟨Context.keepRound v S.ready.context K F, M, VG.Proof.RsaKeyGen.X86.Caller.keepSizedFrame S.ready.caller K (by decide) lengthFar G,
    S.ready.scratch.of_keeps K (by decide)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega))).trans S.r2
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega))).trans S.one
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega))).trans S.minusOne
  · exact (F.val32 (v.arrayFit (by decide)) (arrays (by omega))).trans S.exponent
  · change t.mem.readW (off g.W (g.array 27 + 8 * g.w)) 64 = _
    rw [F.read64 (by have := Prepared.paddedFit v (j := 27) (by decide); omega) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega)]
    exact S.marker
  · change t.mem.readW (off g.W 224) 64 = _
    rw [F.read64 (by have := v.headerFit; omega) (fun r mem => by
      simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega)]
    exact S.stride

end VG.Proof.RsaKeyGen.X86.RoundCall
