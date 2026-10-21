module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGaps
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedGeometry

/-! # Secret witness bookkeeping occupies the free prepared-header gap -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem Data.keepHeader {g : Geometry} (v : g.Valid) {s t : State} {c capacity d bytes : Nat} {p : BitVec 32}
    (S : Data g c capacity p s) (lo : 128 ≤ d) (hi : d + bytes ≤ 224)
    (O : Outside g.W d bytes s.mem t.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) : Data g c capacity p t := by
  have outs := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.ready.scratch.nowrap outs
  refine ⟨⟨Prepared.keepGaps v S.ready.context K base outs (by
      intro r mem; obtain rfl := List.mem_singleton.mp mem; exact Or.inl ⟨lo, hi⟩),
    S.ready.modulus.keep v F (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact Or.inl lo)
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; right; have := v.arrayHeader 0; omega),
    S.ready.caller.keepOuts K sp outs
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega),
    S.ready.scratch.of_keeps K base sp⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (O.val32 (Or.inr (by have := v.arrayHeader 4; omega))
      (by have := S.ready.scratch.nowrap; have := v.arrayFit (j := 4) (by decide); omega)).trans S.r2
  · exact (O.val32 (Or.inr (by have := v.arrayHeader 9; omega))
      (by have := S.ready.scratch.nowrap; have := v.arrayFit (j := 9) (by decide); omega)).trans S.one
  · exact (O.val32 (Or.inr (by have := v.arrayHeader 10; omega))
      (by have := S.ready.scratch.nowrap; have := v.arrayFit (j := 10) (by decide); omega)).trans S.minusOne
  · exact (O.val32 (Or.inr (by have := v.arrayHeader 27; omega))
      (by have := S.ready.scratch.nowrap; have := v.arrayFit (j := 27) (by decide); omega)).trans S.exponent
  · exact (O.word (Or.inr (by have := v.arrayHeader 27; omega))
      (by have := S.ready.scratch.nowrap; have := Prepared.paddedFit v (j := 27) (by decide); omega)).trans S.marker
  · exact (O.word (Or.inr hi) (by decide)).trans S.stride

theorem Data.keepGap {g : Geometry} (v : g.Valid) {s t : State} {c capacity d : Nat} {p : BitVec 32}
    (S : Data g c capacity p s) (lo : 128 ≤ d) (hi : d + 4 ≤ 224)
    (O : Outside g.W d 4 s.mem t.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) : Data g c capacity p t :=
  S.keepHeader v lo hi O K base sp

theorem storeGap_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity d : Nat} {p : BitVec 32}
    (S : Data g c capacity p s) (lo : 128 ≤ d) (hi : d + 4 ≤ 224) :
    WP isa (.block [.store (sc d) .eax]) s fun t =>
      Data g c capacity p t ∧ t.mem.readW (off g.W d) 32 = s.gpr .eax ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [] s t := by
  have fit : d + 4 ≤ g.L := Nat.le_trans (by omega) v.headerFit
  refine wp_storeS (S.ready.scratch.ea (by omega)) (S.ready.scratch.write fit) fun t T => WP.block_nil ?_
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by have := S.ready.scratch.nowrap; omega)
  exact ⟨S.keepGap v lo hi O (T.keeps []) (by decide) (by decide),
    by rw [T.mem, Mem.readW_writeW_self32], O, T.keeps []⟩

end VG.Proof.RsaKeyGen.X86.Prepare
