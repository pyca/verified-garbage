module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessAdvance
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap

/-! # Advancing entropy retains preparation and accounts for exactly one witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessAdvance
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessAdvance

theorem codeAt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity used step : Nat} {p rand : BitVec 32}
    (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand)
    (consumed : w32 s.mem g.W usedOffset = used) (fit : used + step < 2 ^ 32) :
    WP isa (.block (codeAt step)) s fun t =>
      Prepare.Data g c capacity p t ∧ t.gpr .esi = rand + BitVec.ofNat 32 used ∧
      w32 t.mem g.W usedOffset = used + step ∧
      Outside g.W usedOffset 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  have head := v.headerFit
  unfold codeAt
  refine wp_movS (readSrc_sc S.ready.scratch (by omega)) fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (d := usedOffset) (by unfold usedOffset; omega)) fun b B _ =>
    wp_addS rfl fun d D _ => wp_addS rfl fun e E _ => ?_
  have K : Keeps [.eax, .esi] s e := (((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps
  have Se := S.ready.scratch.of_keeps K (by decide)
  refine wp_storeS (Se.ea (by unfold usedOffset; omega)) (Se.write (by unfold usedOffset; omega)) fun t T => WP.block_nil ?_
  have Ot : Outside g.W usedOffset 4 s.mem t.mem := by
    rw [T.mem, E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold usedOffset; decide)
  have Kt := K.widen (T.keeps [])
  refine ⟨S.keepGap v (by unfold usedOffset; decide) (by unfold usedOffset; decide) Ot Kt (by decide) (by decide), ?_, ?_, Ot, Kt⟩
  · rw [T.gpr, E.other .esi (by decide), D.gpr, B.other .esi (by decide), A.gpr, source,
      B.gpr, A.mem]
    have wordEq : s.mem.readW (off g.W usedOffset) 32 = BitVec.ofNat 32 used := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← consumed, Nat.mod_eq_of_lt (by change w32 s.mem g.W usedOffset < 2 ^ 32; exact (s.mem.readW _ 32).isLt)]
    rw [wordEq]
  · rw [T.mem, w32_write_self, E.gpr, D.other .eax (by decide), B.gpr, A.mem,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W usedOffset + step % 2 ^ 32) % 2 ^ 32 = _
    rw [consumed, Nat.mod_eq_of_lt (a := step) (by omega), Nat.mod_eq_of_lt fit]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity used : Nat} {p rand : BitVec 32}
    (S : Prepare.Data g c capacity p s)
    (source : s.mem.readW (off g.W 28) 32 = rand)
    (consumed : w32 s.mem g.W usedOffset = used) (fit : used + 8 * g.w < 2 ^ 32) :
    WP isa (.block (code g.w)) s fun t =>
      Prepare.Data g c capacity p t ∧ t.gpr .esi = rand + BitVec.ofNat 32 used ∧
      w32 t.mem g.W usedOffset = used + 8 * g.w ∧
      Outside g.W usedOffset 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t :=
  codeAt_ok v S source consumed fit

end VG.Proof.RsaKeyGen.X86.WitnessAdvance
