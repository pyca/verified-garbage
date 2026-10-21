module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap

/-! # Entropy exhaustion and the continuation flag of the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem word_equal4 (x : BitVec 32) : (x - 4#32 == 0#32) = decide (x.toNat = 4) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj, BitVec.toNat_sub]
  change (2 ^ 32 - 4 + x.toNat) % 2 ^ 32 = 0 ↔ x.toNat = 4
  have := x.isLt
  omega

theorem again_ok {g : Geometry} (v : g.Valid) {s : State} (S : Scr s g.W g.L) :
    WP isa (.block again) s fun t =>
      t.zf = some (decide (w32 s.mem g.W 168 = 4)) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold again
  refine wp_movS (readSrc_sc S (by have := v.headerFit; omega)) fun a A _ =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans (T.keeps _)⟩
  rw [Z, A.gpr]
  change some (s.mem.readW (off g.W 168) 32 - 4#32 == 0#32) = _
  rw [word_equal4]

theorem exhausted_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Prepare.Data g c capacity p s) :
    WP isa (.block exhausted) s fun t =>
      Prepare.Data g c capacity p t ∧ w32 t.mem g.W 168 = 0 ∧
      Outside g.W 168 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  have head := v.headerFit
  unfold exhausted
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun t T => WP.block_nil ?_
  have O : Outside g.W 168 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have K := A.keeps.widen (T.keeps [])
  exact ⟨S.keepGap v (by decide) (by decide) O K (by decide) (by decide),
    by rw [T.mem, w32_write_self, A.gpr]; rfl, O, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
