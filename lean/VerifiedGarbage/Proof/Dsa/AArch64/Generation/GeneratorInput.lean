module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Bignum.Words

/-! Bind the current generator input to the saved public-exponentiation operands. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Bignum (Outside writeW_outside word_writeW_self)
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Layout

theorem generatorInput_ok {s : State} {F S B hp : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hB : W 5 = B) (hh : W 21 = hp)
    (hout : InRegions s.wr (off B 272) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.generatorInput) s fun t =>
      t.gpr .x0 = B ∧ VG.Proof.Bignum.word t.mem B 272 = hp ∧
      Outside B 272 8 s.mem t.mem ∧ Keep [.x0, .x3] s t := by
  have hb : s.mem.readW (F + BitVec.ofNat 64 40) 64 = B := (R.fr 5 (by decide)).trans hB
  have hx : s.mem.readW (F + BitVec.ofNat 64 168) 64 = hp := (R.fr 21 (by decide)).trans hh
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t =>
    t.gpr .x0 = B ∧ t.mem = s.mem.writeW (off B 272) hp) (by
    brun [Impl.Dsa.AArch64.Generation.generatorInput, Field.offset,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 168) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 168) (n := 8) (by decide), hb, hx, hout])
    rfl rfl rfl) fun t ⟨⟨hdi, hm⟩, hk⟩ => ?_
  refine ⟨hdi, ?_, ?_, hk⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.AArch64.Generation
