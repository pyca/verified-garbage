module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive

/-! # Bind the current generator candidate to the reusable exponentiation parent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout

theorem generatorInput_ok {s : State} {F S B hp : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hB : W 5 = B) (hh : W 21 = hp)
    (hout : InRegions s.wr (off B 272) 8) :
    WP isa (.block Impl.Dsa.X86_64.Generation.generatorInput) s fun t =>
      t.gpr .rdi = B ∧ word t.mem B 272 = hp ∧
      Outside B 272 8 s.mem t.mem ∧ Keep [.rdi, .rax] s t := by
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem.writeW (off B 272) hp) (by
    xrun [Impl.Dsa.X86_64.Generation.generatorInput, ea_sp, L.rsp, Core.field, Field.offset,
      State.ea, BitVec.ofInt_natCast, Impl.Mgf1.X86_64.sp,
      L.ld (d := 40) (by decide), L.ld (d := 168) (by decide),
      R.slot (d := 40) (k := 5) rfl (by decide) hB,
      R.slot (d := 168) (k := 21) rfl (by decide) hh, hout]) rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ => ?_
  refine ⟨hdi, ?_, ?_, hk⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86_64.Generation
