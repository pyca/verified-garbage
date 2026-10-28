module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFilterContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.FastTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.GeneralTiming

/-! # Both exponent paths derive their public geometry from the same candidate input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure TimingInput (workspace p : BitVec 32) (size w candidate exponent : Nat) (s : State) : Prop where
  input : Input (workspace.setWidth 64) size w candidate exponent s
  stack : s.gpr .esp = p
  len : s.mem.readW (off (workspace.setWidth 64) 4) 32 = BitVec.ofNat 32 (8 * w)

theorem TimingInput.workspace {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.input.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem TimingInput.keepReadonly {workspace p : BitVec 32} {size w candidate exponent : Nat} {s t : State}
    (S : TimingInput workspace p size w candidate exponent s) (M : t.mem = s.mem) (K : Keeps [.eax] s t) :
    TimingInput workspace p size w candidate exponent t :=
  ⟨S.input.keepReadonly M K, (K.1 .esp (by decide)).trans S.stack, by rw [M]; exact S.len⟩

theorem TimingInput.framed {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : ExponentRt.Framed workspace p size w s :=
  ⟨⟨S.input.scratch, S.stack, S.input.width, S.input.widthBound, S.input.space, S.len⟩,
    by rw [← S.stack]; exact S.input.fit, by rw [← S.stack]; exact S.input.separate⟩

theorem TimingInput.general {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) (odd : exponent % 2 = 1) :
    ExponentRt.GeneralIn workspace p size w candidate exponent s :=
  ⟨S.framed, S.input.saved, S.input.exponentEq, odd⟩

end VG.Proof.RsaKeyGen.X86.ExponentFilter
