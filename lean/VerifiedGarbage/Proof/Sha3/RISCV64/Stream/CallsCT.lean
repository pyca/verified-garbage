module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Calls
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified

/-!
# The SHA-3 sponge on RISC-V: its calls in constant time

As PPC64LE's (`Proof/Ed448/PPC64LE/Whole/HashCT.lean`): two runs that call
`vg_keccak_absorb`, `vg_keccak_pad` or `vg_keccak_squeeze` on the same
arguments leak the same trace (`absorbCall_ct`, `padCall_ct`,
`squeezeCall_ct`), by the callee's own constant-time proof (`RelCT.call`).
The sponge functions save and restore registers in their working space,
which a taint analysis of their callers would take to be secret afterwards,
so their callers relate these calls instead.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64

section
variable {st : Addr} {pa : Addr} {rate pos pl : Nat}

/-- Both runs call `absorb` on the same arguments. -/
theorem absorbCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ AbsorbArgs a st pa rate pos pl ∧ AbsorbArgs b st pa rate pos pl ∧
      Covers ([⟨pa, pl⟩] ++ [⟨st, 200⟩]) (a.rd ++ a.wr) ∧ Covers [⟨st, 200⟩] a.wr ∧
      Covers ([⟨pa, pl⟩] ++ [⟨st, 200⟩]) (b.rd ++ b.wr) ∧ Covers [⟨st, 200⟩] b.wr) :
    RelCT isa P (.call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb) fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.absorbRISCV64) absorb_verified'.1 absorb_ct [⟨pa, pl⟩] [⟨st, 200⟩]
    fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨absorb_pre ha, absorb_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.absorbRISCV64, ce_gpr _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.a1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.a3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, hb.a0, hb.a1, hb.a2, hb.a3,
    hb.a4, hsp, and_self]

/-- Both runs call `pad` on the same arguments. -/
theorem padCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ PadArgs a st rate pos ∧ PadArgs b st rate pos ∧
      Covers ([] ++ [⟨st, 200⟩]) (a.rd ++ a.wr) ∧ Covers [⟨st, 200⟩] a.wr ∧
      Covers ([] ++ [⟨st, 200⟩]) (b.rd ++ b.wr) ∧ Covers [⟨st, 200⟩] b.wr) :
    RelCT isa P (.call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad) fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.padRISCV64) pad_verified'.1 pad_ct [] [⟨st, 200⟩] fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨pad_pre ha, pad_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.padRISCV64, ce_gpr _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.a1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp, ha.a0, ha.a1, ha.a2, hb.a0, hb.a1, hb.a2, hsp, and_self]

/-- Both runs call `squeeze` on the same arguments. -/
theorem squeezeCall_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp ∧ SqueezeArgs a st pa rate pos pl ∧ SqueezeArgs b st pa rate pos pl ∧
      Covers ([] ++ [⟨st, 200⟩, ⟨pa, pl⟩]) (a.rd ++ a.wr) ∧ Covers [⟨st, 200⟩, ⟨pa, pl⟩] a.wr ∧
      Covers ([] ++ [⟨st, 200⟩, ⟨pa, pl⟩]) (b.rd ++ b.wr) ∧ Covers [⟨st, 200⟩, ⟨pa, pl⟩] b.wr) :
    RelCT isa P (.call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze) fun _ _ => True := by
  refine RelCT.call (k := Proof.Sha3.squeezeRISCV64) squeeze_verified'.1 squeeze_ct [] [⟨st, 200⟩, ⟨pa, pl⟩]
    fun a b hab => ?_
  obtain ⟨hsp, ha, hb, ca, wa, cb, wb⟩ := hP a b hab
  refine ⟨squeeze_pre ha, squeeze_pre hb, ?_, ca, wa, cb, wb⟩
  simp only [Proof.Sha3.squeezeRISCV64, ce_gpr _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.a1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.a3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp, ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, hb.a0, hb.a1, hb.a2, hb.a3,
    hb.a4, hsp, and_self]

end

end VG.Proof.Sha3.RISCV64.Stream
