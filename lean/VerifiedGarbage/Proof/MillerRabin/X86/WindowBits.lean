module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.FlagMath
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath

/-! # A window replaces the pass flag exactly when its digit is nonzero -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem windowBits_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (E1 E2 F : Bool)
    (eq1 : s.mem.readW (off g.W sEq1) 32 = BitVec.ofNat 32 E1.toNat)
    (eq2 : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E2.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat) :
    WP isa (.block (windowEnd.take 12)) s fun t =>
      t.gpr .eax = s.mem.readW (off g.W sValue) 32 ∧
      (t.gpr .ecx).toNat = (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0 then F else E1 || E2).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have header := v.headerFit
  change WP isa (.block [.mov .eax (.mem (slot sValue)), .mov .edx (.reg .eax), .shift .shr .edx 28,
    .alu .sub .edx (.imm 1), .shift .shr .edx 31, .mov .ebx (.reg .edx), .alu .xor .ebx (.imm 1),
    .mov .ecx (.mem (slot sEq1)), .alu .or .ecx (.mem (slot sEq2)), .alu .and .ecx (.reg .ebx),
    .alu .and .edx (.mem (slot sFlag)), .alu .or .ecx (.reg .edx)]) s _
  refine wp_movS (C.readScalar sValue (by unfold sValue; omega)) fun a A _ => ?_
  refine wp_movS rfl fun b B _ => wp_shr (by decide) fun c D _ => wp_subS rfl fun d H _ => ?_
  refine wp_shr (by decide) fun e I _ => wp_movS rfl fun f J _ => wp_logicS (.inr rfl) rfl fun h K => ?_
  have Kh : Keeps [.eax, .ebx, .edx] s h :=
    ((((((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen H.keeps).widen I.keeps).widen J.keeps).widen K.keeps
  have Mh : h.mem = s.mem := by rw [K.mem, J.mem, I.mem, H.mem, D.mem, B.mem, A.mem]
  refine wp_movS (C.readScalarAfter Kh (by decide) Mh sEq1 (by unfold sEq1; omega)) fun i L _ => ?_
  have Ki : Keeps [.eax, .ebx, .ecx, .edx] s i := (Kh.mono (by decide)).widen L.keeps
  have Mi : i.mem = s.mem := L.mem.trans Mh
  refine wp_orS (C.readScalarAfter Ki (by decide) Mi sEq2 (by unfold sEq2; omega)) fun j N => ?_
  refine wp_logicS (.inl rfl) rfl fun k P => ?_
  have Kk : Keeps [.eax, .ebx, .ecx, .edx] s k := (Ki.widen N.keeps).widen P.keeps
  have Mk : k.mem = s.mem := P.mem.trans (N.mem.trans Mi)
  refine wp_logicS (.inl rfl) (C.readScalarAfter Kk (by decide) Mk sFlag (by unfold sFlag; omega)) fun l Q => ?_
  refine wp_orS rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (Q.mem.trans Mk), (Kk.widen Q.keeps).widen T.keeps⟩
  · rw [T.other .eax (by decide), Q.other .eax (by decide), P.other .eax (by decide),
      N.other .eax (by decide), L.other .eax (by decide), K.other .eax (by decide),
      J.other .eax (by decide), I.other .eax (by decide), H.other .eax (by decide),
      D.other .eax (by decide), B.other .eax (by decide), A.gpr]
  · rw [T.gpr, Q.other .ecx (by decide), P.gpr, N.gpr, L.gpr, eq1, eq2,
      N.other .ebx (by decide), L.other .ebx (by decide), K.gpr, J.gpr,
      Q.gpr, P.other .edx (by decide), N.other .edx (by decide), L.other .edx (by decide),
      K.other .edx (by decide), J.other .edx (by decide), I.gpr, H.gpr, D.gpr, B.gpr, A.gpr, flag]
    change let z := ((s.mem.readW (off g.W sValue) 32 >>> 28) - 1) >>> 31
      (((BitVec.ofNat 32 E1.toNat ||| BitVec.ofNat 32 E2.toNat) &&& (z ^^^ 1)) |||
        (z &&& BitVec.ofNat 32 F.toNat)).toNat = _
    have digit := digit_lt (s.mem.readW (off g.W sValue) 32)
    have result := windowFlag_value digit E1 E2 F
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using result

end VG.Proof.MillerRabin.X86
