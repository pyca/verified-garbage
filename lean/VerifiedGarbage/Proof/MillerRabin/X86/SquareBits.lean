module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.FlagMath

/-! # A square includes minus-one equality only above its secret threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem squareBits_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {q r : Nat} (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (count : s.mem.readW (off g.W sSquares) 32 = BitVec.ofNat 32 q)
    (threshold : s.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 r)
    (eqBit : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat) :
    WP isa (.block (squareFlag.take 8)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 q ∧ (t.gpr .edx).toNat = (F || (E && decide (r < q))).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have header := v.headerFit
  change WP isa (.block [.mov .eax (.mem (slot sSquares)), .mov .edx (.mem (slot sThreshold)),
    .alu .sub .edx (.reg .eax), .shift .shr .edx 31, .mov .ecx (.mem (slot sEq2)),
    .alu .and .ecx (.reg .edx), .mov .edx (.mem (slot sFlag)), .alu .or .edx (.reg .ecx)]) s _
  refine wp_movS (C.readScalar sSquares (by unfold sSquares; omega)) fun a A _ => ?_
  refine wp_movS (C.readScalarAfter A.keeps (by decide) A.mem sThreshold
    (by unfold sThreshold; omega)) fun b B _ => ?_
  refine wp_subS rfl fun c D _ => wp_shr (by decide) fun d H _ => ?_
  have Kd : Keeps [.eax, .edx] s d := (((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := by rw [H.mem, D.mem, B.mem, A.mem]
  refine wp_movS (C.readScalarAfter Kd (by decide) Md sEq2 (by unfold sEq2; omega)) fun e I _ => ?_
  refine wp_logicS (.inl rfl) rfl fun f J => ?_
  have Kf : Keeps [.eax, .ecx, .edx] s f := (Kd.mono (by decide)).widen I.keeps |>.widen J.keeps
  have Mf : f.mem = s.mem := J.mem.trans (I.mem.trans Md)
  refine wp_movS (C.readScalarAfter Kf (by decide) Mf sFlag (by unfold sFlag; omega)) fun h K _ => ?_
  refine wp_orS rfl fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, T.mem.trans (K.mem.trans Mf), (Kf.widen K.keeps).widen T.keeps⟩
  · rw [T.other .eax (by decide), K.other .eax (by decide), J.other .eax (by decide),
      I.other .eax (by decide), H.other .eax (by decide), D.other .eax (by decide),
      B.other .eax (by decide), A.gpr, count]
  · rw [T.gpr, K.gpr, K.other .ecx (by decide), J.gpr, I.gpr, I.other .edx (by decide),
      H.gpr, D.gpr, B.gpr, B.other .eax (by decide), A.gpr,
      count, threshold, eqBit, flag]
    change ((BitVec.ofNat 32 F.toNat) ||| ((BitVec.ofNat 32 E.toNat) &&&
      ((BitVec.ofNat 32 r - BitVec.ofNat 32 q) >>> 31))).toNat = _
    exact squareFlag_value rBound qBound E F

end VG.Proof.MillerRabin.X86
