module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer

/-! # Exponent words are addressed by the public countdown, from high to low -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem loadWord_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q ≤ g.words)
    (count : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q) :
    WP isa (.block loadWord) s fun t =>
      t.mem = (s.mem.writeW (off g.W sValue)
        (s.mem.readW (off g.W (g.array aExponent + 4 * (q - 1))) 32)).writeW
          (off g.W sWindows) 8#32 ∧
      Outs g.W [(sValue, 4), (sWindows, 4)] s.mem t.mem ∧
      Keeps [.eax, .edx, .ebp] s t ∧ Context g t := by
  have header := v.headerFit
  have expFit := v.arrayFit (j := aExponent) (by decide)
  have small : q ≤ 256 := by have := v.maxWidth; unfold Geometry.words at bound; omega
  unfold loadWord
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun u ⟨P, Mu, Ku⟩ => ?_)
  have Cu := C.keepMem Ku (by decide) Mu
  refine wp_movS (Cu.readScalar sWords (by unfold sWords; omega)) fun a A _ => ?_
  refine wp_subS rfl fun b B _ => wp_addS rfl fun c D _ => wp_addS rfl fun d H _ => ?_
  have Kd : Keeps [.eax, .edx, .ebp] s d :=
    ((((Ku.mono (by decide)).widen A.keeps).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := H.mem.trans (D.mem.trans (B.mem.trans (A.mem.trans Mu)))
  have bp : PtrAt d g.W .ebp (g.array aExponent) := by
    rw [PtrAt, H.other .ebp (by decide), D.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide)]; exact P
  have indexVal : (d.gpr .eax).toNat = 4 * (q - 1) := by
    rw [H.gpr, D.gpr, B.gpr, A.gpr, Mu, count]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 +
      ((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
    omega
  refine wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp] s e := Kd.widen I.keeps
  have Me : e.mem = s.mem := I.mem.trans Md
  have be : PtrAt e g.W .ebp (g.array aExponent + 4 * (q - 1)) := by
    rw [PtrAt, I.gpr, ptr_add bp, indexVal]
  have Ce := C.keepMem Ke (by decide) Me
  refine wp_movS (readSrc_ptr Ce.ws be (d := 0) (by omega)) fun f J _ => ?_
  have Kf : Keeps [.eax, .edx, .ebp] s f := Ke.widen J.keeps
  have Mf : f.mem = s.mem := J.mem.trans Me
  have Cf := C.keepMem Kf (by decide) Mf
  refine wp_storeS (ea_ptr Cf.ws Cf.base (d := sValue) (by unfold sValue; omega))
    (ws_write Cf.ws (y := 0 + sValue) (n := 4) (by unfold sValue; omega)) fun h L => ?_
  have Ov : Outside g.W sValue 4 f.mem h.mem := by
    rw [L.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sValue; omega)
  have Ch := Cf.keepScalar (L.keeps []) (by decide) Ov (by unfold scratchWord sValue; simp)
  refine wp_movS rfl fun k N _ => ?_
  have Ck := Ch.keepMem N.keeps (by decide) N.mem
  refine wp_storeS (ea_ptr Ck.ws Ck.base (d := sWindows) (by unfold sWindows; omega))
    (ws_write Ck.ws (y := 0 + sWindows) (n := 4) (by unfold sWindows; omega)) fun t T => WP.block_nil ?_
  have Ow : Outside g.W sWindows 4 h.mem t.mem := by
    rw [T.mem, Nat.zero_add, N.mem]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sWindows; omega)
  have Kall : Keeps [.eax, .edx, .ebp] s t :=
    (((Kf.widen (L.keeps [])).widen N.keeps).widen (T.keeps []))
  refine ⟨?_, ?_, Kall, Ck.keepScalar (T.keeps []) (by decide)
    (by rw [N.mem]; exact Ow) (by unfold scratchWord sWindows; simp)⟩
  · rw [T.mem, Nat.zero_add, N.gpr, N.mem, L.mem, Nat.zero_add, J.gpr, Me, Mf, Nat.add_zero]
    rfl
  · rw [Mf] at Ov
    exact (Outs.of_outside Ov (by simp)).trans (Outs.of_outside Ow (by simp))

end VG.Proof.MillerRabin.X86
