module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.Words32

/-! # Reduction digit for prepared paired-word multiplication -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The prepared negative inverse supplies one radix-2³² reduction digit. -/
theorem redDigit_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {S w : Nat} (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp w)
    (headerFit : 60 ≤ L) (wordFit : w + 4 ≤ L) (digitFit : S + Rt.multOff + 4 ≤ L) :
    WP isa (.block Compact.redDigit) s fun u =>
      w32 u.mem W (S + Rt.multOff) = w32 s.mem W w * w32 s.mem W 56 % 2 ^ 32 ∧
      Keeps [.eax, .edx] s u ∧ Outside W (S + Rt.multOff) 4 s.mem u.mem := by
  have nowrap := hw.nowrap
  unfold Compact.redDigit
  refine wp_movS (ha.read 0 (by decide)) fun a B _ => ?_
  have ptr : PtrAt a W .edx 0 := by
    rw [PtrAt, B.gpr, base, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have bp : PtrAt a W .ebp w := by
    rw [PtrAt, B.other .ebp (by decide)]; exact hebp
  refine wp_movS (readSrc_ptr (hw.of_keeps B.keeps) bp (d := 0) (by omega)) fun b C _ => ?_
  have ptr' : PtrAt b W .edx 0 := by
    rw [PtrAt, C.other .edx (by decide)]; exact ptr
  refine wp_movS (readSrc_ptr ((hw.of_keeps B.keeps).of_keeps C.keeps) ptr' (d := 56) (by omega)) fun c D _ => ?_
  refine wp_mul fun d E => ?_
  have K : Keeps [.eax, .edx] s d :=
    (((B.keeps.mono (by decide)).widen C.keeps).widen D.keeps).widen E.keeps
  have dp : PtrAt d W .edi S := by
    rw [PtrAt, K.1 .edi (by decide)]; exact hedi
  refine wp_storeS (ea_ptr (hw.of_keeps K) dp (d := Rt.multOff) (by omega))
    (ws_write (hw.of_keeps K) (y := S + Rt.multOff) (n := 4) digitFit) fun u F => WP.block_nil ?_
  refine ⟨?_, K.widen (F.keeps []), ?_⟩
  · rw [F.mem, w32_write_self, E.eax, D.other .eax (by decide), C.gpr, D.gpr,
      C.mem, B.mem, BitVec.toNat_ofNat, Nat.add_zero, Nat.zero_add]
  · rw [F.mem, E.mem, D.mem, C.mem, B.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Mont.X86.Compact
