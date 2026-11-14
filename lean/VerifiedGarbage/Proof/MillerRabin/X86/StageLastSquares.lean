module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.MarkerPointer
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.MillerRabin.Word32

/-! ### `MillerRabin.X86.MarkerCalc`, which only this module used -/

section

/-! # Native instructions fold the secret exponent marker without branching -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/MarkerMath.lean`, which only this module imported.
section

/-! # Folding the exponent marker derives the final secret square threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86

private theorem double_eq_shift (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

def markerFold (lo hi : BitVec 32) : BitVec 32 :=
  let x1 := lo ||| hi
  let x2 := x1 ||| x1 >>> 16
  let x3 := x2 ||| x2 >>> 8
  let x4 := x3 ||| x3 >>> 4
  let b1 := x4 >>> 1 &&& 1
  let b2 := x4 >>> 2 &&& 1
  let b3 := x4 >>> 3 &&& 1
  b3 + b1 + b1 + b1 + b2 + b2

theorem markerFold_eq (lo hi : BitVec 32) : markerFold lo hi = Word32.foldR lo hi := by
  unfold markerFold Word32.foldR
  dsimp only
  rw [← double_eq_shift, ← double_eq_shift]
  simp only [BitVec.add_assoc]
  rfl

theorem markerFold_twoPow {k : Nat} (bound : k < 64) :
    markerFold (BitVec.ofNat 32 (2 ^ k % 2 ^ 32)) (BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) =
      BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k) := by
  rw [markerFold_eq]
  exact Word32.foldR_eq k bound

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem markerCalc_ok {s : State} {W : Addr} {L d : Nat} (hw : Ws s W L)
    (ptr : PtrAt s W .ebp d) (fit : d + 8 ≤ L) :
    WP isa (.block markerCalc) s fun t =>
      t.gpr .eax = markerFold (s.mem.readW (off W d) 32) (s.mem.readW (off W (d + 4)) 32) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold markerCalc
  refine wp_movS (readSrc_ptr hw ptr (d := 0) (by omega_using [fit])) fun s1 u1 _ => ?_
  have bp1 : PtrAt s1 W .ebp d := by rw [PtrAt, u1.other .ebp (by decide)]; exact ptr
  refine wp_orS (readSrc_ptr (hw.of_keeps u1.keeps) bp1 (d := 4) fit) fun s2 u2 => ?_
  refine wp_movS rfl fun s3 u3 _ => ?_
  refine wp_shr (by decide) fun s4 u4 _ => ?_
  refine wp_orS rfl fun s5 u5 => ?_
  refine wp_movS rfl fun s6 u6 _ => ?_
  refine wp_shr (by decide) fun s7 u7 _ => ?_
  refine wp_orS rfl fun s8 u8 => ?_
  refine wp_movS rfl fun s9 u9 _ => ?_
  refine wp_shr (by decide) fun s10 u10 _ => ?_
  refine wp_orS rfl fun s11 u11 => ?_
  refine wp_movS rfl fun s12 u12 _ => ?_
  refine wp_shr (by decide) fun s13 u13 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s14 u14 => ?_
  refine wp_movS rfl fun s15 u15 _ => ?_
  refine wp_shr (by decide) fun s16 u16 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s17 u17 => ?_
  refine wp_shr (by decide) fun s18 u18 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s19 u19 => ?_
  refine wp_addS rfl fun s20 u20 _ => ?_
  refine wp_addS rfl fun s21 u21 _ => ?_
  refine wp_addS rfl fun s22 u22 _ => ?_
  refine wp_addS rfl fun s23 u23 _ => ?_
  refine wp_addS rfl fun s24 u24 _ => ?_
  refine WP.block_nil ⟨?_, ?_, ((((((((((((((((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen u9.keeps).widen u10.keeps).widen u11.keeps).widen u12.keeps).widen u13.keeps).widen u14.keeps).widen u15.keeps).widen u16.keeps).widen u17.keeps).widen u18.keeps).widen u19.keeps).widen u20.keeps).widen u21.keeps).widen u22.keeps).widen u23.keeps).widen u24.keeps)⟩
  · let x1 := s.mem.readW (off W d) 32 ||| s.mem.readW (off W (d + 4)) 32
    let x2 := x1 ||| x1 >>> 16
    let x3 := x2 ||| x2 >>> 8
    let x4 := x3 ||| x3 >>> 4
    have v2 : s2.gpr .eax = x1 := by rw [u2.gpr, u1.gpr, u1.mem, Nat.add_zero]
    have v5 : s5.gpr .eax = x2 := by
      rw [u5.gpr, u4.other .eax (by decide), u3.other .eax (by decide), v2, u4.gpr, u3.gpr, v2]
    have v8 : s8.gpr .eax = x3 := by
      rw [u8.gpr, u7.other .eax (by decide), u6.other .eax (by decide), v5, u7.gpr, u6.gpr, v5]
    have v11 : s11.gpr .eax = x4 := by
      rw [u11.gpr, u10.other .eax (by decide), u9.other .eax (by decide), v8, u10.gpr, u9.gpr, v8]
    have v14 : s14.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u14.gpr, u13.gpr, u12.gpr, v11]
      rfl
    have v17 : s17.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u17.gpr, u16.gpr, u15.gpr, u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have v19 : s19.gpr .eax = x4 >>> 3 &&& 1 := by
      rw [u19.gpr, u18.gpr, u17.other .eax (by decide), u16.other .eax (by decide),
        u15.other .eax (by decide), u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have d19 : s19.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u19.other .edx (by decide), u18.other .edx (by decide), u17.other .edx (by decide),
        u16.other .edx (by decide), u15.other .edx (by decide), v14]
    have b19 : s19.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u19.other .ebx (by decide), u18.other .ebx (by decide), v17]
    rw [u24.gpr, u23.gpr, u22.gpr, u21.gpr, u20.gpr, v19,
      u23.other .ebx (by decide), u22.other .ebx (by decide), u21.other .ebx (by decide),
      u20.other .ebx (by decide), b19,
      u21.other .edx (by decide), u20.other .edx (by decide), d19]
    rfl
  · rw [u24.mem, u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.MillerRabin.X86

end

end

/-! # The folded marker prepares a fixed three-square finishing stage -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/LastSquares.lean`, which only this module imported.
section

/-! # The final three squares use the threshold encoded by the prepared marker -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem lastSquares_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    {k : Nat} (bound : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (.block lastSquares) s fun t =>
      t.mem = (s.mem.writeW (off g.W sThreshold) (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))).writeW
        (off g.W sSquares) 3#32 ∧
      Outs g.W [(sThreshold, 4), (sSquares, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Context g t := by
  have header := v.headerFit
  unfold lastSquares
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (markerPointer_ok v C) fun a ⟨P, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (markerCalc_ok Ca.ws P v.markerFit) fun b ⟨AX, Mb, Kb⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
  have M : b.mem = s.mem := Mb.trans Ma
  have Cb := C.keepMem Kall (by decide) M
  have value : b.gpr .eax = BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k) := by
    rw [AX, Ma, lo, hi, markerFold_twoPow bound]
  refine wp_storeS (ea_ptr Cb.ws Cb.base (d := sThreshold) (by unfold sThreshold; omega))
    (ws_write Cb.ws (y := 0 + sThreshold) (n := 4) (by unfold sThreshold; omega)) fun d D => ?_
  have Oth : Outside g.W sThreshold 4 b.mem d.mem := by
    rw [D.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sThreshold; omega)
  have Cd := Cb.keepScalar (D.keeps []) (by decide) Oth (by unfold scratchWord sThreshold; simp)
  refine wp_movS rfl fun e I _ => ?_
  have Ce := Cd.keepMem I.keeps (by decide) I.mem
  refine wp_storeS (ea_ptr Ce.ws Ce.base (d := sSquares) (by unfold sSquares; omega))
    (ws_write Ce.ws (y := 0 + sSquares) (n := 4) (by unfold sSquares; omega)) fun t T => WP.block_nil ?_
  have Osq : Outside g.W sSquares 4 d.mem t.mem := by
    rw [T.mem, Nat.zero_add, I.mem]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; unfold sSquares; omega)
  refine ⟨?_, ?_, ((Kall.widen (D.keeps [])).widen I.keeps).widen (T.keeps []),
    Ce.keepScalar (T.keeps []) (by decide) (by rw [I.mem]; exact Osq) (by unfold scratchWord sSquares; simp)⟩
  · rw [T.mem, Nat.zero_add, I.gpr, I.mem, D.mem, Nat.zero_add, value, M]
    rfl
  · rw [M] at Oth
    exact (Outs.of_outside Oth (by simp)).trans (Outs.of_outside Osq (by simp))

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.lastSquares {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s)
    {k : Nat} (bound : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (.block lastSquares) s fun t =>
      Stage g capacity c p A Js
        (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
        ([sThreshold, sSquares] ++ wordFields) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := v.headerFit
  have tf : sThreshold + 4 ≤ g.L := by unfold sThreshold; omega_using [header]
  have sf : sSquares + 4 ≤ g.L := by unfold sSquares; omega_using [header]
  have scratch : ∀ d ∈ [sThreshold, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sThreshold; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (lastSquares_ok v S.data.context bound lo hi) fun t ⟨M, O, K, C⟩ => ?_
  have D : Data g A Js
      (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
      ([sThreshold, sSquares] ++ wordFields) t := by
    refine S.data.afterSlots v C [sThreshold, sSquares] ?_ ?_ O
    · intro d mem
      refine ⟨scratch d mem, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · change t.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k)
        apply BitVec.eq_of_toNat_eq
        change w32 t.mem g.W sThreshold = _
        rw [M, w32_write_ne S.data.context.ws.nowrap sf tf
          (by right; unfold sThreshold sSquares; decide), w32_write_self]
      · change t.mem.readW (off g.W sSquares) 32 = 3#32
        rw [M, Mem.readW_writeW_self32]
    · intro d mem _
      change d ∈ [184, 232] at mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> rfl
  exact ⟨S.afterSlots v D [sThreshold, sSquares] scratch O K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
