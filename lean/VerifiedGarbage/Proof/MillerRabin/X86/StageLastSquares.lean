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
import VerifiedGarbage.Proof.MillerRabin.X86.MarkerCalc
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
  have tf : sThreshold + 4 ≤ g.L := by unfold sThreshold; omega
  have sf : sSquares + 4 ≤ g.L := by unfold sSquares; omega
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
