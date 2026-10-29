module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.MillerRabin.X86.EqualLoop
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Impl.MillerRabin.X86.Layout
/-! # Full runtime-width equality of two prepared arrays -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/EqualFinish.lean`, which only this module imported.
section

/-! # Branch-free conversion of a word comparison into a stored bit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equalFinish_ok {s : State} {W : Addr} {L result : Nat} (hw : Ws s W L)
    (base : PtrAt s W .edi 0) (fit : result + 4 ≤ L) :
    WP isa (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
      .alu .adc .eax (.imm 0), .store (slot result) .eax]) s fun t =>
      w32 t.mem W result = (decide (s.gpr .ebx = 0#32)).toNat ∧
      Outside W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cf => wp_adcS rfl cf fun c C _ => ?_
  have K : Keeps [.eax, .ebx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have hc := hw.of_keeps K
  have baseC : PtrAt c W .edi 0 := by rw [PtrAt, K.1 .edi (by decide)]; exact base
  refine wp_storeS (ea_ptr hc baseC (d := result) (by omega))
    (ws_write hc (y := 0 + result) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have value : c.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebx = 0#32)).toNat := by
    rw [C.gpr, B.other .eax (by decide), A.gpr, A.other .ebx (by decide)]
    have test : decide ((s.gpr .ebx).toNat < (1 : BitVec 32).toNat) = decide (s.gpr .ebx = 0#32) := by
      have iffZero : (s.gpr .ebx).toNat < (1 : BitVec 32).toNat ↔ s.gpr .ebx = 0#32 := by
        rw [← BitVec.toNat_inj]
        change (s.gpr .ebx).toNat < 1 ↔ (s.gpr .ebx).toNat = 0
        omega
      simp only [iffZero]
    rw [test]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, Nat.zero_add, w32_write_self, value, BitVec.toNat_ofNat]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  · rw [T.mem, Nat.zero_add, M]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equal_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (result a b : Nat) (resultFit : result + 4 ≤ g.L) (aIndex : a < 28) (bIndex : b < 28) :
    WP isa (equal result a b) s fun t =>
      w32 t.mem g.W result =
        (decide (val32 s.mem g.W (g.array a) g.words = val32 s.mem g.W (g.array b) g.words)).toNat ∧
      Outside g.W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold equal
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v a aIndex .ebp (by decide) (by decide))
    fun u ⟨P, M, K⟩ => ?_))
  have Cu := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Cu.ptr v b bIndex .ecx (by decide) (by decide))
    fun b₁ ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Cu.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d D _ => WP.block_nil ?_
  have keep : Keeps [.ebx, .ecx, .edx, .ebp, .esi] s d :=
    (((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))).widen D.keeps
  have mem : d.mem = s.mem := D.mem.trans (Mc.trans (Mb.trans M))
  have bp : PtrAt d g.W .ebp (g.array a) := by
    rw [PtrAt, D.other .ebp (by decide), Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have cx : PtrAt d g.W .ecx (g.array b) := by
    rw [PtrAt, D.other .ecx (by decide), Kc.1 .ecx (by decide)]; exact Pb
  refine WP.seq (WP.mono (equalLoop_ok (C.ws.of_keeps keep)
    (by have := v.minWidth; unfold Geometry.words; omega) (v.arrayFit aIndex) (v.arrayFit bIndex)
    bp cx (by rw [D.other .esi (by decide)]; exact Count) D.gpr) fun e ⟨Me, V, Ke⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s e :=
    (keep.mono (by decide)).trans (Ke.mono (by decide))
  have Ce := C.keepMem Kall (by decide) (Me.trans mem)
  refine WP.mono (equalFinish_ok Ce.ws Ce.base resultFit) fun t ⟨Value, O, Kt⟩ => ?_
  simp only [V, mem, xorWords_zero] at Value
  rw [Me, mem] at O
  exact ⟨Value, O, Kall.widen Kt⟩

end VG.Proof.MillerRabin.X86
