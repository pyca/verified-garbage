module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayStep
/-! # The remainder of the saved candidate minus one by `e`, at a run-time width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayInit.lean`, which only this module imported.
section

/-! # The array reduction starts with remainder zero -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem zeroRemainder_ok (s : State) :
    WP isa (.block zeroRemainder) s fun t =>
      t.gpr .ecx = 0#32 ∧ t.gpr .ebx = 0#32 ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  unfold zeroRemainder
  refine wp_movS rfl fun a A _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .ecx (by decide), A.gpr]; rfl, by rw [T.gpr]; rfl,
    T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayLoop.lean`, which only this module imported.
section

/-! # Reduce every native word while preserving the full modular prefix invariant -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem loop_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (S : ArrayState g candidate exponent 0 s) :
    WP isa (.loop (arrayStep g.exponent) .ne) s fun t =>
      ArrayState g candidate exponent g.n t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let Inv := fun q t => ∃ i, i + q = g.n ∧ 0 < q ∧ ArrayState g candidate exponent i t ∧
    Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  refine WP.loop (M := isa) Inv ?_ g.n s ⟨0, by omega, v.positive, S, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  rintro q t ⟨i, count, positive, T, O, K⟩
  refine WP.mono (T.step v (by omega)) fun u ⟨U, Z, Ou, Ku⟩ => ?_
  by_cases done : i + 1 = g.n
  · left
    refine ⟨?_, done ▸ U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some false
    rw [Z, decide_eq_true done]
    rfl
  · right
    refine ⟨?_, q - 1, by omega, i + 1, by omega, by omega, U, O.trans Ou, K.trans Ku⟩
    change u.zf.map Bool.not = some true
    rw [Z, decide_eq_false done]
    rfl

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Proof.RsaKeyGen.X86.Mod64

/-- The geometry of the reduction of array 5 by `e` (at byte 128). -/
def geometry (sp workspace : BitVec 32) (size w : Nat) : ArrayGeometry := ⟨sp, workspace, size, 2 * w, slot w 5, 128⟩

theorem init_ok {sp workspace : BitVec 32} {size w : Nat} (v : (geometry sp workspace size w).Valid)
    {candidate exponent : Nat} {s : State} (C : ArrayContext (geometry sp workspace size w) candidate exponent s)
    (positive : 0 < exponent) (hw : w ≤ 64)
    (len : s.mem.readW (off (geometry sp workspace size w).base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block arrayInit) s fun t =>
      ArrayState (geometry sp workspace size w) candidate exponent 0 t ∧
      Outside (sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have hn := v.sourceFit
  change slot w 5 + 4 * (2 * w) ≤ size at hn
  have wpos := v.positive
  change 0 < 2 * w at wpos
  have nowrap := C.scratch.nowrap
  change (workspace.setWidth 64).toNat + size ≤ 2 ^ 32 at nowrap
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := workspace.isLt; omega)] at nowrap
  have header : 8 ≤ size := by have := slot5_lo w; omega
  unfold arrayInit
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine savedPtr_ok C.scratch header len (by decide) (by decide) (by decide) fun a Ka Ma eaxA => ?_
  have Sa := C.scratch.of_keeps Ka (by decide)
  refine wp_movS (readSrc_sc Sa (by change 4 + 4 ≤ size; omega)) fun b B _ => wp_addS rfl fun c D _ => wp_subS rfl fun d E _ => ?_
  have Kd : Keeps [.eax, .edx] s d :=
    (((Ka.mono (by decide)).trans (B.keeps.mono (by decide))).trans (D.keeps.mono (by decide))).trans
      (E.keeps.mono (by decide))
  have Cd := C.stack.keep Kd (by decide)
  refine wp_storeS (Cd.address 0 (by decide)) (ws_write Cd.ws (by decide)) fun e F => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun f G => ?_
  have Kf : Keeps [.eax, .edx] s f := (Kd.trans ((F.keeps []).mono (by decide))).trans (G.keeps.mono (by decide))
  have Cf := C.stack.keep Kf (by decide)
  refine wp_storeS (Cf.address 4 (by decide)) (ws_write Cf.ws (by decide)) fun g H => ?_
  have Kg : Keeps [.eax, .edx] s g := Kf.trans ((H.keeps []).mono (by decide))
  have lenB : b.gpr .edx = BitVec.ofNat 32 (8 * w) := by rw [B.gpr, Ma, len]
  have edi : s.gpr .edi = workspace := C.workspace
  have ptr : d.gpr .eax = (geometry sp workspace size w).pointer 0 := by
    rw [E.gpr, D.gpr, B.other .eax (by decide), eaxA, lenB, edi]
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 32).toNat = 4 := rfl
    simp only [geometry, ArrayGeometry.pointer, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h4]
    have := workspace.isLt
    have := slot5_lo w
    omega
  have count : f.gpr .edx = BitVec.ofNat 32 (2 * w) := by
    rw [G.gpr, F.gpr, E.other .edx (by decide), D.other .edx (by decide), lenB]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
    omega
  have Oe : Outside (sp.setWidth 64) 0 4 s.mem e.mem := by
    rw [F.mem, E.mem, D.mem, B.mem, Ma]
    exact writeW32_outside _ _ _ (by decide)
  have Og : Outside (sp.setWidth 64) 4 4 e.mem g.mem := by
    rw [H.mem, G.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Cg := C.keepFrame v Kg (by decide) (by decide)
    (arrayStackFrame ((Oe.mono (by decide) (by decide)).trans (Og.mono (by decide) (by decide))))
  have Pg : g.mem.readW (off (sp.setWidth 64) 0) 32 = (geometry sp workspace size w).pointer 0 := by
    rw [BitVec.eq_of_toNat_eq (Og.w32 (d := 0) (by decide) (by decide)), F.mem]
    exact (Mem.readW_writeW_self32 ..).trans ptr
  have Ng : g.mem.readW (off (sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (2 * w) := by
    rw [H.mem]
    exact (Mem.readW_writeW_self32 ..).trans count
  refine WP.mono (zeroRemainder_ok g) fun t ⟨Zc, Zb, M, K⟩ => ?_
  have Ct := Cg.keepReadonly K (by decide) (by decide) M
  have zero : pair (t.gpr .ecx) (t.gpr .ebx) = 0 := by rw [Zc, Zb]; rfl
  have bound : candidate < 2 ^ (32 * (2 * w)) := by rw [← C.candidateValue]; exact val32_lt ..
  refine ⟨⟨Ct, by rw [M]; exact Pg, by rw [M]; exact Ng, ?_, ?_⟩, ?_, (Kg.mono (by decide)).trans (K.mono (by decide))⟩
  · change pair (t.gpr .ecx) (t.gpr .ebx) = (candidate / 2 ^ (32 * (2 * w - 0))) % exponent
    rw [zero, Nat.sub_zero, Nat.div_eq_of_lt bound, Nat.zero_mod]
  · rw [zero]; exact positive
  · rw [M]
    exact (Oe.mono (by decide) (by decide)).trans (Og.mono (by decide) (by decide))

theorem array_ok {sp workspace : BitVec 32} {size w : Nat} (v : (geometry sp workspace size w).Valid)
    {candidate exponent : Nat} {s : State} (C : ArrayContext (geometry sp workspace size w) candidate exponent s)
    (positive : 0 < exponent) (hw : w ≤ 64)
    (len : s.mem.readW (off (geometry sp workspace size w).base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa array s fun t =>
      ArrayContext (geometry sp workspace size w) candidate exponent t ∧
      pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      Outside (sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (init_ok v C positive hw len) fun u ⟨U, O, K⟩ => ?_)
  refine WP.mono (loop_ok v U) fun t ⟨T, Ot, Kt⟩ => ?_
  refine ⟨T.context, ?_, O.trans Ot, (K.mono (by decide)).trans Kt⟩
  simpa only [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using T.value

theorem array_noSp : NoSp array := by
  apply NoSp.of_all
  have bitSafe (e : Nat) : (VG.Impl.RsaKeyGen.X86.Mod64.bit e).all (fun i => !Taint.clobbers i .esp) = true := by rfl
  simp only [Code.allInstrs_eq, array, VG.Impl.RsaKeyGen.X86.Mod64.arrayStep, instrs,
    List.all_append, VG.Impl.RsaKeyGen.X86.Mod64.word, VG.Impl.RsaKeyGen.X86.Mod64.steps, List.all_flatMap, bitSafe]
  rfl

theorem framed_context {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Scr s base size) (width : 4 ≤ w) (space : slot w 5 + 8 * w ≤ size)
    (value : val32 s.mem base (slot w 5) (2 * w) = candidate)
    (eValue : exponentValue s.mem base 128 = exponent)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    (geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w).Valid ∧
      ArrayContext (geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w) candidate exponent (allocFrame 20 s) := by
  let g : ArrayGeometry := geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w
  have baseEq : g.base = base := S.edi
  have lo := slot5_lo w
  refine ⟨⟨by change 0 < 2 * w; omega, by change slot w 5 + 4 * (2 * w) ≤ size; omega,
    by change 128 + 8 ≤ size; omega, by
    change (⟨g.base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩
    rw [baseEq]
    exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))⟩, ?_⟩
  refine ⟨?_, VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (s := s) (by omega), ?_, ?_⟩
  · change Scr (allocFrame 20 s) g.base size
    rw [baseEq]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S fit separate
  · change val32 s.mem g.base (slot w 5) (2 * w) = candidate
    rw [baseEq]; exact value
  · change exponentValue s.mem g.base 128 = exponent
    rw [baseEq]; exact eValue

theorem framed_ok {base : Addr} {size w candidate exponent : Nat} {s : State}
    (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64) (space : slot w 5 + 8 * w ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (value : val32 s.mem base (slot w 5) (2 * w) = candidate)
    (eValue : exponentValue s.mem base 128 = exponent) (ePositive : 0 < exponent)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.alloc 20) array (.free 20)) s fun t =>
      Scr t base size ∧ pair (t.gpr .ecx) (t.gpr .ebx) = candidate % exponent ∧
      val32 t.mem base (slot w 5) (2 * w) = candidate ∧ exponentValue t.mem base 128 = exponent ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let g : ArrayGeometry := geometry (s.gpr .esp - 20#32) (s.gpr .edi) size w
  have baseEq : g.base = base := S.edi
  have lo := slot5_lo w
  have valid : g.Valid := ⟨by change 0 < 2 * w; omega, by change slot w 5 + 4 * (2 * w) ≤ size; omega,
    by change 128 + 8 ≤ size; omega, by
    change (⟨g.base, size⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩
    rw [baseEq]
    exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))⟩
  have C : ArrayContext g candidate exponent (allocFrame 20 s) := by
    refine ⟨?_, VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (s := s) (by omega), ?_, ?_⟩
    · rw [baseEq]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S fit separate
    · change val32 s.mem g.base (slot w 5) (2 * w) = candidate
      rw [baseEq]; exact value
    · change exponentValue s.mem g.base 128 = exponent
      rw [baseEq]; exact eValue
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) array_noSp ?_
  · refine WP.mono (array_ok valid C ePositive hw (by rw [allocFrame_mem, baseEq]; exact len))
      fun t ⟨T, result, O, K⟩ => ?_
    have Kout := VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps K (by decide)
    refine ⟨S.of_keeps Kout (by decide), ?_, ?_, ?_, ?_, Kout⟩
    · rw [freed_gpr _ _ (by decide), freed_gpr _ _ (by decide)]
      exact result
    · rw [← baseEq]; exact T.candidateValue
    · rw [← baseEq]; exact T.exponentEq
    · have F : Frame [g.stackRegion] (allocFrame 20 s).mem t.mem := arrayStackFrame O
      rw [allocFrame_mem] at F
      exact F

end VG.Proof.RsaKeyGen.X86.ExponentRt
