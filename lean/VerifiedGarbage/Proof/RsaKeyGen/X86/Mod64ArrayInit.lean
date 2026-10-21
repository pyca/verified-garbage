module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayPointerInit

/-! # The array reduction starts at its highest native word with remainder zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem zeroRemainder_ok (s : State) :
    WP isa (.block zeroRemainder) s fun t =>
      t.gpr .ecx = 0#32 ∧ t.gpr .ebx = 0#32 ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  unfold zeroRemainder
  refine wp_movS rfl fun a A _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .ecx (by decide), A.gpr]; rfl, by rw [T.gpr]; rfl,
    T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

theorem init_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) (positive : 0 < exponent) :
    WP isa (.block (init g.n g.src)) s fun t =>
      ArrayState g candidate exponent 0 t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧
      Keeps [.eax, .ecx, .ebx] s t := by
  unfold init
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (pointerInit_ok v C) fun a ⟨Ca, Pa, Oa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (Ca.stack.literal 4 (by decide) (BitVec.ofNat 32 g.n))
    fun b ⟨Mb, Ob, Kb, _⟩ => ?_)
  have Cb := Ca.keepFrame v Kb (by decide) (by decide)
    (arrayStackFrame (Ob.mono (by decide) (by decide)))
  have Pb : b.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer 0 :=
    (BitVec.eq_of_toNat_eq (Ob.w32 (d := 0) (by decide) (by decide))).trans Pa
  have count : b.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 g.n := by
    rw [Mb, Mem.readW_writeW_self32]
  refine WP.mono (zeroRemainder_ok b) fun t ⟨Zc, Zb, M, K⟩ => ?_
  have Ct := Cb.keepReadonly K (by decide) (by decide) M
  have Ot : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by
    rw [M]
    exact Oa.trans (Ob.mono (by decide) (by decide))
  have zero : pair (t.gpr .ecx) (t.gpr .ebx) = 0 := by rw [Zc, Zb]; rfl
  have bound : candidate < 2 ^ (32 * g.n) := by rw [← C.candidateValue]; exact val32_lt ..
  refine ⟨⟨Ct, ?_, ?_, ?_, ?_⟩, Ot, ((Ka.trans Kb).mono (by decide)).widen K⟩
  · rw [M]
    exact Pb
  · rw [M, Nat.sub_zero]
    exact count
  · rw [zero, Nat.sub_zero, Nat.div_eq_of_lt bound, Nat.zero_mod]
  · rw [zero]
    exact positive

end VG.Proof.RsaKeyGen.X86.Mod64
