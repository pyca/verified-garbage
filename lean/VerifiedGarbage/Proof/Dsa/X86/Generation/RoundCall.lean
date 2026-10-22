module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundResult
import VerifiedGarbage.Proof.Framework.Offset

/-! A complete generic cdecl call of the existing prepared Miller–Rabin round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Spec.Rsa.Mont (wOf numAt)

theorem round_call_noSp (v : RoundImpl) :
    NoSp (.seq (.block roundArguments) (.call v.name v.code) : Prog isa) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact (NoSp.of_all (by decide : (Code.block roundArguments : Prog isa).allInstrs
      (fun i => !Taint.clobbers i .esp) = true)) i hi
  · exact v.noSp i hi

theorem round_call (v : RoundImpl) {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic))
    (upper : n ≤ 48) (width : wOf s.mem (off base Layout.arithmetic) = n)
    (value : numAt s.mem (off base Layout.arithmetic) n 0 = candidate) :
    WP isa (roundCall v.name v.code) s fun t =>
      Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem ∧
      (∀ b, numAt s.mem (off base Layout.arithmetic) n 5 = b % candidate * 2 ^ (64 * n) % candidate →
        (t.gpr .eax).toNat = if Spec.MillerRabin.round candidate b then 1 else 0) ∧
      Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem := by
  have low := room.low
  have fit : ((allocFrame 8 s).gpr .esp).toNat + 8 ≤ 2 ^ 32 := by
    rw [allocFrame_esp, VG.X86.sub_toNat (by omega)]
    have := (s.gpr .esp).isLt; omega
  unfold roundCall
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (round_call_noSp v) ?_
  refine WP.seq (WP.mono (round_arguments fit (by rw [allocFrame_wr]; exact List.mem_cons_self ..))
    fun g ⟨Kg, Fg, first, second⟩ => ?_)
  have stack : g.gpr .esp = s.gpr .esp - 8#32 := by
    rw [Kg.1 .esp (by decide), allocFrame_esp]
  have F : Frame [below (s.gpr .esp) 8] s.mem g.mem := Fg
  have arg0 : g.mem.readW ((g.gpr .esp).setWidth 64) 32 =
      s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic := by
    rw [Kg.1 .esp (by decide), first, allocFrame_gpr _ _ (by decide)]
  have arg1 : g.mem.readW ((g.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32 := by
    rw [Kg.1 .esp (by decide), second]
  refine WP.mono (round_invoke v scr capacity room stack F arg0 arg1
    (by rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_self ..)
    (by rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ scr.wr) L P)
    fun t ⟨rd, wr, saved, Ft, u, memory, registers, post⟩ => ?_
  have result := round_post scr capacity room stack F arg0 arg1 L P upper width value memory
    (registers .eax (by decide)) post
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have savedReg : r ∈ calleeSaved := by
        cases r <;> simp_all [calleeSaved]
      by_cases sp : r = .esp
      · subst sp
        rw [freed_esp, saved .esp savedReg, stack, BitVec.sub_add_cancel]
      · rw [freed_gpr _ _ sp, saved r savedReg, Kg.1 r (by
          intro h; rw [List.mem_singleton.mp h] at hr; exact hr (by decide)), allocFrame_gpr _ _ sp]
    · rw [freed_rd, rd, Kg.2.1, allocFrame_rd]
    · rw [freed_wr, wr, Kg.2.2, allocFrame_wr]; rfl
  · exact (F.sub (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact ⟨below (s.gpr .esp) 1184, by simp, below_sub (by decide) low⟩)).trans Ft
  · simpa only [freed_gpr _ _ (show Reg.eax ≠ .esp by decide)] using result.1
  · exact result.2

end VG.Proof.Dsa.X86.Generation
