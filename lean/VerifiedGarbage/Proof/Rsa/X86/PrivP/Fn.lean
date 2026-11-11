module

public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Body
public import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
import VerifiedGarbage.Proof.Rsa.X86.PrivRestore
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-! # `vg_rsa_private_checked_precomputed` on x86: the function

`vg_rsa_private_checked`'s frame around `bodyP` (`privateFnP_ok`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated freed freed_esp freed_gpr)

def privCodeP (v : CrtImpl) (w : CrtPImpl) : Prog isa := codeP w.name w.code v.pcName v.pc v.pdName v.pd

theorem privateBodyP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) := by
  unfold bodyP check
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.call' w.noSp)
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pcNoSp)
      (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pdNoSp)
        (.of_all (by decide +kernel)))))))

theorem privateAllocationP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.frame (.alloc frameBytes)
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact privateBodyP_noSp v w i hi
  · rfl

theorem privateInnerP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.seq (.frame (.alloc frameBytes)
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) (.block restore)) :=
  .seq' (privateAllocationP_noSp v w) (.of_all (by decide +kernel))

theorem privateFnP_ok (v : CrtImpl) (w : CrtPImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    {P : BitVec 32} {L : Nat} (h : PrivFnInput g bs s) (H : PreCtx g bs P L (entered s)) :
    WP isa (privCodeP v w) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold stackBytes at this; omega
  have allocation : VG.Impl.Rsa.X86.PrivChecked.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [stackBytes, VG.Impl.Rsa.X86.PrivChecked.frameBytes] at *
    omega
  unfold privCodeP codeP
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (privateInnerP_noSp v w) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (privateBodyP_noSp v w) ?_
  refine WP.mono (privateBodyP_ok v w (entered s) h.context H) ?_
  rintro u ⟨result, _, frame, rest⟩
  have spU : (freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).rd ++
        (freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).wr)
        (addr ((freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega)
  refine WP.mono (restore_ok (freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u)
    (read 4 (by decide)) (read 8 (by decide)) (read 0 (by decide))) ?_
  rintro t ⟨edi, ebp, esi, memT, restT⟩
  have spT : t.gpr .esp = (pushed savedRegisters s).gpr .esp :=
    (restT.1 .esp (by decide)).trans spU
  have words (i : Nat) (hi : i < 4) := h.savedWord frame i hi
  have mem : t.mem = u.mem := memT
  have savedEdi : t.gpr .edi = s.gpr .edi := by
    rw [edi, spU]; exact words 0 (by decide)
  have savedEbp : t.gpr .ebp = s.gpr .ebp := by
    rw [ebp, spU]; exact words 2 (by decide)
  have savedEsi : t.gpr .esi = s.gpr .esi := by
    rw [esi, spU]; exact words 1 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, spT, mem]
      exact words 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEbp
    · rw [popped_esp, spT, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]; exact h.returnWord frame
  · rw [popped_mem, popped_gpr _ _ _ (by decide) (by decide), mem,
      restT.1 .eax (by decide), freed_gpr _ _ (by decide)]
    exact result
end VG.Proof.Rsa.X86.PrivChecked
