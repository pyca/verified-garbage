module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT

import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: parity uses public addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64

theorem odd_ct :
    RelCT isa (Two GoodW1) (seqs (isOdd aXm)) fun _ _ => True := by
  change RelCT isa (Two GoodW1)
    (.block (([.mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++
      [.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1)])) _
  refine RelCT.block_append ((pin_ct (Φ := GoodW1) (Ψ := fun (_ : Ws) (_ : State) => True)
    [.rdi] [.rbx] (fun L _ => off L.B (slot L.w aXm)) pins_goodW1
    (by taint_decide) ?_ (by taint_decide) ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial))
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, _, _⟩ := h
    have hh := hdr_lt_slot L.w 8 (show sArr aXm < 32 by decide)
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w aXm))
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sArr aXm) (by omega), hg.hdr.harr aXm (by decide)]) rfl)
      fun t ⟨hb, _⟩ r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    exact hb
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, hw, _⟩ := h
    have hp := WP.mono (isOdd_ok hg hZ hw (show aXm < 8 by decide)) (fun _ _ => True.intro)
    change WP isa (.block (([.mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++
      [.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1)])) s (fun _ => True) at hp
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hp)

end VG.Proof.Ffdh.X86_64.CheckDomain
