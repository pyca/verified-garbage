module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent

import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Flags
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Flags
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # FFDH domain validation on x86-64: constructing p minus one in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (zeroArr)

abbrev CdP.ows (p : CdP) : Ws := ⟨p.B, p.Z, p.w⟩

private def loads : List Instr :=
  [.mov .rsi (.mem (hdr sDom)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))]

private def decLow : List Instr :=
  [.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax]

private def ML (p : CdP) (s : State) : Prop := Parent p s ∧ s.gpr .rsi = p.dp ∧
  s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot p.w aX)

private theorem loads_ok (p : CdP) (s : State) (h : Parent p s) : WP isa (.block loads) s (ML p) := by
  refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t =>
      t.gpr .rsi = p.dp ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
      t.gpr .rbx = off p.B (slot p.w aX) ∧ t.mem = s.mem)
    (by unfold loads; xrun [State.ea, hdr, hdrOff, h.outer.rdi,
      h.outer.ld (show sDom < 32 by decide), h.outer.ld (show sK < 32 by decide),
      h.outer.ld (show sArr aX < 32 by decide), h.base.hdr (sDom, p.dp) (by simp [CdP.headers]),
      h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]), h.outer.harr aX (by decide)]) rfl)
    fun _ ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ => ⟨h.keep hm k (k.gpr (by decide)), hsi, hcx, hbx⟩

private theorem tail_ok (p : CdP) (s : State) (h : ML p s) :
    WP isa (.seq loadBE (.block decLow)) s fun _ => True := by
  obtain ⟨hp, hsi, hcx, hbx⟩ := h
  have hk := hp.base.k1
  have hk' := hp.base.k2
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hZ := hp.good.2
  have hs := hp.base.dom.take p.k
  refine WP.seq (WP.mono (loadBE_ok (w := p.w) hp.outer.scr hsi hcx hbx hp.base.plen
    (by omega) (by omega) rfl (by omega)
    (fun i hi => hs.rd i (by rw [hp.base.plen]; exact hi)) (fun i hi => hs.val i _)
    (fun i hi => Or.inr (by have := hs.out i (by rw [hp.base.plen]; exact hi); omega)))
    fun u ⟨_, _, k⟩ => ?_)
  have hbx' : u.gpr .rbx = off p.B (slot p.w aX) := (k.gpr (by decide)).trans hbx
  have scr := hp.outer.scr.congr k.2.2
  exact WP.mono (WP.keep [.rax]
    (Q := fun t => t.mem = u.mem.writeW (off p.B (slot p.w aX)) (word u.mem p.B (slot p.w aX) - 1))
    (by unfold decLow; xrun [State.ea, at0, hbx',
      show off p.B (slot p.w aX) + BitVec.ofInt 64 0 = off p.B (slot p.w aX) from by simp,
      scr.ld (show slot p.w aX + 8 ≤ p.Z by omega), scr.st (show slot p.w aX + 8 ≤ p.Z by omega)]) rfl)
    (fun _ _ => True.intro)

private theorem zero_parent (p : CdP) (s : State) (h : Parent p s) : WP isa (zeroArr aX) s (Parent p) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot p.w aX (show 31 < 32 by decide)
  have hZ := h.good.2
  refine WP.mono (zeroArr_ok h.good.1 hZ (by omega) (by omega) (show aX < 8 by decide))
    fun _ ⟨_, ho, k⟩ => ?_
  have hf : Frm p.B [(slot p.w aX, 8 * (p.w + 2))] _ _ := Frm.of_outside ho (by simp)
  exact (h.array hf (fun r he => by rw [List.mem_singleton.mp he]; exact ⟨by omega, by omega⟩)
    k (k.gpr (by decide))).1

private def regs (p : CdP) (r : Reg) : BitVec 64 :=
  if r = .rdi then p.B else if r = .rsi then p.dp else if r = .rcx then BitVec.ofNat 64 p.k else off p.B (slot p.w aX)

theorem minus_ct : RelCT isa (Two Parent)
    (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) fun _ _ => True := by
  change RelCT isa (Two Parent) (.seq (zeroArr aX) (.seq (.block loads) (.seq loadBE (.block decLow)))) _
  refine RelCT.seq (R := Two Parent)
    (two_post (two_map CdP.ows (fun _ _ h => ⟨_, h.good.1, h.good.2⟩)
      (zeroArr_ct (by decide) (by taint_decide))) zero_parent) ?_
  exact (pin_ct (Ψ := fun (_ : CdP) (_ : State) => True) [.rdi] [.rdi, .rsi, .rcx, .rbx] regs
    (pins_rdiB CdP.B fun _ _ h => h.outer.rdi) (by taint_decide)
    (fun p s h => WP.mono (loads_ok p s h) fun t ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ht.1.outer.rdi
      · exact ht.2.1
      · exact ht.2.2.1
      · exact ht.2.2.2)
    (by taint_decide)
    (fun p s h => WP.seq (WP.mono (loads_ok p s h) fun u hu => tail_ok p u hu))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.X86_64.CheckDomain
