module

import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Front
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
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

/-! # FFDH on x86-64: initialize an odd modulus in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws loadArr)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The operands of `setWord aOne rcx`, whose index is zero. -/
def SWPre (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rcx = 0

private def SWRegs (L : Ws) (s : State) : Prop :=
  s.gpr .r8 = off L.B (slot L.w aOne) ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rcx = 0

private theorem setOne_ct : RelCT isa (Two SWPre) (setWord aOne .rcx) fun _ _ => True := by
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := SWRegs) [.rdi]
    (pins_of (fun L _ => L.B) fun L s ⟨⟨_, hg, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.rdi) (by taint_decide) fun L s h => ?_)
    (two_taint [.r8, .r12, .rcx] (pins_of (fun L r => if r = .r8 then off L.B (slot L.w aOne) else
      if r = .r12 then BitVec.ofNat 64 L.w else 0) fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  obtain ⟨⟨mi, hg, hZ⟩, h12, hcx⟩ := h
  have hH := hdr_lt_slot L.w 8 (show sArr aOne < 32 by decide)
  exact WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off L.B (slot L.w aOne))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sArr aOne) (by omega), hg.hdr.harr aOne (by decide)]) rfl)
    fun t ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

abbrev minvRest : List Instr :=
  ([.mov .rbx (.mem (at0 .rbx))] : List Instr) ++ minv ++
    [.store (hdr sMinv) .r15, .mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]

abbrev minvB : List Instr := ([.mov .rbx (.mem (hdr (sArr aN)))] : List Instr) ++ minvRest

private theorem m3_pin (a : MPub) (s : State) (h : M3 a s) :
    WP isa (.block [.mov .rbx (.mem (hdr (sArr aN)))]) s fun t =>
      t.gpr .rdi = off a.B (inner a.w) ∧ t.gpr .rbx = off (off a.B (inner a.w)) (slot a.wx aN) := by
  obtain ⟨mi, hc, _⟩ := h
  have hH := hdr_lt_slot a.wx 8 (show sArr aN < 32 by decide)
  exact WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off (off a.B (inner a.w)) (slot a.wx aN))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hc.good.scr.ld hH, hc.hdr.harr aN (by decide)]) rfl)
    fun t ⟨hbx, k⟩ => ⟨(k.gpr (by decide)).trans hc.rdi, hbx⟩

theorem m3_m4 (a : MPub) (s : State) (h : M3 a s) : WP isa (.block minvB) s (SWPre a.ws) := by
  obtain ⟨mi, hc, hodd⟩ := h
  refine WP.mono (minvBlock_ok hc.good (Nat.le_refl _) hodd) fun t ⟨_, hm, h12, _, hcx, k⟩ => ?_
  have o := writeW_outside s.mem (off a.B (inner a.w)) (d := 8 * sMinv) (t.gpr .r15) (by decide)
  rw [← hm] at o
  have f : Frm (off a.B (inner a.w)) [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o (by simp)
  have hc' := hc.of_minv f (fun r hr => Or.inl (List.mem_singleton.mp hr)) k.2.2 (k.gpr (by decide))
  exact ⟨⟨_, hc'.good, Nat.le_refl _⟩, h12, hcx⟩

private theorem minvB_ct : RelCT isa (Two M3) (.block minvB) (Two fun (a : MPub) s => SWPre a.ws s) := by
  unfold minvB
  refine RelCT.block_append (RelCT.seq
    (two_piece (Ψ := fun (a : MPub) t => (t.gpr .rdi = off a.B (inner a.w) ∧
      t.gpr .rbx = off (off a.B (inner a.w)) (slot a.wx aN)) ∧ WP isa (.block minvRest) t (SWPre a.ws))
      [.rdi] (pins_of (fun (a : MPub) _ => off a.B (inner a.w)) fun (a : MPub) s ⟨_, hc, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi) (by taint_decide)
      fun (a : MPub) s h => WP.and (m3_pin a s h) (WP.block_append_iff.mp (m3_m4 a s h)))
    (two_piece [.rdi, .rbx] (pins_of (fun (a : MPub) r => if r = .rdi then off a.B (inner a.w) else
      off (off a.B (inner a.w)) (slot a.wx aN)) fun (a : MPub) s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) (by taint_decide) fun _ _ h => h.2))

/-- Loading, inversion and the constant one use only public addresses and counts. -/
theorem wsMod_ct {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs)
    {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.rdi]) (.block (wsB1 sWs sl)) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW))])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl)), .mov .rbx (.mem (hdr (sArr aN)))]) hc₃).isSome = true) :
    RelCT isa (Two (M1 sp sl)) (seqs (wsSetup sl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sp sl)) fun _ _ => True := by
  refine RelCT.seqs_append (by simp [wsSetup]) (by simp [modSetup, loadArr]) (RelCT.seq (R := Two (M2 sp sl))
    (two_post (wsSetup_ct hsp hsl hspW hslW hT₁) (m1_m2 hsp hsl hspW hslW)) ?_)
  unfold modSetup
  refine RelCT.seqs_append (by simp [loadArr]) (by simp) (RelCT.seq (R := Two M3)
    (two_post (two_map MPub.bp (m2_lpre hsp hsl) (loadArr_ct (by decide) hT₂ hT₃)) (m2_m3 hsp hsl)) ?_)
  exact RelCT.seq minvB_ct (two_map MPub.ws (fun _ _ h => h) setOne_ct)

end VG.Proof.Ffdh.X86_64
