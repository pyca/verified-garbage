module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskSetup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: output masks never control branches or addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The flag may differ between runs; only output pointers and byte counts are public. -/
structure MaskPre (p : GkP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  rdi : s.gpr .rdi = p.B
  room : 256 ≤ p.Z
  k : p.k < 2 ^ 31
  ld : p.ld < p.k
  x : word s.mem p.B (8 * sX) = off p.xp p.ld
  n : word s.mem p.B (8 * sXl) = BitVec.ofNat 64 (p.k - p.ld)
  width : word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k
  out : OutOk s p.B p.Z p.xp p.k
  flag : ∃ c : Bool, s.gpr .rax = BitVec.ofNat 64 c.toNat

private def maskVal (p : GkP) : Reg → BitVec 64
  | .rdi => p.B | .r11 => p.xp | .rcx => BitVec.ofNat 64 p.k | _ => 0

private theorem mask_regs (p : GkP) (s : State) (h : MaskPre p s) :
    WP isa (.block maskSetup) s fun t => ∀ r ∈ [.rdi, .r11, .rcx], t.gpr r = maskVal p r := by
  obtain ⟨c, hc⟩ := h.flag
  refine WP.mono (maskSetup_ok h.scr h.rdi h.room h.k h.ld h.x h.n h.width hc)
    fun t ⟨⟨hp, _, hcx, _⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans h.rdi
  · exact hp
  · exact hcx

private theorem mask_end (p : GkP) (s : State) (h : MaskPre p s) :
    WP isa maskX s fun t => t.gpr .rdi = p.B := by
  obtain ⟨c, hc⟩ := h.flag
  exact WP.mono (maskX_ok h.scr h.rdi h.room h.k h.ld h.x h.n h.width hc h.out)
    fun _ ⟨_, _, hd, _⟩ => hd

theorem mask_ct : RelCT isa (Two MaskPre) maskX (Two fun (p : GkP) s => s.gpr .rdi = p.B) :=
  pin_ct [.rdi] [.rdi, .r11, .rcx] maskVal (pins_rdiB GkP.B fun _ _ h => h.rdi)
    (by taint_decide) mask_regs (by taint_decide) mask_end

theorem mask_status_ct : RelCT isa (Two MaskPre) (seqs [maskX, .block status]) fun _ _ => True :=
  RelCT.seq mask_ct (two_taint [.rdi] (pins_rdiB GkP.B fun _ _ h => h) (by taint_decide))

end VG.Proof.Ffdh.X86_64.GenerateKey
