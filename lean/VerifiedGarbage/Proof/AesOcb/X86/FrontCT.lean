module
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesOcb.X86.Entry

import VerifiedGarbage.Proof.AesOcb.X86.CTBase
meta import VerifiedGarbage.Proof.AesOcb.X86.CTBase
import VerifiedGarbage.Proof.AesOcb.X86.Nonce
meta import VerifiedGarbage.Proof.AesOcb.X86.Nonce
import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
meta import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
import VerifiedGarbage.Proof.AesOcb.X86.Run
meta import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.AesNi.Imc
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.Aes.X86.Decrypt
import VerifiedGarbage.Proof.Aes.X86.Keys
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesOcb.X86.Hash
import VerifiedGarbage.Proof.AesOcb.X86.LNtz
import VerifiedGarbage.Proof.AesOcb.X86.Offset0
import VerifiedGarbage.Proof.AesOcb.X86.Seal
import VerifiedGarbage.Proof.AesOcb.X86.Setup
import VerifiedGarbage.Proof.AesOcb.X86.TagIO
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Spec.Ocb.Contract
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Body
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Imc
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBranches
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyMemory
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyPost
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeySteps
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Loops
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
meta import VerifiedGarbage.Proof.Aes.X86.Decrypt
meta import VerifiedGarbage.Proof.Aes.X86.Keys
meta import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
meta import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
meta import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.AesOcb.X86.Hash
meta import VerifiedGarbage.Proof.AesOcb.X86.LNtz
meta import VerifiedGarbage.Proof.AesOcb.X86.Offset0
meta import VerifiedGarbage.Proof.AesOcb.X86.Seal
meta import VerifiedGarbage.Proof.AesOcb.X86.Setup
meta import VerifiedGarbage.Proof.AesOcb.X86.TagIO
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Spec.Ocb.Contract

/-!
# AES-OCB on x86: the entry, the setup and `Offset_0` in constant time

Untrusted: everything here is checked by Lean. The entry addresses only the
stack and `W` (`entry_ct`); `setup` doubles `L_*` from the key context,
whose address it loads from its slot (`setup_ct`); `nonceBlock` copies the
nonce to an address computed from its length, loaded from its slot
(`nonceBlock_ct`); then a call and `Offset_0`, which addresses only `W`
(`nonce_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct arg0_ok argIn_of LoopPre)

/-- The entry. -/
theorem entry_ct (p : Prm) : CT (fun s => onePre s ∧ prmOf s = p) ocbEntry := by
  rw [ocbEntry_eq]
  refine CT.seq (J := fun s => s.gpr .eax = p.W ∧ s.gpr .esp = p.SP)
    (CT.taint [.esp] (pin1 (x := p.SP) fun s h => by rw [← h.2]; rfl) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (pin2 fun _ h => h) (by taint_decide))
  have Ao := argsOk_of hs.1
  refine WP.mono (arg0_ok (argIn_of Ao.rA Ao.fa (i := 10) (by decide))) fun s' ⟨ax, sp⟩ => ⟨?_, ?_⟩
  · rw [ax, ← hs.2]; rfl
  · rw [sp, ← hs.2]; rfl

/-- `L_$`, `L_0` and the checksum. -/
theorem setup_ct {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) : CT I (.block setup) := by
  show CT I (.block (([.mov .ebx (slot ctxO)] : List Instr) ++ (dbl .ebx 240 ldO ++ dbl .ebp ldO l0O ++ zero4 ckO)))
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ebx = p.K)
      (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_)
      (CT.taint [.ebp, .ebx] (pin2 fun _ h => h) (by taint_decide)))
  have E := hI s hs
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [E.ebp], by gregs [hc]⟩

/-- The nonce block. -/
theorem nonceBlock_ct {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) : CT I nonceBlock := by
  unfold nonceBlock
  refine CT.seq (J := fun s => Env p s ∧ LoopPre s p.N (p.W + BitVec.ofNat 32 (128 - p.nl)) p.nl)
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).ebp) (by taint_decide)) (fun s hs => ?_) ?_
  · obtain ⟨s₂, run₂, E₂, lp, -⟩ := nonceHead_ok L (hI s hs)
    exact WP.of_runBlock ⟨s₂, run₂, E₂, lp⟩
  refine CT.seq (J := Env p) (copyLoop_ct (pin3 fun _ h => ⟨h.2.edi, h.2.edx, h.2.ecx⟩))
    (fun s h => WP.mono (copyW_ok L h.1 (d := 128 - p.nl) (n := p.nl) (by have := L.nl15; omega) h.2) fun _ h' => h'.1) ?_
  rw [← List.singleton_append (x := Instr.mov .ecx (slot nlO))]
  refine RelCT.block_append
    (CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .ecx = BitVec.ofNat 32 p.nl)
      (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide)) (fun s (E : Env p s) => ?_)
      (CT.taint [.ebp, .ecx] (pin2 fun _ h => h) (by taint_decide)))
  have hnl := E.slots.nlen
  simp only [slotv_eq] at hnl
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hnl], by gregs [E.ebp], by gregs [hnl]⟩

/-- `Offset_0`. -/
theorem nonce_ct (v : BlocksImpl) {I : State → Prop} {p : Prm} (L : Lay p) (hI : ∀ s, I s → Env p s) :
    CT I (nonce (callees v)) := by
  unfold nonce
  refine CT.seq (J := Env p) (nonceBlock_ct L hI) (fun s hs => ?_) ?_
  · have E := hI s hs
    refine WP.mono (nonceBlock_ok L E) fun s₁ P₁ => ?_
    have F₁ : Frame (wR p) s.mem s₁.mem := frame_wR P₁.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact inW_wR p (.inl (by decide))
      · exact inW_wR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    exact E.mut L (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₁.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₁.rd P₁.wr (wR_mut F₁)
  refine CT.seq (J := Env p) (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inl rfl) fun _ h => h)
    (fun s E => WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (oneBlock_ok E tmpO) (DReg.w L E (d := tmpO) (n := 1) (by decide) (.inl (by decide)))) fun _ P => P.env)
    (CT.taint [.ebp] (pin_ebp fun s h => h.ebp) (by taint_decide))

end VG.Proof.AesOcb.X86
