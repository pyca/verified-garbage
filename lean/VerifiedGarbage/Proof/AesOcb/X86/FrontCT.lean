import VerifiedGarbage.Proof.AesOcb.X86.CTBase

/-!
# AES-OCB on x86: the entry, the setup and `Offset_0` in constant time

Untrusted: everything here is checked by Lean. The entry addresses only the
stack and `W` (`entry_ct`); `setup` doubles `L_*` from the key context,
whose address it loads from its slot (`setup_ct`); `nonceBlock` copies the
nonce to an address computed from its length, loaded from its slot
(`nonceBlock_ct`); then a call and `Offset_0`, which addresses only `W`
(`nonce_ct`).
-/

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
