module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SSteps
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SSteps
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: `signMain` in constant time

The pieces between the calls are checked by the taint analysis from the
frame's public slots (`s_taintS`), with `SS`'s steps (`SSteps.lean`) for
what correctness says after them; the calls of `H`'s streaming functions are
of the same addresses with the same public arguments in both runs (`s_init`,
`s_upd`, `s_updExt` for the salt, where it is, and `s_fin`), and so is MGF1
(`s_mgf`); the private-key operation is constant time for its contract,
whose public data (the registers, its stack arguments, `n` and `e`) the
entry's public data fix (`privS_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sHD oEm oSt oDig oBuf oW oRsa scr lay)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor initF updF finF ldFn)
open VG.Proof.RsaOaep.X86_64 (decStack fb Lay Rep upd nW lenOf Calls frT FnsD two_initF two_updF two_updExtF
  two_finF MQ MFit mgf_ct nopin sizes e_entry_regs outR below_subD rdIn_entry)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK PrivImpl)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

theorem sks_sub {ks : List Nat} (h : ks.all (fun k => decide (k ∈ vKs ∨ k = 33 ∨ k = 44)) = true) :
    ∀ k ∈ ks, VKey k := fun k hk =>
  (of_decide_eq_true (List.all_eq_true.mp h k hk) : k ∈ vKs ∨ k = 33 ∨ k = 44)

/-- Table 18's words in their slots. -/
theorem SS.fnw {P : State → (Nat → BitVec 64) → Prop} {s t : State} (h : SS P s t) :
    t.mem.readW (off (fb s) (8 * 45)) 64 = VG.Proof.RsaOaep.X86_64.tw s.mem (stackArg s 18) 0 ∧
      t.mem.readW (off (fb s) (8 * 45 + 8)) 64 = VG.Proof.RsaOaep.X86_64.tw s.mem (stackArg s 18) 1 ∧
      t.mem.readW (off (fb s) (8 * 45 + 16)) 64 = VG.Proof.RsaOaep.X86_64.tw s.mem (stackArg s 18) 2 := by
  obtain ⟨-, -, ⟨V, W, R, hA, -⟩, -⟩ := h
  exact ⟨(R.fr 45 (by decide)).trans hA.sel.2.2.1.1, (R.fr 46 (by decide)).trans hA.sel.2.2.1.2.1,
    (R.fr 47 (by decide)).trans hA.sel.2.2.1.2.2⟩

/-! ## The calls of `H`'s streaming functions -/

section
variable {T : Spec.HashFns.Streaming} {Hs : Spec.Mgf1.Hash} (hT : StreamingOK T Hs)
  (hfn : ∀ a s, SSib kH kG a s → FnsD s T 18)

include hT hfn in
theorem s_init {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop}
    (hJ : ∀ s t, J s t → SS P s t ∧ t.gpr .rdi = off (stackArg s 14) oSt)
    (ht : ∃ hc, (taint.check (frT [] [] 2) (.block (ldFn (8 * 45))) hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) (initF (8 * 45)) fun _ _ => True :=
  two_initF hT decStack fb (fun a => stackArg a 14) (fun a => [outR a, sscrR a]) id
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 0)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 1)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 2) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, hdi⟩ := hJ s t hj
      have hf := h.fnw
      refine ⟨?_, ?_, ?_, ?_, S.calls h.1 (.inl rfl) (hfn a s S)⟩
      · rw [← S.fb, ← S.out_eq, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (.inl rfl) (i := 0) (by decide)]; exact hf.1
      · rw [← S.arg (j := 14) (by decide)]; exact hdi) (by decide) ht

include hT hfn in
/-- `update` with the `Ln s` bytes at `scratch + O s`, after `C s`. -/
theorem s_upd {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (O Ln C : State → Nat)
    (hJ : ∀ s t, SPre s → J s t → SS P s t ∧ SRU (off (stackArg s 14) (O s)) (Ln s) (C s) s t ∧
      O s + Ln s ≤ oRsa ∧ (O s + Ln s ≤ oSt ∨ oSt + T.S.stateBytes ≤ O s) ∧
      (O s + Ln s ≤ oW ∨ oW + 8 * T.scratch ≤ O s))
    (hs : ∀ a s, SSib kH kG a s → O s = O a ∧ Ln s = Ln a ∧ C s = C a)
    (ht : ∃ hc, (taint.check (frT [] [] 2) (.block (ldFn (8 * 45 + 8))) hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) (updF (8 * 45)) fun _ _ => True :=
  two_updF hT decStack fb (fun a => stackArg a 14) (fun a => [outR a, sscrR a]) id
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 0)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 1)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 2) O Ln
    (fun a => BitVec.ofNat 64 (C a)) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, ⟨hdi, hsi, hdx, hcx, h8⟩, b1, b2, b3⟩ := hJ s t S.1 hj
      obtain ⟨e1, e2, e3⟩ := hs a s S
      have hf := h.fnw
      rw [e1, e2] at b1 b2 b3
      refine ⟨?_, ?_, ?_, S.calls h.1 (.inl rfl) (hfn a s S), b1, b2, b3, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← S.fb, ← S.out_eq, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (.inl rfl) (i := 1) (by decide)]; exact hf.2.1
      · rw [← S.arg (j := 14) (by decide)]; exact hdi
      · rw [← e3]; exact hsi
      · rw [← S.arg (j := 14) (by decide), ← e1]; exact hdx
      · rw [← e2]; exact hcx
      · rw [← S.arg (j := 14) (by decide)]; exact h8) (by decide) ht

include hT hfn in
/-- `update` with the salt, where it is, after `C s`. -/
theorem s_updExt {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (C : State → Nat)
    (hJ : ∀ s t, SPre s → J s t → SS P s t ∧ SRU (stackArg s 12) (ssl s) (C s) s t)
    (hs : ∀ a s, SSib kH kG a s → C s = C a)
    (ht : ∃ hc, (taint.check (frT [] [] 2) (.block (ldFn (8 * 45 + 8))) hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) (updF (8 * 45)) fun _ _ => True :=
  two_updExtF hT decStack fb (fun a => stackArg a 14) (fun a => [outR a, sscrR a]) id
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 0)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 1)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 2) (fun a => stackArg a 12) ssl
    (fun a => BitVec.ofNat 64 (C a)) (fun a t ⟨s, S, hj⟩ => by
      have hp := S.1
      obtain ⟨h, ⟨hdi, hsi, hdx, hcx, h8⟩⟩ := hJ s t hp hj
      have A := hp.saltAt h.1 h.2.2.1.choose_spec.choose_spec.2.1
      have hf := h.fnw
      have e12 := S.arg (j := 12) (by decide)
      have esl := S.sl_eq
      have hin : ssaR a ∈ a.rd := by
        rw [← S.2.2.2.2.1, hp.hrd, show ssaR a = ssaR s by
          simp only [ssaR, S.arg (j := 12) (by decide), S.arg (j := 13) (by decide)]]
        simp [srd]
      refine ⟨?_, ?_, ?_, S.calls h.1 (.inl rfl) (hfn a s S), ?_, ?_, rdIn_entry hin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← S.fb, ← S.out_eq, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (.inl rfl) (i := 1) (by decide)]; exact hf.2.1
      · rw [← esl]; exact A.len
      · rw [← esl, ← e12]; exact hp.wSa
      · rw [← esl, ← e12, ← S.arg (j := 14) (by decide)]; exact A.dS
      · rw [← esl, ← e12, ← S.fb]; exact A.dK
      · rw [← S.arg (j := 14) (by decide)]; exact hdi
      · rw [← hs a s S]; exact hsi
      · rw [← e12]; exact hdx
      · rw [← esl]; exact hcx
      · rw [← S.arg (j := 14) (by decide)]; exact h8) (by decide) ht

include hT hfn in
theorem s_fin {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (O C : State → Nat)
    (hJ : ∀ s t, SPre s → J s t → SS P s t ∧ SRF (O s) (C s) s t ∧ (O s + 64 ≤ oSt ∨ (oSt + 256 ≤ O s ∧ O s + 64 ≤ oW)))
    (hs : ∀ a s, SSib kH kG a s → O s = O a ∧ C s = C a)
    (ht : ∃ hc, (taint.check (frT [] [] 2) (.block (ldFn (8 * 45 + 16))) hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) (finF (8 * 45)) fun _ _ => True :=
  two_finF hT decStack fb (fun a => stackArg a 14) (fun a => [outR a, sscrR a]) id
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 0)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 1)
    (fun a => VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a 18) 2) O
    (fun a => BitVec.ofNat 64 (C a)) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, ⟨hdi, hsi, hdx, hcx⟩, b1⟩ := hJ s t S.1 hj
      obtain ⟨e1, e3⟩ := hs a s S
      have hf := h.fnw
      rw [e1] at b1
      refine ⟨?_, ?_, ?_, S.calls h.1 (.inl rfl) (hfn a s S), b1, ?_, ?_, ?_, ?_⟩
      · rw [← S.fb, ← S.out_eq, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 14) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (.inl rfl) (i := 2) (by decide)]; exact hf.2.2
      · rw [← S.arg (j := 14) (by decide)]; exact hdi
      · rw [← e3]; exact hsi
      · rw [← S.arg (j := 14) (by decide), ← e1]; exact hdx
      · rw [← S.arg (j := 14) (by decide)]; exact hcx) (by decide) ht

end

/-! ## The call of the private-key operation -/

/-- The private operation's stack arguments are the anchor's. -/
theorem SSib.parg {a s : State} (S : SSib kH kG a s) {i : Nat} (hi : i < 14) : pArg s i = pArg a i := by
  match i, hi with
  | 0, _ => exact congrArg (off · oEm) (S.arg (j := 14) (by decide))
  | 1, _ => exact S.gpr (r := .rcx) (by decide)
  | 2, _ => exact S.arg (j := 0) (by decide)
  | 3, _ => exact S.arg (j := 1) (by decide)
  | 4, _ => exact S.arg (j := 2) (by decide)
  | 5, _ => exact S.arg (j := 3) (by decide)
  | 6, _ => exact S.arg (j := 4) (by decide)
  | 7, _ => exact S.arg (j := 5) (by decide)
  | 8, _ => exact S.arg (j := 6) (by decide)
  | 9, _ => exact S.arg (j := 7) (by decide)
  | 10, _ => exact S.arg (j := 8) (by decide)
  | 11, _ => exact S.arg (j := 9) (by decide)
  | 12, _ => exact congrArg (off · oRsa) (S.arg (j := 14) (by decide))
  | 13, _ => exact congrArg (· - BitVec.ofNat 64 1024) (S.arg (j := 15) (by decide))

/-- What `vg_rsa_private_checked`'s contract makes public, from the anchor. -/
theorem privS_view {a s t : State} (S : SSib kH kG a s) (h : SSet s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (privRdS s) (privWrS s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions (privRdS s) (privWrS s))) =
      (List.range 14).map (pArg a) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRdS s) (privWrS s)).mem
      ((t.callEntry.withRegions (privRdS s) (privWrS s)).gpr .rdx)
      ((t.callEntry.withRegions (privRdS s) (privWrS s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRdS s) (privWrS s)).mem
      ((t.callEntry.withRegions (privRdS s) (privWrS s)).gpr .r8)
      ((t.callEntry.withRegions (privRdS s) (privWrS s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  have hp := S.1
  have hfe : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hfE : FrS s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions (privRdS s) (privWrS s)).gpr r = t.gpr r :=
    fun hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · rw [e_entry_regs, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rcx) (by decide), S.gpr (r := .rdx) (by decide), S.gpr (r := .r8) (by decide),
      S.gpr (r := .r9) (by decide)]
  · have hi' := List.mem_range.mp hi
    rw [privS_args hp h _ _ hi', S.parg hi']
  · rw [g (by decide), g (by decide), h.rdx, h.rcx, State.withRegions_mem,
      FrS.bytes hfE hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega)]
    exact S.2.1.2.2.1.symm
  · rw [g (by decide), g (by decide), h.r8, h.r9, State.withRegions_mem,
      FrS.bytes hfE hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega)]
    exact S.2.1.2.2.2.1.symm

theorem privS_ct (v : PrivImpl) : RelCT isa (Two (SAt kH kG SSet)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := privK) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁, e₁⟩ := privS_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := privS_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := privS_covers S₁.1 j₁
  obtain ⟨c₂, w₂⟩ := privS_covers S₂.1 j₂
  exact ⟨privRdS s₁, privWrS s₁, privRdS s₂, privWrS s₂, privS_pre S₁.1 j₁, privS_pre S₂.1 j₂,
    ⟨List.map_inj_left.mp (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

end VG.Proof.RsaPss.X86_64
