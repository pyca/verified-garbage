module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopMain
public import VerifiedGarbage.Spec.SlhDsa.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`, correct

`sign(sk = rdi, msg = rsi, msg_len = rdx, ctx = rcx, ctx_len = r8,
addrnd = r9, sig = [rsp + 8], scratch = [rsp + 16])`
(`Impl.SlhDsa.X86_64.Shake.sign`): `ctx_len` against 256; if it is below,
the frame of nine words (`Pushed`, from the arguments: `SL.of`) and its
body (`body_ok`), which writes `slh_sign_internal` of the formatted message
to `sig` and returns 1; otherwise 2 (`sign_wp`, against `sgK`, the
contract spelled out a fact at a time).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Proof.Sha3.X86_64 (Upd wp_movm wp_mov32i)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)

/-! ## The contract, as the proof uses it -/

/-- `signContract`'s precondition, a fact at a time. -/
structure SG (p : Params) (stack : Nat) (s : State) : Prop where
  sp : stack ≤ (s.gpr .rsp).toNat
  top : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdi, p.skLen⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨s.gpr .r9, p.n⟩, ⟨stackArgAddr s 0, 16⟩]
  wr : s.wr = [⟨stackArg s 0, p.sigLen⟩, ⟨stackArg s 1, scratchWords * 8⟩]
  sk_sig : Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨stackArg s 0, p.sigLen⟩
  sk_scr : Region.Disjoint ⟨s.gpr .rdi, p.skLen⟩ ⟨stackArg s 1, scratchWords * 8⟩
  msg_sig : Region.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ⟨stackArg s 0, p.sigLen⟩
  msg_scr : Region.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ⟨stackArg s 1, scratchWords * 8⟩
  ctx_sig : Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ⟨stackArg s 0, p.sigLen⟩
  ctx_scr : Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ⟨stackArg s 1, scratchWords * 8⟩
  rnd_sig : Region.Disjoint ⟨s.gpr .r9, p.n⟩ ⟨stackArg s 0, p.sigLen⟩
  rnd_scr : Region.Disjoint ⟨s.gpr .r9, p.n⟩ ⟨stackArg s 1, scratchWords * 8⟩
  sig_scr : Region.Disjoint ⟨stackArg s 0, p.sigLen⟩ ⟨stackArg s 1, scratchWords * 8⟩
  sig_args : Region.Disjoint ⟨stackArg s 0, p.sigLen⟩ ⟨stackArgAddr s 0, 16⟩
  scr_args : Region.Disjoint ⟨stackArg s 1, scratchWords * 8⟩ ⟨stackArgAddr s 0, 16⟩
  ret_sk : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, p.skLen⟩
  ret_msg : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  ret_ctx : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  ret_rnd : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, p.n⟩
  ret_sig : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨stackArg s 0, p.sigLen⟩
  ret_scr : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨stackArg s 1, scratchWords * 8⟩
  ret_args : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨stackArgAddr s 0, 16⟩
  stk_sk : Region.Disjoint (below (s.gpr .rsp) stack) ⟨s.gpr .rdi, p.skLen⟩
  stk_msg : Region.Disjoint (below (s.gpr .rsp) stack) ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  stk_ctx : Region.Disjoint (below (s.gpr .rsp) stack) ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  stk_rnd : Region.Disjoint (below (s.gpr .rsp) stack) ⟨s.gpr .r9, p.n⟩
  stk_sig : Region.Disjoint (below (s.gpr .rsp) stack) ⟨stackArg s 0, p.sigLen⟩
  stk_scr : Region.Disjoint (below (s.gpr .rsp) stack) ⟨stackArg s 1, scratchWords * 8⟩
  stk_args : Region.Disjoint (below (s.gpr .rsp) stack) ⟨stackArgAddr s 0, 16⟩
  f_sk : (s.gpr .rdi).toNat + p.skLen ≤ 2 ^ 64
  f_msg : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  f_ctx : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  f_rnd : (s.gpr .r9).toNat + p.n ≤ 2 ^ 64
  f_sig : (stackArg s 0).toNat + p.sigLen ≤ 2 ^ 64
  f_scr : (stackArg s 1).toNat + scratchWords * 8 ≤ 2 ^ 64

/-- The signature of `slh_sign` of the arguments of `s` into the memory `m'`, and the result `r`. -/
def sgOut (p : Params) (s : State) (m' : Mem) (r : BitVec 32) : Prop :=
  match formatMessage (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) with
  | none => r = 2 ∧ bytesAt m' (stackArg s 0) p.sigLen = bytesAt s.mem (stackArg s 0) p.sigLen
  | some M' => r = 1 ∧ bytesAt m' (stackArg s 0) p.sigLen = signInternal p M' (bytesAt s.mem (s.gpr .rdi) p.skLen)
      (bytesAt s.mem (s.gpr .r9) p.n)

def sgK (p : Params) (stack : Nat) : Contract isa where
  pre s := SG p stack s
  post s s' := sgOut p s s'.mem ((s'.gpr .rax).setWidth 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-! ## The run -/

/-- The run of `sign` from the state `σ`, with `stack` bytes below `rsp`. -/
def SL.of (p : Params) (stack : Nat) (σ : State) : SL where
  B := σ.gpr .rsp - BitVec.ofNat 64 stack
  st := stack - 80
  S := stackArg σ 1
  sk := σ.gpr .rdi
  msg := σ.gpr .rsi
  len := σ.gpr .rdx
  ctx := σ.gpr .rcx
  ctxLen := σ.gpr .r8
  rnd := σ.gpr .r9
  sig := stackArg σ 0
  sigL := p.sigLen
  n := p.n

section
variable {p : Params} {stack : Nat} {σ : State}

theorem of_B (h : 80 ≤ stack) {d : Nat} (hd : d ≤ stack) :
    (SL.of p stack σ).B + BitVec.ofNat 64 (stack - 80 + 80 - d) = σ.gpr .rsp - BitVec.ofNat 64 d := by
  simp only [SL.of]
  rw [Offset.sub_ofNat_eq (σ.gpr .rsp) hd, show stack - 80 + 80 - d = stack - d by omega]

theorem of_SP (h : 80 ≤ stack) : (SL.of p stack σ).SP = σ.gpr .rsp - BitVec.ofNat 64 72 := by
  have := of_B (p := p) (σ := σ) h (d := 72) (by omega)
  rw [show stack - 80 + 80 - 72 = stack - 80 + 8 by omega] at this
  exact this

theorem of_RET (h : 80 ≤ stack) : (SL.of p stack σ).RET = ⟨σ.gpr .rsp, 8⟩ := by
  show (⟨(SL.of p stack σ).B + BitVec.ofNat 64 (stack - 80 + 80), 8⟩ : Region) = _
  simp only [SL.of]
  rw [show stack - 80 + 80 = stack by omega, BitVec.sub_add_cancel]

theorem of_ARGS (h : 80 ≤ stack) : (SL.of p stack σ).ARGS = ⟨stackArgAddr σ 0, 16⟩ := by
  show (⟨(SL.of p stack σ).B + BitVec.ofNat 64 (stack - 80 + 88), 16⟩ : Region) = _
  simp only [SL.of, stackArgAddr]
  rw [show stack - 80 + 88 = stack + 8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem of_STK (h : 80 ≤ stack) : (SL.of p stack σ).STK = below (σ.gpr .rsp) stack := by
  show (⟨(SL.of p stack σ).B, stack - 80 + 80⟩ : Region) = _
  simp only [SL.of]; congr 1; omega

theorem of_ok (hp : VPar p) (h : SG p stack σ) (h80 : 80 ≤ stack) (h62 : stack < 2 ^ 62)
    (hc : (σ.gpr .r8).toNat < 256) : (SL.of p stack σ).Ok := by
  have hS : (SL.of p stack σ).SCR = ⟨stackArg σ 1, scratchWords * 8⟩ := rfl
  have hR := of_RET (p := p) (σ := σ) h80
  have hK := of_STK (p := p) (σ := σ) h80
  have hA := of_ARGS (p := p) (σ := σ) h80
  have e : ((SL.of p stack σ).B).toNat = (σ.gpr .rsp).toNat - stack := by
    simp only [SL.of]; rw [toNat_sub_ofNat h.sp]
  refine ⟨by show (SL.of p stack σ).B.toNat + (stack - 80) + 104 ≤ 2 ^ 64; rw [e]; have := h.top; have := h.sp; omega, by simp only [SL.of]; omega, h.f_scr,
    h.f_sk, h.f_msg, h.f_ctx, h.f_rnd, h.f_sig, hc, hp.n, by simp only [SL.of]; rw [hp.sigLen]; omega,
    by rw [hS]; exact h.sk_scr.symm, by rw [hS]; exact h.msg_scr.symm, by rw [hS]; exact h.ctx_scr.symm,
    by rw [hS]; exact h.rnd_scr.symm, by rw [hS]; exact h.sig_scr.symm, by rw [hS, hA]; exact h.scr_args,
    by rw [hK]; exact h.stk_sk, by rw [hK]; exact h.stk_msg, by rw [hK]; exact h.stk_ctx, by rw [hK]; exact h.stk_rnd,
    by rw [hK]; exact h.stk_sig, by rw [hK, hS]; exact h.stk_scr, by rw [hR, hS]; exact h.ret_scr,
    by rw [hR]; exact h.ret_sig, h.sk_sig.symm, h.msg_sig.symm, h.ctx_sig.symm, h.rnd_sig.symm,
    by rw [hA]; exact h.sig_args⟩

end

/-! ## The frame -/

theorem sx256 : (BitVec.signExtend 64 (256 : BitVec 32)).toNat = 256 := by decide

/-- The frame's push. -/
theorem pushed_ok {p : Params} {stack : Nat} {σ s : State} (h : SG p stack σ) (h80 : 80 ≤ stack)
    (hgs : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s.gpr r = σ.gpr r) (h10 : s.gpr .r10 = stackArg σ 0)
    (h11 : s.gpr .r11 = stackArg σ 1) (hax : s.gpr .rax = 0) (hm : s.mem = σ.mem) (hrd : s.rd = σ.rd)
    (hwr : s.wr = σ.wr) :
    Pushed (SL.of p stack σ) σ.gpr σ.mem (pushed Impl.SlhDsa.X86_64.Shake.signRegs s) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hgs _ (by decide) (by decide) (by decide)
  have hn : 8 * Impl.SlhDsa.X86_64.Shake.signRegs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp]; have := h.sp; show 72 ≤ _; omega
  obtain ⟨hf, hr⟩ := pushRegs_mem s Impl.SlhDsa.X86_64.Shake.signRegs (by decide) hn
  have hSP := of_SP (p := p) (σ := σ) h80
  have hsp' : s.gpr .rsp - BitVec.ofNat 64 (8 * Impl.SlhDsa.X86_64.Shake.signRegs.length) = (SL.of p stack σ).SP := by
    rw [hsp, hSP]; rfl
  refine ⟨by rw [pushed_rd, hrd, h.rd]; show _ = [_, _, _, _, (SL.of p stack σ).ARGS]; rw [of_ARGS h80]; rfl, by rw [pushed_wr, hwr, h.wr, hsp']; rfl,
    by rw [pushed_rsp, hsp'], fun r hr h1 => by
      rw [pushed_gpr _ _ h1, hgs r (by intro e; subst e; revert hr; decide) (by intro e; subst e; revert hr; decide)
        (by intro e; subst e; revert hr; decide)],
    by rw [pushed_gpr _ _ (by decide), hgs _ (by decide) (by decide) (by decide)]; rfl, fun j hj => ?_, ?_⟩
  · have ea : (SL.of p stack σ).SP + BitVec.ofNat 64 (8 * j) =
        s.gpr .rsp - BitVec.ofNat 64 (8 * ((8 - j) + 1)) := by
      rw [hSP, hsp, Offset.sub_ofNat_eq (σ.gpr .rsp) (a := 8 * ((8 - j) + 1)) (b := 72) (by omega),
        show 72 - 8 * ((8 - j) + 1) = 8 * j by omega]
    show (pushRegs s _).mem.readW _ 64 = _
    rw [ea, hr (8 - j) (by simp only [Impl.SlhDsa.X86_64.Shake.signRegs, List.length_cons, List.length_nil]; omega)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hax
    · exact h11
    · exact hgs .r9 (by decide) (by decide) (by decide)
    · exact h10
    · exact hgs .r8 (by decide) (by decide) (by decide)
    · exact hgs .rcx (by decide) (by decide) (by decide)
    · exact hgs .rdx (by decide) (by decide) (by decide)
    · exact hgs .rsi (by decide) (by decide) (by decide)
    · exact hgs .rdi (by decide) (by decide) (by decide)
  · rw [← hm]
    refine hf.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(SL.of p stack σ).STK, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [hsp, of_STK h80]
    show Region.Sub ⟨σ.gpr .rsp - BitVec.ofNat 64 72, 72⟩ ⟨σ.gpr .rsp - BitVec.ofNat 64 stack, stack⟩
    exact Offset.sub_below _ (by omega) (by omega)

/-! ## The function -/

theorem fmt_some {ctx M : List Byte} (h : ctx.length ≤ 255) :
    formatMessage ctx M = some ([0, BitVec.ofNat 8 ctx.length] ++ ctx ++ M) := by
  simp only [formatMessage, show ¬ ctx.length > 255 by omega, ite_false]
  simp [toByte]

theorem fmt_none {ctx M : List Byte} (h : 255 < ctx.length) : formatMessage ctx M = none := by
  simp only [formatMessage, h, ite_true]

theorem pre_nm : (Code.block [.mov .r10 (.mem (Impl.SlhDsa.X86_64.Shake.stk 8)),
    .mov .r11 (.mem (Impl.SlhDsa.X86_64.Shake.stk 16)), .mov32 .rax (.imm 0)] : Prog isa).allInstrs
    (fun i => !loadsMxcsr i) = true := rfl

/-- The comparison of `ctx_len` with 256. -/
theorem cmp_ok (σ : State) : WP isa (.block [.alu .cmp .r8 (.imm 256)]) σ fun s => s.gpr = σ.gpr ∧
    s.mem = σ.mem ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.cf = some (decide ((σ.gpr .r8).toNat < 256)) :=
  Fors.wp_cmpiC (s := σ) fun _ g m r w _ c => WP.block_nil ⟨g, m, r, w, by rw [c, sx256]⟩

/-- The loads of the stack arguments before the frame. -/
theorem preload_ok {p : Params} {stack : Nat} {σ s₁ : State} (hK : SG p stack σ)
    (h : s₁.gpr = σ.gpr ∧ s₁.mem = σ.mem ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr) :
    WP isa (.block [.mov .r10 (.mem (Impl.SlhDsa.X86_64.Shake.stk 8)),
        .mov .r11 (.mem (Impl.SlhDsa.X86_64.Shake.stk 16)), .mov32 .rax (.imm 0)]) s₁ fun s₄ =>
      (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s₄.gpr r = σ.gpr r) ∧ s₄.gpr .r10 = stackArg σ 0 ∧
        s₄.gpr .r11 = stackArg σ 1 ∧ s₄.gpr .rax = 0 ∧ s₄.mem = σ.mem ∧ s₄.rd = σ.rd ∧ s₄.wr = σ.wr := by
  obtain ⟨g₁, m₁, r₁, w₁⟩ := h
  have htop := hK.top
  have hin : ∀ {d : Nat}, d + 8 ≤ 24 → 8 ≤ d → InRegions (s₁.rd ++ s₁.wr) (σ.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    fun h1 h2 => ⟨⟨stackArgAddr σ 0, 16⟩, by rw [r₁, hK.rd]; simp, by
      show Region.Contains ⟨σ.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 16⟩ _ 8
      exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  exact wp_movm (a := σ.gpr .rsp + BitVec.ofNat 64 8) (by rw [stk_ea, g₁])
    (hin (by omega) (by omega)) fun s₂ u₂ => wp_movm (a := σ.gpr .rsp + BitVec.ofNat 64 16)
      (by rw [stk_ea, u₂.other _ (by decide), g₁]) (by rw [u₂.rd, u₂.wr]; exact hin (by omega) (by omega))
      fun s₃ u₃ => wp_mov32i fun s₄ u₄ => WP.block_nil ⟨fun r h1 h2 h3 => by
          rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, g₁],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁]; rfl,
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁]; rfl, by rw [u₄.gpr]; rfl,
        by rw [u₄.mem, u₃.mem, u₂.mem, m₁], by rw [u₄.rd, u₃.rd, u₂.rd, r₁],
        by rw [u₄.wr, u₃.wr, u₂.wr, w₁]⟩

theorem sign_wp {p : Params} (hp : VPar p) (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.X86_64.Shake.Fns} (ht : f.t4 = T.code) (F : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f))
    {stack : Nat} (hst : T.stack + 104 ≤ stack) (hFs : F.stack + 80 ≤ stack) (h62 : stack < 2 ^ 62) {σ : State}
    (hK : SG p stack σ) :
    WP isa (Impl.SlhDsa.X86_64.Shake.sign p f) σ fun s' => abiPreserved σ s' ∧ (sgK p stack).post σ s' := by
  have h80 : 80 ≤ stack := by omega
  have hsp := hK.sp
  have htop := hK.top
  unfold Impl.SlhDsa.X86_64.Shake.sign
  refine WP.seq (WP.mono_mx (show (Code.block [.alu .cmp .r8 (.imm 256)] : Prog isa).allInstrs
      (fun i => !loadsMxcsr i) = true from rfl)
    (Fors.wp_cmpiC (s := σ) (Q := fun s₁ => s₁.gpr = σ.gpr ∧ s₁.mem = σ.mem ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr ∧
      s₁.cf = some (decide ((σ.gpr .r8).toNat < 256))) fun s₁ g₁ m₁ r₁ w₁ _ c₁ =>
      WP.block_nil ⟨g₁, m₁, r₁, w₁, by rw [c₁, sx256]⟩) fun s₁ ⟨g₁, m₁, r₁, w₁, c₁⟩ mx₁ => ?_)
  refine WP.ite _ (Fors.eval_b c₁) (fun hc => ?_) (fun hc => ?_)
  · -- `ctx_len < 256`: the frame
    simp only [decide_eq_true_eq] at hc
    have hin : ∀ {d : Nat}, d + 8 ≤ 24 → 8 ≤ d → InRegions (s₁.rd ++ s₁.wr) (σ.gpr .rsp + BitVec.ofNat 64 d) 8 :=
      fun h1 h2 => ⟨⟨stackArgAddr σ 0, 16⟩, by rw [r₁, hK.rd]; simp, by
        show Region.Contains ⟨σ.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 16⟩ _ 8
        exact Offset.contains _ (by omega) (by omega) (by omega)⟩
    refine WP.seq (WP.mono_mx pre_nm (Q := fun (s₄ : State) => (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax →
          s₄.gpr r = σ.gpr r) ∧ s₄.gpr .r10 = stackArg σ 0 ∧ s₄.gpr .r11 = stackArg σ 1 ∧ s₄.gpr .rax = 0 ∧
          s₄.mem = σ.mem ∧ s₄.rd = σ.rd ∧ s₄.wr = σ.wr)
      (wp_movm (a := σ.gpr .rsp + BitVec.ofNat 64 8) (by rw [stk_ea, g₁])
      (hin (by omega) (by omega)) fun s₂ u₂ => wp_movm (a := σ.gpr .rsp + BitVec.ofNat 64 16)
        (by rw [stk_ea, u₂.other _ (by decide), g₁]) (by rw [u₂.rd, u₂.wr]; exact hin (by omega) (by omega))
        fun s₃ u₃ => wp_mov32i fun s₄ u₄ => WP.block_nil ⟨fun r h1 h2 h3 => by
            rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, g₁],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁]; rfl,
          by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁]; rfl, by rw [u₄.gpr]; rfl,
          by rw [u₄.mem, u₃.mem, u₂.mem, m₁], by rw [u₄.rd, u₃.rd, u₂.rd, r₁],
          by rw [u₄.wr, u₃.wr, u₂.wr, w₁]⟩) fun s₄ hs₄ mx₄ => ?_)
    obtain ⟨hg₄, h10, h11, hax, hm₄, hr₄, hw₄⟩ := hs₄
    have hpush := pushed_ok (p := p) hK h80 hg₄ h10 h11 hax hm₄ hr₄ hw₄
    have hL : (SL.of p stack σ).Ok := of_ok hp hK h80 h62 hc
    have hsp₄ : s₄.gpr .rsp = σ.gpr .rsp := hg₄ _ (by decide) (by decide) (by decide)
    refine WP.frame (by decide) (by decide) (by decide) (by rw [hsp₄]; show 72 ≤ _; omega) ?_
    have eSP : σ.gpr .rsp - BitVec.ofNat 64 (8 * Impl.SlhDsa.X86_64.Shake.signRegs.length) = (SL.of p stack σ).SP := by
      rw [of_SP h80]; rfl
    refine WP.mono (body_ok T ht F ⟨⟨hp, hz, hh, rfl, rfl⟩, by simp only [SL.of]; omega, by simp only [SL.of]; omega,
      hL⟩ hpush) fun s₅ ⟨hsp₅, hwr₅, _, hcs₅, hax₅, hsig₅, hf₅, mx₅⟩ => ⟨?_, ?_, fun m u hm => ?_⟩
    · rw [hsp₅, pushed_rsp, hsp₄, of_SP h80]; rfl
    · rw [hwr₅, pushed_wr, hw₄, hK.wr, hsp₄, eSP]; rfl
    rw [hsp₄, eSP] at hm
    have hret : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ (SL.of p stack σ).FR := by
      show Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨(SL.of p stack σ).SP, 72⟩
      rw [of_SP h80]; exact Offset.base_disjoint_below _ (by omega)
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · by_cases e : r = .rsp
      · subst e
        show (popped .r11 9 s₅).gpr .rsp = _
        rw [popped_rsp, hsp₅, of_SP h80]; exact BitVec.sub_add_cancel _ _
      · show (popped .r11 9 s₅).gpr r = _
        rw [popped_gpr _ _ _ e (by intro e'; subst e'; revert hr; decide)]
        exact hcs₅ r hr e
    · show m.readW _ 64 = _
      rw [Thash4Avx.readW_frame hm fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hret,
        Thash4Avx.readW_frame hf₅ fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hK.ret_scr
          · rw [of_STK h80]; exact Offset.base_disjoint_below _ (by omega)
          · exact hK.ret_sig]
    · show (popped .r11 9 s₅).mxcsr.extractLsb' 6 10 = _
      rw [popped_mxcsr, mx₅, pushed_mxcsr, mx₄, mx₁]
    · show sgOut p σ m (BitVec.setWidth 32 ((popped .r11 9 s₅).gpr .rax))
      have hl : (bytesAt σ.mem (σ.gpr .rcx) (σ.gpr .r8).toNat).length = (σ.gpr .r8).toNat := bytesAt_length' _ _ _
      simp only [sgOut]
      rw [fmt_some (by rw [hl]; omega), hl]
      refine ⟨by rw [popped_gpr _ _ _ (by decide) (by decide), hax₅]; rfl, ?_⟩
      have hfr : Region.Sub (SL.of p stack σ).FR (below (σ.gpr .rsp) stack) := by
        have := hL.fr_stk (d := 0) (n := 72) (by omega)
        rw [of_STK h80] at this; simpa using this
      rw [bytesAt_frame hm (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hK.stk_sig.symm.sub_right hfr) (by have := hp.sigLt; omega)]
      exact hsig₅
  · -- `ctx_len ≥ 256`
    simp only [decide_eq_false_iff_not] at hc
    refine WP.mono_mx (show (Code.block [.mov32 .rax (.imm 2)] : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true
      from rfl) (wp_mov32i (Q := fun s₂ => s₂.gpr .rax = BitVec.ofNat 64 2 ∧ (∀ r, r ≠ .rax → s₂.gpr r = σ.gpr r) ∧
        s₂.mem = σ.mem) fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr]; rfl, fun r h => by rw [u₂.other _ h, g₁],
          by rw [u₂.mem, m₁]⟩) fun s₂ ⟨h2, hg, hm⟩ mx₂ => ?_
    refine ⟨⟨fun r hr => hg r (by intro e; subst e; revert hr; decide), by rw [hm], by
      show s₂.mxcsr.extractLsb' 6 10 = _; rw [mx₂, mx₁]⟩, ?_⟩
    show sgOut p σ s₂.mem ((s₂.gpr .rax).setWidth 32)
    have hl : (bytesAt σ.mem (σ.gpr .rcx) (σ.gpr .r8).toNat).length = (σ.gpr .r8).toNat := bytesAt_length' _ _ _
    simp only [sgOut]
    rw [fmt_none (by rw [hl]; omega), hm, h2]
    exact ⟨rfl, rfl⟩

end VG.Proof.SlhDsa.X86_64.SignTop
