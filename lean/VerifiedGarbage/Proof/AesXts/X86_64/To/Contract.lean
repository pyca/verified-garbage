module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesXts.Spec

import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Call
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Contract

/-!
# XTS-AES of whole blocks on x86-64, out of place: the contract

Untrusted: the contract of the internal functions `vg_aes_xts_encrypt_to`
and `vg_aes_xts_decrypt_to`, which only the out-of-place data-unit functions
call: `(schedule = rdi, rounds = rsi, tweak = rdx, src = rcx, n = r8,
scratch = r9, dst = r10)`. They are `vg_aes_xts_encrypt` and
`vg_aes_xts_decrypt` (`modeX86_64 (xtsMode enc)`) with the blocks read from
`src` and written to `dst`, a buffer of their own: the `n` blocks at `dst`
are XTS of the `n` blocks at `src`, from the tweak at `tweak`, which is
replaced with the one after them. They may use the 16 bytes of stack below
the return address (`below rsp 16`), for calls of their own.

`xtsTo_call`: a call of such a function, from its contract (`WP.call`):
only the tweak, `dst`, the scratch buffer and the 24 bytes of stack below the
caller's `rsp` change. `xtsTo_rel`: such calls, with the same arguments in
both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.To

open VG VG.X86_64
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (toNat_rounds callEntry_frame)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_xts_encrypt_to` (`enc`) or `vg_aes_xts_decrypt_to`. -/
def xtsToX86_64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let src : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let dst : Region := ⟨s.gpr .r10, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    s.rd = [sched, src] ∧ s.wr = [iv, dst, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint dst ∧ sched.Disjoint scr ∧ src.Disjoint iv ∧
      src.Disjoint dst ∧ src.Disjoint scr ∧ iv.Disjoint dst ∧ iv.Disjoint scr ∧ dst.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint dst ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint src ∧ stack.Disjoint iv ∧ stack.Disjoint dst ∧
      stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r10).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat < 2 ^ 59 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1))
    let iv := bytesAt s.mem (s.gpr .rdx) 16
    Spec.Cbc.blocksAt s'.mem (s.gpr .r10) (s.gpr .r8).toNat =
        Spec.Xts.crypt (ciphOf enc (s.gpr .rsi).toNat w) iv
          (Spec.Cbc.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Xts.next iv (s.gpr .r8).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The 24 bytes below `rsp`: the return address of a call of such a
function, and the 16 bytes below it that it may use. -/
abbrev stk3 (s : State) : Region := below (s.gpr .rsp) 24

/-- What a call of an out-of-place whole-block function on `N` blocks needs. -/
structure XtPre (s : State) (W T Sr D S : Addr) (N R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = T
  rcx : s.gpr .rcx = Sr
  r8 : s.gpr .r8 = BitVec.ofNat 64 N
  r9 : s.gpr .r9 = S
  r10 : s.gpr .r10 = D
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 59
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  rt : (⟨Sr, 16 * N⟩ : Region).Disjoint ⟨T, 16⟩
  rd' : (⟨Sr, 16 * N⟩ : Region).Disjoint ⟨D, 16 * N⟩
  rs : (⟨Sr, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (stk3 s).Disjoint ⟨W, 240⟩
  stkR : (stk3 s).Disjoint ⟨Sr, 16 * N⟩
  stkT : (stk3 s).Disjoint ⟨T, 16⟩
  stkD : (stk3 s).Disjoint ⟨D, 16 * N⟩
  stkS : (stk3 s).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapR : Sr.toNat + 16 * N ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  rsp_lo : 24 ≤ (s.gpr .rsp).toNat
  rsp_hi : (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨Sr, 16 * N⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of an out-of-place whole-block function on `N` blocks leaves. -/
structure XtPost (enc : Bool) (s : State) (W T Sr D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩, stk3 s] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem Sr N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem ret8_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (stk3 s) := by
  rw [State.callEntry_rsp]
  exact below_sub (sp := s.gpr .rsp) (a := 8) (b := 24) (by decide) (by decide)

theorem stack16_sub (s : State) : Region.Sub (below (s.callEntry.gpr .rsp) 16) (stk3 s) := by
  rw [State.callEntry_rsp]
  exact below_callee _ 16

theorem callEntry_rsp_toNat {s : State} (h : 24 ≤ (s.gpr .rsp).toNat) :
    (s.callEntry.gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
  rw [State.callEntry_rsp, BitVec.toNat_sub]
  have := (s.gpr .rsp).isLt
  simp only [show (8 : BitVec 64).toNat = 8 from rfl]
  omega

/-- The callee's precondition, on entry to a call with the regions it is given. -/
theorem XtPre.to_pre {enc : Bool} {s : State} {W T Sr D S : Addr} {N R : Nat} (h : XtPre s W T Sr D S N R) :
    (xtsToX86_64 enc).pre
      (s.callEntry.withRegions [⟨W, 240⟩, ⟨Sr, 16 * N⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := Unit.toNat_n (show N < 2 ^ 60 by have := h.n; omega)
  have hsp := callEntry_rsp_toNat h.rsp_lo
  simp only [xtsToX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r10 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.r10, hR, hN, hsp]
  refine ⟨trivial, trivial, h.wt, h.wd, h.ws, h.rt, h.rd', h.rs, h.td, h.ts, h.ds,
    h.stkT.sub_left (ret8_sub s), h.stkD.sub_left (ret8_sub s), h.stkS.sub_left (ret8_sub s),
    h.stkW.sub_left (stack16_sub s), h.stkR.sub_left (stack16_sub s), h.stkT.sub_left (stack16_sub s),
    h.stkD.sub_left (stack16_sub s), h.stkS.sub_left (stack16_sub s), h.wrapT, h.wrapR, h.wrapD, h.wrapS,
    by have := h.rsp_lo; omega, by have := h.rsp_hi; omega, h.n, h.rounds⟩

theorem xtsTo_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 2)
    {s : State} {W T Sr D S : Addr} {N R : Nat} (h : XtPre s W T Sr D S N R) :
    WP isa (.call n c) s (XtPost enc s W T Sr D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := Unit.toNat_n (show N < 2 ^ 60 by have := h.n; omega)
  refine WP.call (k := xtsToX86_64 enc) ok nosp (by omega)
    (rd := [⟨W, 240⟩, ⟨Sr, 16 * N⟩]) (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.to_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  have hf' := Frame.below_mono hf (b := 24) (by omega) (by decide)
  refine ⟨hrd, hwr, hcs, by simpa using hf', ?_, ?_⟩ <;>
  · simp only [xtsToX86_64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r10 ≠ .rsp),
      h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r10, hR, hN] at hpost
    have fE := callEntry_frame s
    have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
    have b8 : Region.Sub (below (s.gpr .rsp) 8) (stk3 s) := below_sub (by decide) (by decide)
    have eW := Proof.Cmac.bytesAt_frame fE (p := W) (n := 16 * (R + 1))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((h.stkW.sub_right (Region.sub_prefix hRb)).sub_left b8).symm)
      (by omega)
    have eT := Proof.Cmac.bytesAt_frame fE (p := T) (n := 16)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkT.sub_left b8).symm)
      (by decide)
    have eR := Unit.blocksAt_frame fE (p := Sr) (n := N)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkR.sub_left b8).symm)
      (by have := h.wrapR; omega)
    rw [← hm₂]
    first
      | rw [hpost.1, eW, eT, eR]
      | rw [hpost.2, eT]

/-- Calls of an out-of-place whole-block function, with the same arguments in
both runs, are constant time. -/
theorem xtsTo_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (ct : ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T Sr D S : Addr, ∃ N R : Nat,
      XtPre s₁ W T Sr D S N R ∧ XtPre s₂ W T Sr D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, Sr, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.to_pre (enc := enc), h₂.to_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes, hsp⟩
  simp only [xtsToX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r10 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₁.r10, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9,
    h₂.r10, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- An implementation of the out-of-place whole-block functions,
`vg_aes_xts_encrypt_to` and `vg_aes_xts_decrypt_to` (with a variant's
suffix), as the out-of-place data-unit functions call them. -/
structure ToImpl where
  enc : Impl.Aes.X86_64.Blocks
  encDepth : enc.code.depth ≤ 2
  encOk : ∀ s, (xtsToX86_64 true).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 true).post s s'
  encCt : ConstantTime isa (xtsToX86_64 true).pre (xtsToX86_64 true).pub enc.code
  encNosp : NoSp enc.code
  encMxcsr : enc.code.allInstrs (fun i => !loadsMxcsr i) = true
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  dec : Impl.Aes.X86_64.Blocks
  decDepth : dec.code.depth ≤ 2
  decOk : ∀ s, (xtsToX86_64 false).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 false).post s s'
  decCt : ConstantTime isa (xtsToX86_64 false).pre (xtsToX86_64 false).pub dec.code
  decNosp : NoSp dec.code
  decMxcsr : dec.code.allInstrs (fun i => !loadsMxcsr i) = true
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true

end VG.Proof.AesXts.X86_64.To
