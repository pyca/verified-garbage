module
public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesXts.Spec

import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.AesCbc.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# XTS-AES of data units on x86-64: a call of a whole-block function

`xts_call`: a call of an implementation of `vg_aes_xts_encrypt` or
`vg_aes_xts_decrypt` (`enc` true or false) on `N` blocks at `D`, from the
tweak at `T`, with working space `S`, from its contract (`WP.call`): the
blocks are then XTS of them, the tweak the one after them, and only the
tweak, the blocks, `S` and the 16 bytes of stack below `rsp` change.
`xts_rel`: such calls, with the same arguments in both runs, are constant
time.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64
open VG.Proof.AesCbc.X86_64 (modeX86_64 toNat_rounds callEntry_frame)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- The 16 bytes below `rsp`, which a call and the call it makes use. -/
abbrev stk (s : State) : Region := below (s.gpr .rsp) 16

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = T
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 N
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 60
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (stk s).Disjoint ⟨W, 240⟩
  stkT : (stk s).Disjoint ⟨T, 16⟩
  stkD : (stk s).Disjoint ⟨D, 16 * N⟩
  stkS : (stk s).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩, stk s] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ret_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (stk s) := by
  rw [State.callEntry_rsp]
  exact below_sub (sp := s.gpr .rsp) (a := 8) (b := 16) (by decide) (by decide)

theorem stack_sub (s : State) : Region.Sub (below (s.callEntry.gpr .rsp) 8) (stk s) := by
  rw [State.callEntry_rsp]
  exact below_callee _ 8

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modeX86_64 (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds,
    h.stkT.sub_left (ret_sub s), h.stkD.sub_left (ret_sub s), h.stkS.sub_left (ret_sub s),
    h.stkW.sub_left (stack_sub s), h.stkT.sub_left (stack_sub s), h.stkD.sub_left (stack_sub s),
    h.stkS.sub_left (stack_sub s), h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modeX86_64 (AesXts.xtsMode enc)) ok nosp (by omega)
    (rd := [⟨W, 240⟩]) (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  have hf' := Frame.below_mono hf (b := 16) (by omega) (by decide)
  refine ⟨hrd, hwr, hcs, by simpa using hf', ?_, ?_⟩ <;>
  · simp only [modeX86_64, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN,
      Proof.AesXts.Unit.length_blocksAt] at hpost
    have fE := callEntry_frame s
    have hn := h.n
    have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
    have eW := Proof.Cmac.bytesAt_frame fE (p := W) (n := 16 * (R + 1))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((h.stkW.sub_right (Region.sub_prefix hRb)).sub_left
          (below_sub (sp := s.gpr .rsp) (a := 8) (b := 16) (by decide) (by decide))).symm)
      (by omega)
    have eT := Proof.Cmac.bytesAt_frame fE (p := T) (n := 16)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkT.sub_left (below_sub (sp := s.gpr .rsp) (a := 8) (b := 16) (by decide) (by decide))).symm)
      (by decide)
    have eD := blocksAt_frame fE (p := D) (n := N)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkD.sub_left (below_sub (sp := s.gpr .rsp) (a := 8) (b := 16) (by decide) (by decide))).symm)
      (by omega)
    rw [← hm₂]
    first
      | rw [hpost.1, eW, eT, eD]
      | rw [hpost.2, eT]

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes, hsp⟩
  simp only [modeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.X86_64.Unit
