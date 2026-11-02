module

public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Apply
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Apply
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream

/-!
# Streaming ChaCha20 on RISC-V: `apply`, constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/ChaCha20/PPC64LE/Stream/ApplyCT.lean`): two runs from states that
agree on the pointers, the length, the stack pointer and the number of bytes
of keystream left (which the contract lets `apply` leak) are related piece
by piece (`RelCT`): the taint analysis proves each piece without calls
constant time from the registers that hold public values (`taintRegs`),
which correctness determines in each run (`Apply.lean`) from those public
values; the calls of the block function and of `vg_chacha20_xor` are
constant time by their own proofs (`RelCT.call`), their arguments agreeing;
and the branches are on public values (`RelCT.ite`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.ChaCha20.RISCV64.Stream
open VG.Impl.ChaCha20.RISCV64.Xor (mov)

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- `F` of the entry state `a`, with the stack pointer of `a`. -/
abbrev Sp (F : State → State → Prop) (a x : State) : Prop := F a x ∧ x.sp = a.sp

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s a : State} {F : State → State → Prop} (h : WP isa c s (F a))
    (hs : s.sp = a.sp) : WP isa c s (Sp F a) := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, (Exec.sp he).trans hs⟩

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : APre a
  pb : APre b
  hst : st a = st b
  hdp : dp a = dp b
  ha2 : a.gpr .a2 = b.gpr .a2
  hsp : a.sp = b.sp
  hleft : N a = N b

theorem Two.eqL {a b : State} (h : Two a b) : L a = L b := by
  show (a.gpr .a2).toNat = (b.gpr .a2).toNat; rw [h.ha2]
theorem Two.eqO {a b : State} (h : Two a b) : O a = O b := by
  show N a % 64 = N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : Two a b) : H a = H b := by
  show min (N a % 64) (L a) = min (N b % 64) (L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : Two a b) : NB a = NB b := by
  show (L a - H a) / 64 = (L b - H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : Two a b) : T a = T b := by
  show (L a - H a) % 64 = (L b - H b) % 64; rw [h.eqH, h.eqL]

/-! ## The call of `vg_chacha20_xor` -/

/-- The arguments of the call of `vg_chacha20_xor`. -/
structure Args (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = st s₀ + BitVec.ofNat 64 192
  a1 : s.gpr .a1 = dp s₀ + BitVec.ofNat 64 (H s₀)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (64 * NB s₀)
  a3 : s.gpr .a3 = st s₀ + BitVec.ofNat 64 256
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]

theorem args_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (.block blocksArgs) s (Args s₀) :=
  WP.mono (args_exec h.s5 (h.w hp) (by rw [h.rd, hp.rd])) fun _ A =>
    ⟨A.a0, by rw [A.a1, h.s6], by rw [A.a2, h.a2], A.a3, by rw [A.rd, h.rd, hp.rd], by rw [A.wr, h.wr, hp.wr]⟩

theorem Args.covers {s₀ s : State} (h : Args s₀ s) :
    Covers ([] ++ [cpR s₀, blR s₀, wkR s₀]) (s.rd ++ s.wr) ∧ Covers [cpR s₀, blR s₀, wkR s₀] s.wr := by
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, HNB_le s₀⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  exact ⟨by rw [h.rd, h.wr, List.nil_append, List.nil_append]; exact Covers.of_sub hcov,
    by rw [h.wr]; exact Covers.of_sub hcov⟩

theorem Args.pre {s₀ s : State} (hp : APre s₀) (h : Args s₀ s) :
    Proof.ChaCha20.xorRISCV64.pre (s.callEntry.withRegions [] [cpR s₀, blR s₀, wkR s₀]) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  have hn : (BitVec.ofNat 64 (64 * NB s₀)).toNat = 64 * NB s₀ := toNat_ofNat_lt (by omega)
  simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, hn]
  exact ⟨trivial, trivial, (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀), hwrap,
    al4_of_al8 hp.st_al (by decide), al4_of_al8 hp.st_al (by decide)⟩

/-! ## The call of the block function -/

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a1 : s.gpr .a1 = st s₀ + BitVec.ofNat 64 64
  s5 : s.gpr .s5 = st s₀
  s6 : s.gpr .s6 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (T s₀)
  rd : s.rd = []
  wr : s.wr = [stR s₀, dR s₀]
  al : (st s₀).toNat % 8 = 0

theorem tailArgs_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) :=
  wp_mv fun s' u => wp_addi (by decide) fun s'' u' => WP.block_nil
    ⟨by rw [u'.other _ (by decide), u.gpr, h.s5], by rw [u'.gpr, u.other _ (by decide), h.s5],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.s5],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.s6],
      by rw [u'.other _ (by decide), u.other _ (by decide), h.s7],
      by rw [u'.rd, u.rd, h.rd, hp.rd], by rw [u'.wr, u.wr, h.wr, hp.wr], hp.st_al⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  s5 : s.gpr .s5 = st s₀
  s6 : s.gpr .s6 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (T s₀)

theorem TArgs.covers {s₀ s : State} (h : TArgs s₀ s) :
    Covers ([⟨st s₀, 64⟩] ++ [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨st s₀ + BitVec.ofNat 64 64, 256⟩] s.wr := by
  refine ⟨?_, ?_⟩
  · rw [h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
    · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩
  · rw [h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩

theorem TArgs.pre {s₀ s : State} (h : TArgs s₀ s) :
    Proof.ChaCha20.blockRISCV64.pre
      (s.callEntry.withRegions [⟨st s₀, 64⟩] [⟨st s₀ + BitVec.ofNat 64 64, 256⟩]) := by
  simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs),
    h.a0, h.a1]
  exact ⟨trivial, trivial, Offset.disjoint_base _ (by omega) (by omega), by have := h.al; omega,
    al4_of_al8 h.al (by decide)⟩

theorem TArgs.call {s₀ s : State} (h : TArgs s₀ s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) s (TAfter s₀) :=
  block_call h.a0 h.a1 (Offset.disjoint_base _ (by omega) (by omega)) (by have := h.al; omega)
    (al4_of_al8 h.al (by decide)) h.covers.1 h.covers.2
    fun _ k _ => ⟨by rw [k.cs .s5 (by decide), h.s5], by rw [k.cs .s6 (by decide), h.s6],
      by rw [k.cs .s7 (by decide), h.s7]⟩

/-! ## The pieces, related -/

section
variable {a b : State} (h : Two a b)
include h

theorem check_rel :
    RelCT isa (fun x y => x = a ∧ y = b) (.block check) fun x y => Sp Q0 a x ∧ Sp Q0 b y :=
  RelCT.post (taintRegs [.a0] (fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨h.hsp, fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr; exact h.hst) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact wp_sp (check_ok h.pa) rfl, by subst hy; exact wp_sp (check_ok h.pb) rfl⟩

theorem part1_rel (hle : L a ≤ N a) :
    RelCT isa (fun x y => Sp Q0 a x ∧ Sp Q0 b y) part1 fun x y => Sp Q1 a x ∧ Sp Q1 b y :=
  RelCT.post (taintRegs [.a0, .a1, .a2, .t3, .t5] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx.rest.other _ (by decide), hy.rest.other _ (by decide)]; exact h.hst
      · rw [hx.rest.other _ (by decide), hy.rest.other _ (by decide)]; exact h.hdp
      · rw [hx.rest.other _ (by decide), hy.rest.other _ (by decide)]; exact h.ha2
      · rw [hx.t3, hy.t3, h.eqO]
      · rw [hx.t5, hy.t5, h.eqO, h.eqL]) (by taint_decide))
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part1_ok h.pa hle hx) sx,
      wp_sp (part1_ok h.pb (by rw [← h.eqL, ← h.hleft]; exact hle) hy) sy⟩

theorem xor_rel :
    RelCT isa (fun x y => Sp Args a x ∧ Sp Args b y) (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor)
      fun _ _ => True := by
  have ecp : cpR b = cpR a := by simp only [cpR, h.hst]
  have ebl : blR b = blR a := by simp only [blR, h.hdp, h.eqH, h.eqNB]
  have ewk : wkR b = wkR a := by simp only [wkR, h.hst]
  refine RelCT.call Proof.ChaCha20.RISCV64.Xor.xor_correct Proof.ChaCha20.RISCV64.Xor.xor_ct []
    [cpR a, blR a, wkR a] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_
  have py := hy.pre h.pb
  have cy := hy.covers
  rw [ecp, ebl, ewk] at py cy
  refine ⟨hx.pre h.pa, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' x (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' x (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.a3 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.a3 ∉ linkRegs),
    hx.a0, hx.a1, hx.a2, hx.a3, hy.a0, hy.a1, hy.a2, hy.a3, h.hst, h.hdp, h.eqH, h.eqNB, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem part2_rel :
    RelCT isa (fun x y => Sp Q1 a x ∧ Sp Q1 b y) part2 fun x y => Sp Q2 a x ∧ Sp Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part2_ok h.pa hx) sx, wp_sp (part2_ok h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      rw [eval_zero, eval_zero, hx.a2, hy.a2, h.eqNB])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => Sp Args a x ∧ Sp Args b y) ?_ (xor_rel h)
  refine RelCT.post (taintRegs [.s5] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [hx.s5, hy.s5, h.hst]) (by taint_decide))
    fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨wp_sp (args_ok h.pa hx) sx, wp_sp (args_ok h.pb hy) sy⟩

theorem part3_rel : RelCT isa (fun x y => Sp Q2 a x ∧ Sp Q2 b y) part3 fun x y => Sp Q3 a x ∧ Sp Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp (part3_ok h.pa hx) sx, wp_sp (part3_ok h.pb hy) sy⟩
  refine RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      rw [eval_zero, eval_zero, hx.s7, hy.s7, h.eqT])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => Sp TArgs a x ∧ Sp TArgs b y)
    (RelCT.post (taintRegs [.s5] (fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => by
        refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.s5, hy.s5, h.hst]) (by taint_decide))
      fun x y ⟨⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩, _⟩ => ⟨wp_sp (tailArgs_ok h.pa hx) sx, wp_sp (tailArgs_ok h.pb hy) sy⟩) ?_
  refine RelCT.seq (R := fun x y => Sp TAfter a x ∧ Sp TAfter b y) ?_
    (taintRegs [.s5, .s6, .s7] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
      refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.s5, hy.s5, h.hst]
      · rw [hx.s6, hy.s6, h.hdp, h.eqH, h.eqNB]
      · rw [hx.s7, hy.s7, h.eqT]) (by taint_decide))
  have est : st b = st a := h.hst.symm
  refine RelCT.post (RelCT.call Proof.ChaCha20.RISCV64.block_verified.1 Proof.ChaCha20.RISCV64.block_verified.2.1
    [⟨st a, 64⟩] [⟨st a + BitVec.ofNat 64 64, 256⟩] fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ?_)
    fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => ⟨wp_sp hx.call sx, wp_sp hy.call sy⟩
  have py := hy.pre
  have cy := hy.covers
  rw [est] at py cy
  refine ⟨hx.pre, py, ?_, hx.covers.1, hx.covers.2, cy.1, cy.2⟩
  simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' x (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' x (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' y (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' y (by decide : Reg.a1 ∉ linkRegs),
    hx.a0, hx.a1, hy.a0, hy.a1, h.hst, sx, sy, h.hsp]
  exact ⟨trivial, trivial, trivial⟩

theorem apply_rel : RelCT isa (fun x y => x = a ∧ y = b) apply fun _ _ => True := by
  rw [apply_eq]
  have e4 : ∀ {s₀ x : State}, Q0 s₀ x →
      isa.eval (.nonzero .t4) x = some (decide (N s₀ < L s₀)) := fun {s₀ x} hx => by
    rw [eval_nonzero_ofNat x .t4 (by cases decide (N s₀ < L s₀) <;> decide) hx.t4]
    by_cases hh : N s₀ < L s₀ <;> simp [hh]
  refine RelCT.seq (check_rel h) (RelCT.ite (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
      rw [e4 hx, e4 hy, h.hleft, h.eqL])
    (taintRegs [] (fun x y ⟨⟨⟨_, sx⟩, ⟨_, sy⟩⟩, _⟩ => ⟨by rw [sx, sy, h.hsp], fun r hr => by simp at hr⟩)
      (by taint_decide)) ?_)
  by_cases hlt : N a < L a
  · refine RelCT.of_false fun x y hp => ?_
    have he := hp.2
    rw [e4 hp.1.1.1] at he
    simp [hlt] at he
  have hle : L a ≤ N a := by omega
  refine RelCT.seq (RelCT.mono (part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (part2_rel h) (RelCT.seq (part3_rel h) ?_))
  exact taintRegs [.s5] (fun x y ⟨⟨hx, sx⟩, ⟨hy, sy⟩⟩ => by
    refine ⟨by rw [sx, sy, h.hsp], fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.s5, hy.s5, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyRISCV64.pre a) (hb : Proof.ChaCha20.applyRISCV64.pre b)
    (hq : Proof.ChaCha20.applyRISCV64.pub a b) : Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct : ConstantTime isa Proof.ChaCha20.applyRISCV64.pre Proof.ChaCha20.applyRISCV64.pub apply :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (apply_rel (Two.of h₁ h₂ hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (s : State) (hs : Proof.ChaCha20.applyRISCV64.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyRISCV64.post s s' := by
  obtain ⟨t, s', he, hf⟩ := apply_correct (APre.of s hs)
  exact ⟨t, s', he, ⟨hf.1, Exec.sp he, hf.2.1⟩, hf.2.2⟩

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩]

theorem apply_verified : Verified RISCV64.target apply (Spec.ChaCha20.applyContract RISCV64.abi 0) :=
  Verified.of_correct apply_ok apply_ct (by
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, Proof.ChaCha20.applyRISCV64,
      RISCV64.abi, RISCV64.argRegs] [applySat] using applySat)

end VG.Proof.ChaCha20.RISCV64.Stream
