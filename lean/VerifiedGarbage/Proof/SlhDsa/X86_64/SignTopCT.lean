module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTop
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTop
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
public meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: constant time

Two runs from states that agree on the pointers and the lengths have the
same run `SL` (`SL.of`), and leak the same trace: each block by the taint
analysis, from the registers that hold pointers (the blocks of arguments,
with their displacements and immediates erased, `taintE`), and each call
by its contract (`RelCT.call`), whose public data each run's correctness
determines from the pointers and lengths alone; the runs are put together
along their correctness proofs (`Levels.relSeq`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (Arg kabs kpad ksqz callA)
open VG.Proof.MlKem.X86_64 (AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre)

/-- A block whose taint, with its displacements and immediates erased (`is'`), the analysis checks. -/
theorem taintE {P : State → State → Prop} {is is' : List Instr} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) (he : (Code.block is : Prog isa).mapBlocks Instr.erase = .block is')
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is') hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True := by
  refine Levels.taintR rs hr (hc := hc) ?_
  rw [← (taint_eraseInv.check (.block is) (Taint.ofRegs rs) hc rfl).1, he]; exact h

/-- A block of moves, whose analysis is that of the same block with its
numbers zeroed (`is₀`, which the kernel evaluates). -/
theorem taintS {P : State → State → Prop} {is is₀ : List Instr} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    (he : (Code.block is : Prog isa).mapBlocks Instr.erase = (Code.block is₀ : Prog isa).mapBlocks Instr.erase)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is₀) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True := by
  refine Levels.taintR rs hr (hc := hc) ?_
  rw [← (taint_eraseInv.check (.block is) (Taint.ofRegs rs) hc rfl).1, he,
    (taint_eraseInv.check (.block is₀) (Taint.ofRegs rs) hc rfl).1]; exact h

/-! ## The sponge's calls -/

section
variable {L : SL} (hL : L.Ok)

/-- What a call of the sponge needs of a state of each run. -/
abbrev InCtx (L : SL) (t : State) : Prop := ∃ g m₀, Ctx L g m₀ t

theorem inCtx_regs {P₁ P₂ : State → Prop} (h₁ : ∀ x, P₁ x → InCtx L x) (h₂ : ∀ x, P₂ x → InCtx L x) :
    ∀ x y, (P₁ x ∧ P₂ y) → ∀ r ∈ [Reg.rsp, .rbx], x.gpr r = y.gpr r := fun x y ⟨hx, hy⟩ r hr => by
  obtain ⟨_, _, cx⟩ := h₁ x hx
  obtain ⟨_, _, cy⟩ := h₂ y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [cx.rsp, cy.rsp]
  · rw [cx.rbx, cy.rbx]

/-- After the arguments of a call of `vg_keccak_absorb_scratch`. -/
abbrev KB (L : SL) (A : Addr) (l q : Nat) (t₁ : State) : Prop :=
  AbsorbArgs t₁ (at' L.S Layout.oStream) A (at' L.S (Layout.oStream + 200)) 136 q l ∧
    Covers ([⟨A, l⟩] ++ [stR L, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, swR L] t₁.wr ∧ t₁.gpr .rsp = L.SP

abbrev PB (L : SL) (q : Nat) (t₁ : State) : Prop :=
  PadArgs t₁ (at' L.S Layout.oStream) (at' L.S (Layout.oStream + 200)) 136 q ∧
    Covers ([] ++ [stR L, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, swR L] t₁.wr ∧ t₁.gpr .rsp = L.SP

abbrev SB (L : SL) (D : Addr) (len : Nat) (t₁ : State) : Prop :=
  SqueezeArgs t₁ (at' L.S Layout.oStream) D (at' L.S (Layout.oStream + 200)) 136 0 len ∧
    Covers ([] ++ [stR L, ⟨D, len⟩, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, ⟨D, len⟩, swR L] t₁.wr ∧
    t₁.gpr .rsp = L.SP

include hL in
theorem kabs_args (hst : 8 ≤ L.st) {src len pos : Arg} (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos)
    {A : Addr} {l q : Nat} (hl64 : l < 2 ^ 64) (hq : q < 136)
    (hAst : Region.Disjoint ⟨A, l⟩ (stR L)) (hAsw : Region.Disjoint ⟨A, l⟩ (swR L))
    (hAk : Region.Disjoint (below L.SP 16) ⟨A, l⟩) {t : State} (hc : InCtx L t) (hA : argV L t src = A)
    (hlv : argV L t len = BitVec.ofNat 64 l) (hpv : argV L t pos = BitVec.ofNat 64 q)
    (hAin : Covers [⟨A, l⟩] (t.rd ++ t.wr)) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, src, len,
      .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t₁ =>
      AbsorbArgs t₁ (at' L.S Layout.oStream) A (at' L.S (Layout.oStream + 200)) 136 q l ∧
      Covers ([⟨A, l⟩] ++ [stR L, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, swR L] t₁.wr ∧ t₁.gpr .rsp = L.SP := by
  obtain ⟨g, m₀, hc⟩ := hc
  refine args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, src),
    (.r8, len), (.r9, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv _ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hs | exact hl | exact hp | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
    (.rcx, src), (.r8, len), (.r9, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have hcw : Covers [stR L, swR L] t₁.wr := by rw [hw]; exact stR_cov hc
  refine ⟨?_, Covers.append_left (by rw [hr, hw]; exact hAin) (Covers.right hcw), hcw, hsp₁⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, hq, hl64, st_sw, hAst, hAsw, ?_, ?_, ?_⟩
  · exact v (.rdi) (.scr Layout.oStream) (.head _)
  · exact v (.rsi) (.imm 136) (.tail _ (.head _))
  · rw [v (.rdx) pos (.tail _ (.tail _ (.head _))), hpv]
  · rw [v (.rcx) src (.tail _ (.tail _ (.tail _ (.head _)))), hA]
  · rw [v (.r8) len (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), hlv]
  · exact v (.r9) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  · rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst
  · rw [hsp₁]; exact hAk
  · rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst

include hL in
theorem kabs_ct (hst : 8 ≤ L.st) {src len pos : Arg} (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos)
    {A : Addr} {l q : Nat} (hl64 : l < 2 ^ 64) (hq : q < 136)
    (hAst : Region.Disjoint ⟨A, l⟩ (stR L)) (hAsw : Region.Disjoint ⟨A, l⟩ (swR L))
    (hAk : Region.Disjoint (below L.SP 16) ⟨A, l⟩) {P₁ P₂ : State → Prop}
    (hP : ∀ t, P₁ t ∨ P₂ t → InCtx L t ∧ argV L t src = A ∧ argV L t len = BitVec.ofNat 64 l ∧
      argV L t pos = BitVec.ofNat 64 q ∧ Covers [⟨A, l⟩] (t.rd ++ t.wr))
    (hb : RelCT isa (fun a b => P₁ a ∧ P₂ b) (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip
      [Arg.scr Layout.oStream, .imm 136, pos, src, len, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d))
      fun _ _ => True) :
    RelCT isa (fun a b => P₁ a ∧ P₂ b) (kabs src len pos) fun _ _ => True := by
  unfold kabs callA
  refine Levels.relSeq (B₁ := KB L A l q) (B₂ := KB L A l q) hb (fun a ha => ?_) (fun b hb' => ?_) (RelCT.call
    Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct [⟨A, l⟩] [stR L, swR L]
    fun x y ⟨⟨hx, cx, wx, sx⟩, ⟨hy, cy, wy, sy⟩⟩ => ⟨absorb_pre hx, absorb_pre hy, ?_, cx, wx, cy, wy, by rw [sx, sy]⟩)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hP a (.inl ha); exact kabs_args hL hst hs hl hp hl64 hq hAst hAsw hAk h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hP b (.inr hb'); exact kabs_args hL hst hs hl hp hl64 hq hAst hAsw hAk h1 h2 h3 h4 h5
  · simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
      hx.rdi, hx.rsi, hx.rdx, hx.rcx, hx.r8, hx.r9, hy.rdi, hy.rsi, hy.rdx, hy.rcx, hy.r8, hy.r9, sx, sy, and_self]

include hL in
theorem kpad_args (hst : 8 ≤ L.st) {pos : Arg} (hp : ArgOk pos) {q : Nat} (hq : q < 136) {t : State}
    (hc : InCtx L t) (hpv : argV L t pos = BitVec.ofNat 64 q) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, pos, .imm 0x1f,
      .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t₁ =>
      PadArgs t₁ (at' L.S Layout.oStream) (at' L.S (Layout.oStream + 200)) 136 q ∧
      Covers ([] ++ [stR L, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, swR L] t₁.wr ∧ t₁.gpr .rsp = L.SP := by
  obtain ⟨g, m₀, hc⟩ := hc
  refine args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, .imm 0x1f),
    (.r8, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv _ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hp | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
    (.rcx, .imm 0x1f), (.r8, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have hcw : Covers [stR L, swR L] t₁.wr := by rw [hw]; exact stR_cov hc
  refine ⟨⟨v (.rdi) (.scr Layout.oStream) (.head _), v (.rsi) (.imm 136) (.tail _ (.head _)),
    by rw [v (.rdx) pos (.tail _ (.tail _ (.head _))), hpv],
    v (.r8) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by decide, hq, st_sw,
    by rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst, by rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst⟩,
    Covers.append_left Covers.nil (Covers.right hcw), hcw, hsp₁⟩

include hL in
theorem kpad_ct (hst : 8 ≤ L.st) {pos : Arg} (hp : ArgOk pos) {q : Nat} (hq : q < 136) {P₁ P₂ : State → Prop}
    (hP : ∀ t, P₁ t ∨ P₂ t → InCtx L t ∧ argV L t pos = BitVec.ofNat 64 q)
    (hb : RelCT isa (fun a b => P₁ a ∧ P₂ b) (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip
      [Arg.scr Layout.oStream, .imm 136, pos, .imm 0x1f, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d))
      fun _ _ => True) :
    RelCT isa (fun a b => P₁ a ∧ P₂ b) (kpad pos) fun _ _ => True := by
  unfold kpad callA
  refine Levels.relSeq (B₁ := PB L q) (B₂ := PB L q) hb (fun a ha => ?_) (fun b hb' => ?_) (RelCT.call
    Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct [] [stR L, swR L]
    fun x y ⟨⟨hx, cx, wx, sx⟩, ⟨hy, cy, wy, sy⟩⟩ => ⟨pad_pre hx, pad_pre hy, ?_, cx, wx, cy, wy, by rw [sx, sy]⟩)
  · obtain ⟨h1, h2⟩ := hP a (.inl ha); exact kpad_args hL hst hp hq h1 h2
  · obtain ⟨h1, h2⟩ := hP b (.inr hb'); exact kpad_args hL hst hp hq h1 h2
  · simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      hx.rdi, hx.rsi, hx.rdx, hx.r8, hy.rdi, hy.rsi, hy.rdx, hy.r8, sx, sy, and_self]

include hL in
theorem ksqz_args (hst : 8 ≤ L.st) {dst : Arg} (hd : ArgOk dst) {len : Nat} (hlen : len < 2 ^ 31) {D : Addr}
    (hDst : Region.Disjoint (stR L) ⟨D, len⟩) (hDsw : Region.Disjoint ⟨D, len⟩ (swR L))
    (hDk : Region.Disjoint (below L.SP 16) ⟨D, len⟩) {t : State} (hc : InCtx L t) (hD : argV L t dst = D)
    (hDin : Covers [⟨D, len⟩] t.wr) :
    WP isa (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip [Arg.scr Layout.oStream, .imm 136, .imm 0, dst,
      .imm len, .scr (Layout.oStream + 200)]).flatMap fun (d, a) => a.mov d)) t fun t₁ =>
      SqueezeArgs t₁ (at' L.S Layout.oStream) D (at' L.S (Layout.oStream + 200)) 136 0 len ∧
      Covers ([] ++ [stR L, ⟨D, len⟩, swR L]) (t₁.rd ++ t₁.wr) ∧ Covers [stR L, ⟨D, len⟩, swR L] t₁.wr ∧
      t₁.gpr .rsp = L.SP := by
  obtain ⟨g, m₀, hc⟩ := hc
  refine args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0), (.rcx, dst),
    (.r8, .imm len), (.r9, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv _ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hd | exact hlen | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0),
    (.rcx, dst), (.r8, .imm len), (.r9, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have hcw : Covers [stR L, ⟨D, len⟩, swR L] t₁.wr := by
    rw [hw]
    have h2 := stR_cov hc
    have hs : Covers [stR L] t.wr :=
      (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans h2
    have hw' : Covers [swR L] t.wr :=
      (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans h2
    exact Covers.cons hs (Covers.cons hDin hw')
  refine ⟨⟨v (.rdi) (.scr Layout.oStream) (.head _), v (.rsi) (.imm 136) (.tail _ (.head _)),
    v (.rdx) (.imm 0) (.tail _ (.tail _ (.head _))), by rw [v (.rcx) dst (.tail _ (.tail _ (.tail _ (.head _)))), hD],
    v (.r8) (.imm len) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
    v (.r9) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))),
    by decide, Nat.zero_le _, by omega, hDst, st_sw, hDsw, by rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst,
    by rw [hsp₁]; exact hDk, by rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst⟩,
    Covers.append_left Covers.nil (Covers.right hcw), hcw, hsp₁⟩

include hL in
theorem ksqz_ct (hst : 8 ≤ L.st) {dst : Arg} (hd : ArgOk dst) {len : Nat} (hlen : len < 2 ^ 31) {D : Addr}
    (hDst : Region.Disjoint (stR L) ⟨D, len⟩) (hDsw : Region.Disjoint ⟨D, len⟩ (swR L))
    (hDk : Region.Disjoint (below L.SP 16) ⟨D, len⟩) {P₁ P₂ : State → Prop}
    (hP : ∀ t, P₁ t ∨ P₂ t → InCtx L t ∧ argV L t dst = D ∧ Covers [⟨D, len⟩] t.wr)
    (hb : RelCT isa (fun a b => P₁ a ∧ P₂ b) (.block (([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip
      [Arg.scr Layout.oStream, .imm 136, .imm 0, dst, .imm len, .scr (Layout.oStream + 200)]).flatMap
      fun (d, a) => a.mov d)) fun _ _ => True) :
    RelCT isa (fun a b => P₁ a ∧ P₂ b) (ksqz dst len) fun _ _ => True := by
  unfold ksqz callA
  refine Levels.relSeq (B₁ := SB L D len) (B₂ := SB L D len) hb (fun a ha => ?_) (fun b hb' => ?_) (RelCT.call
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct []
      [stR L, ⟨D, len⟩, swR L]
    fun x y ⟨⟨hx, cx, wx, sx⟩, ⟨hy, cy, wy, sy⟩⟩ => ⟨squeeze_pre hx, squeeze_pre hy, ?_, cx, wx, cy, wy, by rw [sx, sy]⟩)
  · obtain ⟨h1, h2, h3⟩ := hP a (.inl ha); exact ksqz_args hL hst hd hlen hDst hDsw hDk h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := hP b (.inr hb'); exact ksqz_args hL hst hd hlen hDst hDsw hDk h1 h2 h3
  · simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
      hx.rdi, hx.rsi, hx.rdx, hx.rcx, hx.r8, hx.r9, hy.rdi, hy.rsi, hy.rdx, hy.rcx, hy.r8, hy.r9, sx, sy, and_self]

end

/-! ## `hashM'` -/

section
variable {L : SL} (hL : L.Ok)

/-- A state of the sponge, after `ℓ` bytes. -/
abbrev HS (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (ℓ : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ ∃ msg : List Byte, Repr t.mem (at' L.S Layout.oStream) 136 msg ∧ msg.length = ℓ

abbrev HSr (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (ℓ : Nat) (t : State) : Prop :=
  HS L g m₀ ℓ t ∧ t.gpr .rax = BitVec.ofNat 64 (ℓ % 136)

include hL in
theorem kabs_step {g : Reg → BitVec 64} {m₀ : Mem} (hst : 8 ≤ L.st) {src len pos : Arg} (hs : ArgOk src)
    (hl : ArgOk len) (hp : ArgOk pos) {A : Addr} {l : Nat} (hl64 : l < 2 ^ 64)
    (hAst : Region.Disjoint ⟨A, l⟩ (stR L)) (hAsw : Region.Disjoint ⟨A, l⟩ (swR L))
    (hAk : Region.Disjoint (below L.SP 16) ⟨A, l⟩) {ℓ : Nat} {t : State} (h : HS L g m₀ ℓ t)
    (hA : argV L t src = A) (hlv : argV L t len = BitVec.ofNat 64 l) (hpv : argV L t pos = BitVec.ofNat 64 (ℓ % 136))
    (hAin : Covers [⟨A, l⟩] (t.rd ++ t.wr)) :
    WP isa (kabs src len pos) t (HSr L g m₀ (ℓ + l)) := by
  obtain ⟨hc, msg, hR, hml⟩ := h
  refine kabs_ok hL hc hst hs hl hp hA hlv hl64 hAin hAst hAsw hAk hR (by rw [hml]; exact hpv)
    fun t' hc' hR' hx _ _ => ⟨⟨hc', _, hR', by rw [List.length_append, hml, bytesAt_length']⟩, ?_⟩
  rw [← Levels.ofNat_toNat64 (t'.gpr .rax), hx, hml, Nat.mod_add_mod]

end

/-- The argument blocks, as `taintS` checks them. -/
abbrev zArgs (as : List Arg) : List Instr := ([Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].zip as).flatMap fun (d, a) => a.mov d

section
variable {L : SL} (hL : L.Ok)

include hL in
theorem tail_ct {g₁ : Reg → BitVec 64} {m₁ : Mem} {g₂ : Reg → BitVec 64} {m₂ : Mem} (hst : 8 ≤ L.st) {ℓ q : Nat}
    (hpl : ℓ + 2 < 136) (hq : q = ℓ) {dst : Arg} (hd : ArgOk dst) {len : Nat} (hlen : len < 2 ^ 31) {D : Addr}
    (hD : ∀ g m₀ t', Ctx L g m₀ t' → argV L t' dst = D) (hDin : ∀ g m₀ t', Ctx L g m₀ t' → Covers [⟨D, len⟩] t'.wr)
    (hDst : Region.Disjoint (stR L) ⟨D, len⟩) (hDsw : Region.Disjoint ⟨D, len⟩ (swR L))
    (hDk : Region.Disjoint (below L.SP 16) ⟨D, len⟩)
    (hbd : RelCT isa (fun a b => Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b)
      (.block (zArgs [Arg.scr Layout.oStream, .imm 136, .imm 0, dst, .imm len, .scr (Layout.oStream + 200)]))
        fun _ _ => True) :
    RelCT isa (fun a b => HS L g₁ m₁ ℓ a ∧ HS L g₂ m₂ ℓ b) (.seq (kabs .sp (.imm 2) (.imm q))
      (.seq (kabs (.slot Impl.SlhDsa.X86_64.Shake.fCtx) (.slot Impl.SlhDsa.X86_64.Shake.fCtxLen) .ret)
      (.seq (kabs (.slot Impl.SlhDsa.X86_64.Shake.fMsg) (.slot Impl.SlhDsa.X86_64.Shake.fLen) .ret)
        (.seq (kpad .ret) (ksqz dst len))))) fun _ _ => True := by
  have hnB := hL.nB
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
  have hfrSt : Region.Disjoint ⟨L.SP, 2⟩ (stR L) := by
    have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (hL.scr_sub (o := Layout.oStream) (l := 200)
      (by rw [oStream_eq]; omega)); simpa only [e0] using this
  have hfrSw : Region.Disjoint ⟨L.SP, 2⟩ (swR L) := by
    have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (hL.scr_sub (o := Layout.oStream + 200) (l := 640)
      (by rw [oStream_eq]; omega)); simpa only [e0] using this
  have hfrCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [⟨L.SP, 2⟩] (t.rd ++ t.wr) := fun hc =>
    Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by rw [hc.rd, hc.wr]; simp, 0, by simp, by show 0 + 2 ≤ 72; omega⟩
  have hcCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [L.CTX] (t.rd ++ t.wr) := fun hc =>
    Covers.left (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hc.rd]; simp)
  have hmCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [L.MSG] (t.rd ++ t.wr) := fun hc =>
    Covers.left (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hc.rd]; simp)
  have hcSt : Region.Disjoint L.CTX (stR L) := hL.sCtx.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have hcSw : Region.Disjoint L.CTX (swR L) := hL.sCtx.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have hmSt : Region.Disjoint L.MSG (stR L) := hL.sMsg.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have hmSw : Region.Disjoint L.MSG (swR L) := hL.sMsg.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have cl : ∀ {g m₀ t}, Ctx L g m₀ t → argV L t (.slot Impl.SlhDsa.X86_64.Shake.fCtxLen) =
      BitVec.ofNat 64 L.ctxLen.toNat := fun hc => by
    show _ = _; rw [show argV L _ (.slot Impl.SlhDsa.X86_64.Shake.fCtxLen) = _ from hc.pCtxLen, Levels.ofNat_toNat64]
  have ml : ∀ {g m₀ t}, Ctx L g m₀ t → argV L t (.slot Impl.SlhDsa.X86_64.Shake.fLen) =
      BitVec.ofNat 64 L.len.toNat := fun hc => by
    show _ = _; rw [show argV L _ (.slot Impl.SlhDsa.X86_64.Shake.fLen) = _ from hc.pLen, Levels.ofNat_toNat64]
  subst q
  have hq' : ℓ % 136 = ℓ := Nat.mod_eq_of_lt (by omega)
  -- the frame's two bytes
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (ℓ + 2)) (B₂ := HSr L g₂ m₂ (ℓ + 2))
    (kabs_ct hL hst (src := .sp) (len := .imm 2) (pos := .imm ℓ) trivial (by dsimp only [ArgOk]; decide)
      (show ℓ < 2 ^ 31 by omega) (A := L.SP) (l := 2) (q := ℓ) (by decide) (by omega) hfrSt hfrSw
      (Offset.base_disjoint_below L.SP (by omega)).symm (fun t ht => by
        rcases ht with ⟨hc, _⟩ | ⟨hc, _⟩ <;> exact ⟨⟨_, _, hc⟩, rfl, rfl, rfl, hfrCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1⟩) fun x hx => ⟨_, _, hx.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .sp, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .sp) (len := .imm 2) (pos := .imm ℓ) trivial (by dsimp only [ArgOk]; decide)
      (show ℓ < 2 ^ 31 by omega) (by decide)
      hfrSt hfrSw (Offset.base_disjoint_below L.SP (by omega)).symm ha rfl rfl (by rw [hq']; rfl) (hfrCov ha.1))
    (fun b hb => kabs_step hL hst (src := .sp) (len := .imm 2) (pos := .imm ℓ) trivial (by dsimp only [ArgOk]; decide)
      (show ℓ < 2 ^ 31 by omega) (by decide)
      hfrSt hfrSw (Offset.base_disjoint_below L.SP (by omega)).symm hb rfl rfl (by rw [hq']; rfl) (hfrCov hb.1)) ?_
  -- the context string
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (ℓ + 2 + L.ctxLen.toNat)) (B₂ := HSr L g₂ m₂ (ℓ + 2 + L.ctxLen.toNat))
    (kabs_ct hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fCtx) (len := .slot Impl.SlhDsa.X86_64.Shake.fCtxLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial (A := L.ctx)
      (l := L.ctxLen.toNat) (q := (ℓ + 2) % 136) (BitVec.isLt _) (Nat.mod_lt _ (by decide)) hcSt hcSw (k16 hL.kCtx)
      (fun t ht => by
        rcases ht with ⟨⟨hc, _⟩, hx⟩ | ⟨⟨hc, _⟩, hx⟩ <;> exact ⟨⟨_, _, hc⟩, hc.pCtx, cl hc, hx, hcCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .ret, .slot 0, .slot 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fCtx) (len := .slot Impl.SlhDsa.X86_64.Shake.fCtxLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial
      (BitVec.isLt _) hcSt hcSw (k16 hL.kCtx) ha.1 ha.1.1.pCtx (cl ha.1.1) ha.2 (hcCov ha.1.1))
    (fun b hb => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fCtx) (len := .slot Impl.SlhDsa.X86_64.Shake.fCtxLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial
      (BitVec.isLt _) hcSt hcSw (k16 hL.kCtx) hb.1 hb.1.1.pCtx (cl hb.1.1) hb.2 (hcCov hb.1.1)) ?_
  -- the message
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (ℓ + 2 + L.ctxLen.toNat + L.len.toNat))
    (B₂ := HSr L g₂ m₂ (ℓ + 2 + L.ctxLen.toNat + L.len.toNat))
    (kabs_ct hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fMsg) (len := .slot Impl.SlhDsa.X86_64.Shake.fLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial (A := L.msg)
      (l := L.len.toNat) (q := (ℓ + 2 + L.ctxLen.toNat) % 136) (BitVec.isLt _) (Nat.mod_lt _ (by decide)) hmSt hmSw
      (k16 hL.kMsg)
      (fun t ht => by
        rcases ht with ⟨⟨hc, _⟩, hx⟩ | ⟨⟨hc, _⟩, hx⟩ <;> exact ⟨⟨_, _, hc⟩, hc.pMsg, ml hc, hx, hmCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .ret, .slot 0, .slot 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fMsg) (len := .slot Impl.SlhDsa.X86_64.Shake.fLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial
      (BitVec.isLt _) hmSt hmSw (k16 hL.kMsg) ha.1 ha.1.1.pMsg (ml ha.1.1) ha.2 (hmCov ha.1.1))
    (fun b hb => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fMsg) (len := .slot Impl.SlhDsa.X86_64.Shake.fLen)
      (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide) trivial
      (BitVec.isLt _) hmSt hmSw (k16 hL.kMsg) hb.1 hb.1.1.pMsg (ml hb.1.1) hb.2 (hmCov hb.1.1)) ?_
  -- padding, then the output
  refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂)
    (kpad_ct hL hst (pos := .ret) trivial (q := (ℓ + 2 + L.ctxLen.toNat + L.len.toNat) % 136) (Nat.mod_lt _ (by decide))
      (fun t ht => by rcases ht with ⟨⟨hc, _⟩, hx⟩ | ⟨⟨hc, _⟩, hx⟩ <;> exact ⟨⟨_, _, hc⟩, hx⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .ret, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ⟨⟨hc, msg, hR, hml⟩, hx⟩ => kpad_ok hL hc hst (pos := .ret) trivial hR (by rw [hml]; exact hx)
      fun t' hc' _ _ _ => hc')
    (fun b ⟨⟨hc, msg, hR, hml⟩, hx⟩ => kpad_ok hL hc hst (pos := .ret) trivial hR (by rw [hml]; exact hx)
      fun t' hc' _ _ _ => hc') ?_
  exact ksqz_ct hL hst hd hlen hDst hDsw hDk (fun t ht => by
      rcases ht with hc | hc <;> exact ⟨⟨_, _, hc⟩, hD _ _ _ hc, hDin _ _ _ hc⟩)
    hbd

end

section
variable {L : SL} (hL : L.Ok)

theorem hs0 {g : Reg → BitVec 64} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)
    (hz : stateAt t.mem (at' L.S Layout.oStream) = Spec.Sha3.zero) : HS L g m₀ 0 t :=
  ⟨hc, [], by show stateAt t.mem _ = Proof.Sha3.Rep 136 []; rw [Proof.Sha3.rep_nil, hz], rfl⟩

include hL in
theorem hashR_ct {p : Params} (hn : L.n = p.n) (hst : 8 ≤ L.st) {g₁ : Reg → BitVec 64} {m₁ : Mem}
    {g₂ : Reg → BitVec 64} {m₂ : Mem} :
    RelCT isa (fun a b => Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b)
      (Impl.SlhDsa.X86_64.Shake.hashM' p [.scr Layout.oSkPrf, .slot Impl.SlhDsa.X86_64.Shake.fRnd]
        (.slot Impl.SlhDsa.X86_64.Shake.fSig) p.n) fun _ _ => True := by
  have hn32 := hL.n32
  rw [hn] at hn32
  have hnB := hL.nB
  have eP : Layout.oSkPrf = 3200 := rfl
  simp only [Impl.SlhDsa.X86_64.Shake.hashM', List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil,
    List.length_cons, List.length_nil]
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  have hsig : Region.Sub ⟨L.sig, p.n⟩ L.SIG := Region.sub_prefix (by rw [← hn]; exact hL.sigN)
  have pSt : Region.Disjoint ⟨at' L.S Layout.oSkPrf, p.n⟩ (stR L) :=
    Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega)
  have pSw : Region.Disjoint ⟨at' L.S Layout.oSkPrf, p.n⟩ (swR L) :=
    Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega)
  have pK : Region.Disjoint (below L.SP 16) ⟨at' L.S Layout.oSkPrf, p.n⟩ :=
    (hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eP]; omega))
  have pCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [⟨at' L.S Layout.oSkPrf, p.n⟩] (t.rd ++ t.wr) := fun hc =>
    Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc.wr]; simp, Layout.oSkPrf, rfl, by show _ + p.n ≤ 65536; rw [eP]; omega⟩)
  have rSt : Region.Disjoint ⟨L.rnd, p.n⟩ (stR L) := by
    rw [← hn]; exact hL.sRnd.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have rSw : Region.Disjoint ⟨L.rnd, p.n⟩ (swR L) := by
    rw [← hn]; exact hL.sRnd.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have rK : Region.Disjoint (below L.SP 16) ⟨L.rnd, p.n⟩ := by rw [← hn]; exact k16 hL.kRnd
  have rCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [⟨L.rnd, p.n⟩] (t.rd ++ t.wr) := fun hc =>
    Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hc.rd, ← hn]; simp)
  refine Levels.relSeq (B₁ := HS L g₁ m₁ 0) (B₂ := HS L g₂ m₂ 0)
    (Levels.taintR [.rbx] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hx.rbx, hy.rbx]) (by taint_decide))
    (fun a ha => zero_ok hL ha fun t hc hz _ _ => hs0 hc hz) (fun b hb => zero_ok hL hb fun t hc hz _ _ => hs0 hc hz) ?_
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (0 + p.n)) (B₂ := HSr L g₂ m₂ (0 + p.n))
    (kabs_ct hL hst (src := .scr Layout.oSkPrf) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
      (A := at' L.S Layout.oSkPrf) (l := p.n) (q := 0) (by omega) (by decide) pSt pSw pK
      (fun t ht => by rcases ht with ⟨hc, _⟩ | ⟨hc, _⟩ <;> exact ⟨⟨_, _, hc⟩, rfl, rfl, by simp [argV], pCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1⟩) fun x hx => ⟨_, _, hx.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .scr 0, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .scr Layout.oSkPrf) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      pSt pSw pK ha rfl rfl (by simp [argV]) (pCov ha.1))
    (fun b hb => kabs_step hL hst (src := .scr Layout.oSkPrf) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      pSt pSw pK hb rfl rfl (by simp [argV]) (pCov hb.1)) ?_
  have hq1 : BitVec.ofNat 64 (p.n * 1) = BitVec.ofNat 64 ((0 + p.n) % 136) := by
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (0 + p.n + p.n)) (B₂ := HSr L g₂ m₂ (0 + p.n + p.n))
    (kabs_ct hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fRnd) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
      (A := L.rnd) (l := p.n) (q := (0 + p.n) % 136) (by omega) (Nat.mod_lt _ (by decide)) rSt rSw rK
      (fun t ht => by rcases ht with ⟨⟨hc, _⟩, _⟩ | ⟨⟨hc, _⟩, _⟩ <;> exact ⟨⟨_, _, hc⟩, hc.pRnd, rfl, hq1, rCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .slot 0, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fRnd) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      rSt rSw rK ha.1 ha.1.1.pRnd rfl hq1 (rCov ha.1.1))
    (fun b hb => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fRnd) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      rSt rSw rK hb.1 hb.1.1.pRnd rfl hq1 (rCov hb.1.1)) ?_
  exact RelCT.mono (tail_ct hL hst (ℓ := 0 + p.n + p.n) (q := p.n * 2) (by omega) (by omega)
      (dst := .slot Impl.SlhDsa.X86_64.Shake.fSig) (by dsimp only [ArgOk]; decide) (by omega) (D := L.sig)
      (fun _ _ _ hc => hc.pSig)
      (fun _ _ _ hc => Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SIG, by rw [hc.wr]; simp, 0, by simp, by show 0 + p.n ≤ L.sigL; rw [← hn]; have := hL.sigN; omega⟩)
      ((hL.sSig.sub_right hsig).sub_left (hL.scr_sub (by rw [oStream_eq]; omega)))
      ((hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
      ((k16 hL.kSig).sub_right hsig)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx⟩) fun x hx => ⟨_, _, hx⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .slot 0, .imm 0, .scr 0]) rfl (by taint_decide))) (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

include hL in
theorem hashD_ct {p : Params} (hn : L.n = p.n) (hm : p.m ≤ 64) (hst : 8 ≤ L.st) {g₁ : Reg → BitVec 64} {m₁ : Mem}
    {g₂ : Reg → BitVec 64} {m₂ : Mem} :
    RelCT isa (fun a b => Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b)
      (Impl.SlhDsa.X86_64.Shake.hashM' p [.slot Impl.SlhDsa.X86_64.Shake.fSig, .scr Layout.oPkSeed,
        .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m) fun _ _ => True := by
  have hn32 := hL.n32
  rw [hn] at hn32
  have hnB := hL.nB
  have eP : Layout.oPkSeed = 3232 := rfl
  have eR : Layout.oPkRoot = 3264 := rfl
  have eD : Layout.oDigest = 30304 := rfl
  simp only [Impl.SlhDsa.X86_64.Shake.hashM', List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil,
    List.length_cons, List.length_nil]
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  have hsig : Region.Sub ⟨L.sig, p.n⟩ L.SIG := Region.sub_prefix (by rw [← hn]; exact hL.sigN)
  have gSt : Region.Disjoint ⟨L.sig, p.n⟩ (stR L) :=
    (hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have gSw : Region.Disjoint ⟨L.sig, p.n⟩ (swR L) :=
    (hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))
  have gCov : ∀ {g m₀ t}, Ctx L g m₀ t → Covers [⟨L.sig, p.n⟩] (t.rd ++ t.wr) := fun hc =>
    Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SIG, by rw [hc.wr]; simp, 0, by simp, by show 0 + p.n ≤ L.sigL; rw [← hn]; have := hL.sigN; omega⟩)
  have sSt : ∀ {o : Nat}, o = 3232 ∨ o = 3264 → Region.Disjoint ⟨at' L.S o, p.n⟩ (stR L) := fun h =>
    Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by omega) (by rw [oStream_eq]; omega)
  have sSw : ∀ {o : Nat}, o = 3232 ∨ o = 3264 → Region.Disjoint ⟨at' L.S o, p.n⟩ (swR L) := fun h =>
    Levels.disj_scr L.S (by rw [oStream_eq]; omega) (by omega) (by rw [oStream_eq]; omega)
  have sK : ∀ {o : Nat}, o = 3232 ∨ o = 3264 → Region.Disjoint (below L.SP 16) ⟨at' L.S o, p.n⟩ := fun h =>
    (hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by omega))
  have sCov : ∀ {o : Nat}, o = 3232 ∨ o = 3264 → ∀ {g m₀ t}, Ctx L g m₀ t →
      Covers [⟨at' L.S o, p.n⟩] (t.rd ++ t.wr) := fun {o} _ {g m₀ t} hc =>
    Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc.wr]; simp, _, rfl, by show _ + p.n ≤ 65536; omega⟩)
  have oP : Layout.oPkSeed = 3232 ∨ Layout.oPkSeed = 3264 := .inl eP
  have oR : Layout.oPkRoot = 3232 ∨ Layout.oPkRoot = 3264 := .inr eR
  refine Levels.relSeq (B₁ := HS L g₁ m₁ 0) (B₂ := HS L g₂ m₂ 0)
    (Levels.taintR [.rbx] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hx.rbx, hy.rbx]) (by taint_decide))
    (fun a ha => zero_ok hL ha fun t hc hz _ _ => hs0 hc hz) (fun b hb => zero_ok hL hb fun t hc hz _ _ => hs0 hc hz) ?_
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (0 + p.n)) (B₂ := HSr L g₂ m₂ (0 + p.n))
    (kabs_ct hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fSig) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
      (A := L.sig) (l := p.n) (q := 0) (by omega) (by decide) gSt gSw ((k16 hL.kSig).sub_right hsig)
      (fun t ht => by rcases ht with ⟨hc, _⟩ | ⟨hc, _⟩ <;> exact ⟨⟨_, _, hc⟩, hc.pSig, rfl, by simp [argV], gCov hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1⟩) fun x hx => ⟨_, _, hx.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .slot 0, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fSig) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      gSt gSw ((k16 hL.kSig).sub_right hsig) ha ha.1.pSig rfl (by simp [argV]) (gCov ha.1))
    (fun b hb => kabs_step hL hst (src := .slot Impl.SlhDsa.X86_64.Shake.fSig) (len := .imm p.n) (pos := .imm (p.n * 0))
      (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      gSt gSw ((k16 hL.kSig).sub_right hsig) hb hb.1.pSig rfl (by simp [argV]) (gCov hb.1)) ?_
  have hq1 : BitVec.ofNat 64 (p.n * 1) = BitVec.ofNat 64 ((0 + p.n) % 136) := by
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (0 + p.n + p.n)) (B₂ := HSr L g₂ m₂ (0 + p.n + p.n))
    (kabs_ct hL hst (src := .scr Layout.oPkSeed) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
      (A := at' L.S Layout.oPkSeed) (l := p.n) (q := (0 + p.n) % 136) (by omega) (Nat.mod_lt _ (by decide))
      (sSt oP) (sSw oP) (sK oP)
      (fun t ht => by rcases ht with ⟨⟨hc, _⟩, _⟩ | ⟨⟨hc, _⟩, _⟩ <;> exact ⟨⟨_, _, hc⟩, rfl, rfl, hq1, sCov oP hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .scr 0, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .scr Layout.oPkSeed) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      (sSt oP) (sSw oP) (sK oP) ha.1 rfl rfl hq1 (sCov oP ha.1.1))
    (fun b hb => kabs_step hL hst (src := .scr Layout.oPkSeed) (len := .imm p.n) (pos := .imm (p.n * 1))
      (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      (sSt oP) (sSw oP) (sK oP) hb.1 rfl rfl hq1 (sCov oP hb.1.1)) ?_
  have hq2 : BitVec.ofNat 64 (p.n * 2) = BitVec.ofNat 64 ((0 + p.n + p.n) % 136) := by
    rw [Nat.mod_eq_of_lt (by omega), show 0 + p.n + p.n = p.n * 2 by omega]
  refine Levels.relSeq (B₁ := HSr L g₁ m₁ (0 + p.n + p.n + p.n)) (B₂ := HSr L g₂ m₂ (0 + p.n + p.n + p.n))
    (kabs_ct hL hst (src := .scr Layout.oPkRoot) (len := .imm p.n) (pos := .imm (p.n * 2))
      (by show _ < 2 ^ 31; rw [eR]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
      (A := at' L.S Layout.oPkRoot) (l := p.n) (q := (0 + p.n + p.n) % 136) (by omega) (Nat.mod_lt _ (by decide))
      (sSt oR) (sSw oR) (sK oR)
      (fun t ht => by rcases ht with ⟨⟨hc, _⟩, _⟩ | ⟨⟨hc, _⟩, _⟩ <;> exact ⟨⟨_, _, hc⟩, rfl, rfl, hq2, sCov oR hc⟩)
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx.1.1⟩) fun x hx => ⟨_, _, hx.1.1⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .scr 0, .imm 0, .scr 0]) rfl (by taint_decide)))
    (fun a ha => kabs_step hL hst (src := .scr Layout.oPkRoot) (len := .imm p.n) (pos := .imm (p.n * 2))
      (by show _ < 2 ^ 31; rw [eR]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      (sSt oR) (sSw oR) (sK oR) ha.1 rfl rfl hq2 (sCov oR ha.1.1))
    (fun b hb => kabs_step hL hst (src := .scr Layout.oPkRoot) (len := .imm p.n) (pos := .imm (p.n * 2))
      (by show _ < 2 ^ 31; rw [eR]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega) (by omega)
      (sSt oR) (sSw oR) (sK oR) hb.1 rfl rfl hq2 (sCov oR hb.1.1)) ?_
  exact RelCT.mono (tail_ct hL hst (ℓ := 0 + p.n + p.n + p.n) (q := p.n * 3) (by omega) (by omega)
      (dst := .scr Layout.oDigest) (by show _ < 2 ^ 31; rw [eD]; decide) (by omega) (D := at' L.S Layout.oDigest)
      (fun _ _ _ _ => rfl)
      (fun _ _ _ hc => Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by rw [hc.wr]; simp, Layout.oDigest, rfl, by show _ + p.m ≤ 65536; rw [eD]; omega⟩)
      (Levels.disj_scr L.S (by rw [eD, oStream_eq]; omega) (by rw [oStream_eq]; omega) (by rw [eD]; omega))
      (Levels.disj_scr L.S (by rw [eD, oStream_eq]; omega) (by rw [eD]; omega) (by rw [oStream_eq]; omega))
      ((hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eD]; omega)))
      (taintS [.rsp, .rbx] (inCtx_regs (fun x hx => ⟨_, _, hx⟩) fun x hx => ⟨_, _, hx⟩)
        (is₀ := zArgs [Arg.scr 0, .imm 0, .imm 0, .scr 0, .imm 0, .scr 0]) rfl (by taint_decide))) (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end

/-! ## The callees' preconditions -/

section
variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem fors_pre {p : Params} {c : Prog isa} (F : ForsFn p c) (hFs : F.stack ≤ L.st) (hL : L.Ok)
    (hst : 8 ≤ L.st) (hn : L.n = p.n) (hsl : p.n + p.forsSigLen ≤ L.sigL) {t : State} (hc : Ctx L g m₀ t)
    {a16 : List Byte} (ha : Adr L t.mem a16) {kp : Nat} (hkp : kp < 2 ^ 32) (h1 : t.gpr .rdi = L.S)
    (h2 : t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n) (h3 : t.gpr .rdx = BitVec.ofNat 64 kp) :
    (forsContract p F.stack).pre (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]) ∧
      Covers ([] ++ [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩] t.wr := by
  have hn32 := hL.n32
  have e1 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]).gpr .rsi = L.sig + BitVec.ofNat 64 p.n := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]).gpr .rdx = BitVec.ofNat 64 kp := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hkp' : (BitVec.ofNat 64 kp).toNat = kp := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 p.n).toNat + p.forsSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have h' : (L.sig + BitVec.ofNat 64 p.n).toNat ≤ L.sig.toNat + p.n := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
    omega
  have env := (ce_ctx hL hst hc [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]).env hn (adr_ce hL hst hc [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩] ha)
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by have := hL.nSig; omega)⟩
  refine ⟨?_, hcov, hcovw⟩
  simp only [forsContract, e1, e3, hkp']
  exact ⟨by rw [e2]; exact regions_ok hL hFs hst hc hsub hfit, ⟨_, _, env⟩, hkp⟩

theorem xmss_pre {p : Params} (hhp : p.hp ≤ 9) (hL : L.Ok) (hst : 8 ≤ L.st) (hn : L.n = p.n) {o : Nat}
    (hsl : o + p.xmssSigLen ≤ L.sigL) (ho : o < 2 ^ 31) {t : State} (hc : Ctx L g m₀ t) {a16 : List Byte}
    (ha : Adr L t.mem a16) {idx : Nat} (hidx : idx < 2 ^ p.hp) (h1 : t.gpr .rdi = L.S)
    (h2 : t.gpr .rsi = BitVec.ofNat 64 idx) (h3 : t.gpr .rdx = L.sig + BitVec.ofNat 64 o) :
    (xmssContract p L.st).pre (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]) ∧
      Covers ([] ++ [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩] t.wr := by
  have hn32 := hL.n32
  have hidx' : idx < 2 ^ 64 := Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))
  have e1 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]).gpr .rdi = L.S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h1]
  have e2 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]).gpr .rsi = BitVec.ofNat 64 idx := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h2]
  have e3 : (t.callEntry.withRegions [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]).gpr .rdx = L.sig + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h3]
  have hidx'' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx']
  have hsub : Region.Sub ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩ L.SIG := Offset.sub_base _ hsl
  have hfit : (L.sig + BitVec.ofNat 64 o).toNat + p.xmssSigLen ≤ 2 ^ 64 := by
    have := hL.nSig
    have h' : (L.sig + BitVec.ofNat 64 o).toNat ≤ L.sig.toNat + o := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
    omega
  have env := (ce_ctx hL hst hc [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩]).env hn (adr_ce hL hst hc [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩] ha)
  obtain ⟨hcov, hcovw⟩ := covers_call (R := ⟨L.sig + BitVec.ofNat 64 o, p.xmssSigLen⟩) hc
    ⟨L.SIG, by simp, Offset.contains_base _ hsl (by omega)⟩
  refine ⟨?_, hcov, hcovw⟩
  simp only [xmssContract, e1, e2, hidx'']
  exact ⟨by rw [e3]; exact regions_ok hL (Nat.le_refl _) hst hc hsub hfit, ⟨_, _, env⟩,
    Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))⟩

end

/-! ## The layers -/

/-- Before layer `j`, as constant time needs it. -/
structure LC (p : Params) (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (j : Nat) (t : State) : Prop where
  ctx : Ctx L g m₀ t
  jd : j ≤ p.d
  v1 : (t.mem.readW (L.var 1) 64).toNat < 2 ^ p.hp
  v2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j
  v3 : t.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)

/-- After a layer's first block. -/
def LB (p : Params) (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (j : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ ∃ a16, Adr L t.mem a16 ∧ ∃ idx, idx < 2 ^ p.hp ∧ t.gpr .rdi = L.S ∧
    t.gpr .rsi = BitVec.ofNat 64 idx ∧ t.gpr .rdx = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)

section
variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem lb_ok {p : Params} (hP : LP p L) (hL : L.Ok) {j : Nat} (hj : j < p.d) {t : State} (hi : LC p L g m₀ j t) :
    WP isa (.block (lblock p)) t fun t₁ => LB p L g m₀ j t₁ ∧
      ∀ i < 4, t₁.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := by
  have hp := hP.hp
  refine lblock_ok hL hP.n hi.ctx (j := j) (T := (t.mem.readW (L.var 0) 64).toNat) (by have := hp.d22; omega)
    (BitVec.isLt _) (Levels.ofNat_toNat64 _).symm hi.v2 fun t₁ hc₁ ha₁ h1 h2 h3 hf _ =>
      ⟨⟨hc₁, _, ha₁, _, hi.v1, h1, by rw [h2, Levels.ofNat_toNat64], by rw [h3, hi.v3]⟩, fun i hi' => ?_⟩
  rw [Thash4Avx.readW_frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Levels.disj_scr L.S (by simp only [Layout.oA, show Impl.SlhDsa.X86_64.Shake.oKgSave = 34080 from rfl]; omega)
      (by rw [show Impl.SlhDsa.X86_64.Shake.oKgSave = 34080 from rfl]; omega) (by simp only [Layout.oA]; omega)]

theorem layerC_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hP : LP p L) (hst : T.stack + 24 ≤ L.st) (hL : L.Ok) {j : Nat} (hj : j < p.d) {t : State}
    (hi : LC p L g m₀ j t) :
    WP isa (Impl.SlhDsa.X86_64.Shake.layerBody p f) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 ≠ p.d)) ∧ LC p L g m₀ (j + 1) t' := by
  have hp := hP.hp
  have hsl : p.n + p.forsSigLen + (j + 1) * p.xmssSigLen ≤ L.sigL := by
    rw [hP.sigL, hp.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega); omega
  have hlt : p.n + p.forsSigLen + (j + 1) * p.xmssSigLen < 2 ^ 31 := by
    have := hp.sigLt; rw [hP.sigL, hp.sigLen] at hsl; rw [hp.sigLen] at this; omega
  have hjm : (j + 1) * p.xmssSigLen = j * p.xmssSigLen + p.xmssSigLen := Nat.succ_mul _ _
  unfold Impl.SlhDsa.X86_64.Shake.layerBody
  refine WP.seq (WP.mono (lb_ok hP hL hj hi) fun t₁ ⟨⟨hbc, _, hba, _, hbi, hb1, hb2, hb3⟩, hv₁⟩ => ?_)
  refine WP.seq (xmssCall_ok T ht hP.hz hP.hh hst (by have := hL.st62; omega) hL hP.n
    (o := p.n + p.forsSigLen + j * p.xmssSigLen) (by omega) (by omega) hbc hba hbi hb1 hb2 hb3
    fun t₂ hc₂ hv₂ _ _ _ _ => ?_)
  have hv : ∀ i < 4, t₂.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64 := fun i hi' => by
    rw [hv₂ i hi', hv₁ i hi']
  refine next_ok hL ⟨hp.hp1, hp.hp9⟩ (by have := hp.d22; omega) hp.xsl hc₂ (j := j)
    (T := (t.mem.readW (L.var 0) 64).toNat) (o := p.n + p.forsSigLen + j * p.xmssSigLen) (by have := hp.d22; omega)
    (BitVec.isLt _) (by rw [hv 0 (by decide), Levels.ofNat_toNat64]) (by rw [hv 2 (by decide)]; exact hi.v2)
    (by rw [hv 3 (by decide)]; exact hi.v3) fun t₃ hc₃ _ h1 h2 h3 he _ _ => ⟨he, hc₃, by omega, ?_, h2, ?_⟩
  · rw [h1, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  · rw [h3, hjm, Nat.add_assoc]

end

/-! ## The frame's body -/

/-- Before FORS. -/
def FB (p : Params) (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) : Prop :=
  Ctx L g m₀ t ∧ (t.mem.readW (L.var 1) 64).toNat < 2 ^ p.hp ∧ ∃ a16, Adr L t.mem a16 ∧ ∃ kp, kp < 2 ^ 32 ∧
    t.gpr .rdi = L.S ∧ t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n ∧ t.gpr .rdx = BitVec.ofNat 64 kp

theorem body_ct {p : Params} (hS : VerifyTop.S6 p) {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (F : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f)) {L : SL} (hB : BP p L T F.stack)
    {g₁ : Reg → BitVec 64} {m₁ : Mem} {g₂ : Reg → BitVec 64} {m₂ : Mem} :
    RelCT isa (fun a b => Pushed L g₁ m₁ a ∧ Pushed L g₂ m₂ b) (Impl.SlhDsa.X86_64.Shake.signBody p f)
      fun _ _ => True := by
  have hP := hB.lp
  have hL := hB.ok
  have hp := hP.hp
  have hn := hP.n
  have hn32 := hL.n32
  have hst8 : 8 ≤ L.st := by have := hB.st; omega
  have rg : ∀ {A₁ A₂ : State → Prop} {rs : List Reg}, (∀ x, A₁ x → InCtx L x) → (∀ x, A₂ x → InCtx L x) →
      (∀ r ∈ rs, r = .rsp ∨ r = .rbx) → ∀ x y, (A₁ x ∧ A₂ y) → ∀ r ∈ rs, x.gpr r = y.gpr r :=
    fun h₁ h₂ hrs x y hxy r hr => by
      rcases hrs r hr with rfl | rfl
      · exact inCtx_regs h₁ h₂ x y hxy .rsp (by simp)
      · exact inCtx_regs h₁ h₂ x y hxy .rbx (by simp)
  unfold Impl.SlhDsa.X86_64.Shake.signBody
  rw [proCode_eq p]
  -- the prologue
  refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂) ?_
    (fun a ha => by rw [← proCode_eq p]; exact pro_ok hL hn ha) (fun b hb => by rw [← proCode_eq p]; exact pro_ok hL hn hb) ?_
  · have pa : ∀ {g m₀ u}, Pushed L g m₀ u → WP isa (.block proA) u fun v => v.gpr .rdi = L.S ∧ v.gpr .rsp = L.SP ∧
        v.rd = L.rd ∧ v.wr = L.FR :: [L.SIG, L.SCR] ∧ v.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.sk :=
      fun hu => WP.mono (proA_ok hL hu) fun v ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3.trans hu.rd, h4.trans hu.wr, h5⟩
    have pb : ∀ {v : State}, (v.gpr .rdi = L.S ∧ v.gpr .rsp = L.SP ∧ v.rd = L.rd ∧ v.wr = L.FR :: [L.SIG, L.SCR] ∧
        v.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.sk) →
        WP isa (.block proB) v fun w => w.gpr .rbx = L.S ∧ w.gpr .rsi = L.sk := fun ⟨h1, h2, h3, h4, h5⟩ =>
      proB_ok hL (by rw [h4]; simp) h1 h2 h5 ⟨L.FR, by rw [h3, h4]; simp, Offset.contains_base _ (by omega) (by omega)⟩
    refine RelCT.block_append (Levels.relSeq (Levels.taintR [.rsp] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.rsp, hy.rsp]) (by taint_decide))
      (fun a ha => pa ha) (fun b hb => pa hb) (RelCT.block_append (Levels.relSeq (Levels.taintR [.rsp, .rdi]
        (fun x y ⟨hx, hy⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [hx.2.1, hy.2.1]
          · rw [hx.1, hy.1]) (by taint_decide)) (fun a ha => pb ha) (fun b hb => pb hb) ?_)))
    have hr : ∀ x y : State, ((x.gpr .rbx = L.S ∧ x.gpr .rsi = L.sk) ∧ (y.gpr .rbx = L.S ∧ y.gpr .rsi = L.sk)) →
        ∀ r ∈ [Reg.rbx, .rsi], x.gpr r = y.gpr r := fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx.1, hy.1]
      · rw [hx.2, hy.2]
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Levels.taintR [.rbx, .rsi] hr (by taint_decide)
  -- `R` and the digest
  refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂) (hashR_ct hL hn hst8)
    (fun a ha => hashR_ok hL ha hn hst8 fun t hc _ _ _ => hc) (fun b hb => hashR_ok hL hb hn hst8 fun t hc _ _ _ => hc) ?_
  refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂) (hashD_ct hL hn hp.m64 hst8)
    (fun a ha => hashD_ok hL ha hn hp.m64 hst8 fun t hc _ _ _ => hc)
    (fun b hb => hashD_ok hL hb hn hp.m64 hst8 fun t hc _ _ _ => hc) ?_
  -- FORS's indices and lanes
  have fb : ∀ {g m₀ t}, Ctx L g m₀ t → WP isa (.block (fblock p)) t (FB p L g m₀) := fun {g m₀ t} hc => by
    have hIL : (L.sd p t.mem).2.2 < 2 ^ p.hp := by
      simp only [SL.sd, splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hIL' : (L.sd p t.mem).2.2 < 2 ^ 32 :=
      Nat.lt_of_lt_of_le hIL (Nat.pow_le_pow_right (by decide) (by have := hp.hp9; omega))
    exact fblock_ok hp hL hn hc fun t' hc' _ h1 ha h1' h2' h3' _ _ _ => ⟨hc', by
      rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hIL, _, ha, _, hIL', h1', h2', h3'⟩
  refine Levels.relSeq (B₁ := FB p L g₁ m₁) (B₂ := FB p L g₂ m₂) ?_ (fun a ha => fb ha) (fun b hb => fb hb) ?_
  · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Levels.taintR [.rsp, .rbx] (rg (fun x hx => ⟨_, _, hx⟩) (fun x hx => ⟨_, _, hx⟩) (by simp)) (by taint_decide)
  -- FORS
  have hsl : p.n + p.forsSigLen ≤ L.sigL := by rw [hP.sigL, hp.sigLen]; omega
  refine Levels.relSeq (B₁ := fun t => Ctx L g₁ m₁ t ∧ (t.mem.readW (L.var 1) 64).toNat < 2 ^ p.hp)
    (B₂ := fun t => Ctx L g₂ m₂ t ∧ (t.mem.readW (L.var 1) 64).toNat < 2 ^ p.hp)
    (RelCT.call F.correct F.ct [] [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
      fun x y ⟨⟨hcx, _, _, hax, _, hkx, h1x, h2x, h3x⟩, ⟨hcy, _, _, hay, _, hky, h1y, h2y, h3y⟩⟩ => by
        obtain ⟨px, cx, wx⟩ := fors_pre F hB.fst hL hst8 hn hsl hcx hax hkx h1x h2x h3x
        obtain ⟨py, cy, wy⟩ := fors_pre F hB.fst hL hst8 hn hsl hcy hay hky h1y h2y h3y
        refine ⟨px, py, ?_, cx, wx, cy, wy, by rw [hcx.rsp, hcy.rsp]⟩
        simp only [forsContract, State.withRegions_gpr, State.callEntry_rsp,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          h1x, h1y, h2x, h2y, hcx.rsp, hcy.rsp, and_self])
    (fun a ⟨hc, hv, _, ha, _, hk, h1, h2, h3⟩ => forsCall_ok F hB.fst hL hst8 hn hsl hp.fsl
      (by have := hp.m; have := hp.m64; omega) hc ha hk h1 h2 h3 _ fun t' hc' hv' _ _ _ _ =>
        ⟨hc', by rw [hv' 1 (by decide)]; exact hv⟩)
    (fun b ⟨hc, hv, _, ha, _, hk, h1, h2, h3⟩ => forsCall_ok F hB.fst hL hst8 hn hsl hp.fsl
      (by have := hp.m; have := hp.m64; omega) hc ha hk h1 h2 h3 _ fun t' hc' hv' _ _ _ _ =>
        ⟨hc', by rw [hv' 1 (by decide)]; exact hv⟩) ?_
  -- the first layer
  have ib : ∀ {g m₀ t}, (Ctx L g m₀ t ∧ (t.mem.readW (L.var 1) 64).toNat < 2 ^ p.hp) →
      WP isa (.block (iblock p)) t (LC p L g m₀ 0) := fun ⟨hc, hv⟩ =>
    init_ok hL hp.fsl hc fun t' hc' h2 h3 h01 _ _ => ⟨hc', Nat.zero_le _, by rw [h01 1 (by decide)]; exact hv, h2,
      by rw [h3]; simp⟩
  refine Levels.relSeq (B₁ := LC p L g₁ m₁ 0) (B₂ := LC p L g₂ m₂ 0)
    (taintS [.rsp, .rbx] (rg (fun x hx => ⟨_, _, hx.1⟩) (fun x hx => ⟨_, _, hx.1⟩) (by simp))
      (is₀ := [.mov32 .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Shake.var 2) .rax, .mov .rax (.mem (Impl.SlhDsa.X86_64.Shake.stk
        Impl.SlhDsa.X86_64.Shake.fSig)), .alu .add .rax (.imm 0), .store (Impl.SlhDsa.X86_64.Shake.var 3) .rax]) rfl (by taint_decide))
    (fun a ha => ib ha) (fun b hb => ib hb) ?_
  -- the layers
  have hd1 := hp.d1
  have lw : ∀ {g m₀}, ∀ m s, (1 ≤ m ∧ m ≤ p.d ∧ LC p L g m₀ (p.d - m) s) →
      WP isa (Impl.SlhDsa.X86_64.Shake.layerBody p f) s fun s' => isa.eval .ne s' = some (decide (m ≠ 1)) ∧
        (decide (m ≠ 1) = false → Ctx L g m₀ s') ∧
        (decide (m ≠ 1) = true → m - 1 < m ∧ (1 ≤ m - 1 ∧ m - 1 ≤ p.d ∧ LC p L g m₀ (p.d - (m - 1)) s')) :=
    fun m s ⟨h1, h2, hs⟩ => WP.mono (layerC_ok T ht hP hB.st hL (j := p.d - m) (by omega) hs) fun s' ⟨he, hs'⟩ =>
      ⟨by rw [he]; congr 1; simp only [decide_eq_decide]; omega, fun _ => hs'.ctx, fun hc => by
        simp only [decide_eq_true_eq] at hc
        exact ⟨by omega, by omega, by omega, by rw [show p.d - (m - 1) = p.d - m + 1 by omega]; exact hs'⟩⟩
  have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
      Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
    rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
  have hhp2 : 2 ≤ p.hp := by rcases hP.hh with h | h | h | h <;> omega
  have hhp9 : p.hp ≤ 9 := hp.hp9
  have hct : ∀ m, RelCT isa (fun a b => (1 ≤ m ∧ m ≤ p.d ∧ LC p L g₁ m₁ (p.d - m) a) ∧
      (1 ≤ m ∧ m ≤ p.d ∧ LC p L g₂ m₂ (p.d - m) b)) (Impl.SlhDsa.X86_64.Shake.layerBody p f) fun _ _ => True := by
    intro m
    by_cases hm : 1 ≤ m ∧ m ≤ p.d
    swap
    · exact RelCT.of_false fun a b h => hm ⟨h.1.1, h.1.2.1⟩
    unfold Impl.SlhDsa.X86_64.Shake.layerBody
    refine Levels.relSeq (B₁ := LB p L g₁ m₁ (p.d - m)) (B₂ := LB p L g₂ m₂ (p.d - m)) ?_
      (fun a ⟨h1, _, ha⟩ => WP.mono (lb_ok hP hL (by omega) ha) fun _ h => h.1)
      (fun b ⟨h1, _, hb⟩ => WP.mono (lb_ok hP hL (by omega) hb) fun _ h => h.1) ?_
    · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Levels.taintR [.rbx] (rg (fun x hx => ⟨_, _, hx.2.2.ctx⟩) (fun x hx => ⟨_, _, hx.2.2.ctx⟩) (by simp))
          (by taint_decide)
    have hsl' : p.n + p.forsSigLen + (p.d - m) * p.xmssSigLen + p.xmssSigLen ≤ L.sigL := by
      have := Nat.mul_le_mul_right p.xmssSigLen (show p.d - m + 1 ≤ p.d by omega)
      have e : (p.d - m + 1) * p.xmssSigLen = (p.d - m) * p.xmssSigLen + p.xmssSigLen := Nat.succ_mul _ _
      rw [hP.sigL, hp.sigLen]; omega
    have ho : p.n + p.forsSigLen + (p.d - m) * p.xmssSigLen + p.xmssSigLen < 2 ^ 31 := by
      have := hp.sigLt; rw [hP.sigL, hp.sigLen] at hsl'; rw [hp.sigLen] at this; omega
    refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂) ?_
      (fun a ⟨hc, _, ha, _, hi, h1, h2, h3⟩ => xmssCall_ok T ht hP.hz hP.hh hB.st (by have := hL.st62; omega) hL hn
        (by omega) (by omega) hc ha hi h1 h2 h3 fun t' hc' _ _ _ _ _ => hc')
      (fun b ⟨hc, _, ha, _, hi, h1, h2, h3⟩ => xmssCall_ok T ht hP.hz hP.hh hB.st (by have := hL.st62; omega) hL hn
        (by omega) (by omega) hc ha hi h1 h2 h3 fun t' hc' _ _ _ _ _ => hc') ?_
    · rw [hcode]
      refine RelCT.call (XmssTree.xmss_correct hP.hz T f.t4name f.wotsName f.levelsName hB.st
          (by have := hL.st62; omega) hhp2 hhp9)
        (XmssTree.xmss_ct hP.hz T f.t4name f.wotsName f.levelsName hB.st (by have := hL.st62; omega) hP.hh) []
        [⟨L.S, scratchLen⟩, ⟨L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen + (p.d - m) * p.xmssSigLen), p.xmssSigLen⟩]
        fun x y ⟨⟨hcx, _, hax, _, hix, h1x, h2x, h3x⟩, ⟨hcy, _, hay, _, hiy, h1y, h2y, h3y⟩⟩ => ?_
      obtain ⟨px, cx, wx⟩ := xmss_pre hhp9 hL hst8 hn (by omega) (by omega) hcx hax hix h1x h2x h3x
      obtain ⟨py, cy, wy⟩ := xmss_pre hhp9 hL hst8 hn (by omega) (by omega) hcy hay hiy h1y h2y h3y
      refine ⟨px, py, ?_, cx, wx, cy, wy, by rw [hcx.rsp, hcy.rsp]⟩
      simp only [xmssContract, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        h1x, h1y, h3x, h3y, hcx.rsp, hcy.rsp, and_self]
    · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Levels.taintR [.rbx] (rg (fun x hx => ⟨_, _, hx⟩) (fun x hx => ⟨_, _, hx⟩) (by simp)) (by taint_decide)
  refine Levels.relSeq (B₁ := Ctx L g₁ m₁) (B₂ := Ctx L g₂ m₂)
    (RelCT.mono (Levels.relLoop (I₁ := fun m s => 1 ≤ m ∧ m ≤ p.d ∧ LC p L g₁ m₁ (p.d - m) s)
      (I₂ := fun m s => 1 ≤ m ∧ m ≤ p.d ∧ LC p L g₂ m₂ (p.d - m) s) (fun m => decide (m ≠ 1)) (fun m => m - 1)
      hct lw lw p.d) (fun a b ⟨ha, hb⟩ => ⟨⟨hd1, Nat.le_refl _, by rw [Nat.sub_self]; exact ha⟩,
        ⟨hd1, Nat.le_refl _, by rw [Nat.sub_self]; exact hb⟩⟩) fun _ _ _ => trivial)
    (fun a ha => Levels.wpLoop _ _ lw p.d ⟨hd1, Nat.le_refl _, by rw [Nat.sub_self]; exact ha⟩)
    (fun b hb => Levels.wpLoop _ _ lw p.d ⟨hd1, Nat.le_refl _, by rw [Nat.sub_self]; exact hb⟩) ?_
  exact Levels.taintR [.rbx] (rg (fun x hx => ⟨_, _, hx⟩) (fun x hx => ⟨_, _, hx⟩) (by simp)) (by taint_decide)

/-! ## The function -/

theorem of_eq {p : Params} {stack : Nat} {s₁ s₂ : State} (h : (sgK p stack).pub s₁ s₂) :
    SL.of p stack s₁ = SL.of p stack s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [SL.of, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- `sign` is constant time: its timing depends only on the pointers and the lengths. -/
theorem sign_ct {p : Params} (hS : VerifyTop.S6 p) (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp) (T : Thash4Impl p.n)
    {f : Impl.SlhDsa.X86_64.Shake.Fns} (ht : f.t4 = T.code) (F : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f))
    {stack : Nat} (hst : T.stack + 104 ≤ stack) (hFs : F.stack + 80 ≤ stack) (h62 : stack < 2 ^ 62) :
    ConstantTime isa (sgK p stack).pre (sgK p stack).pub (Impl.SlhDsa.X86_64.Shake.sign p f) := by
  have hp := hS.par
  have h80 : 80 ≤ stack := by omega
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hK₁ : SG p stack s₁ := h₁
  have hK₂ : SG p stack s₂ := h₂
  have hpub' := hpub
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpub'
  let C (σ : State) (s : State) : Prop := s.gpr = σ.gpr ∧ s.mem = σ.mem ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.cf = some (decide ((σ.gpr .r8).toNat < 256))
  let A (σ : State) (s₄ : State) : Prop := (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s₄.gpr r = σ.gpr r) ∧
    s₄.gpr .r10 = stackArg σ 0 ∧ s₄.gpr .r11 = stackArg σ 1 ∧ s₄.gpr .rax = 0 ∧ s₄.mem = σ.mem ∧ s₄.rd = σ.rd ∧
    s₄.wr = σ.wr
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.X86_64.Shake.sign p f) fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Shake.sign
    refine Levels.relSeq (B₁ := C s₁) (B₂ := C s₂) (Levels.taintR [.r8] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy, p5]) (by taint_decide))
      (fun a ha => by rw [ha]; exact cmp_ok s₁) (fun b hb => by rw [hb]; exact cmp_ok s₂) ?_
    refine RelCT.ite (fun x y ⟨hx, hy⟩ => by rw [(show isa.eval .b x = x.cf from rfl), (show isa.eval .b y = y.cf from rfl), hx.2.2.2.2, hy.2.2.2.2, p5]) ?_ ?_
    · refine RelCT.mono (P := fun a b => (C s₁ a ∧ (s₁.gpr .r8).toNat < 256) ∧ (C s₂ b ∧ (s₂.gpr .r8).toNat < 256))
        ?_ (fun x y ⟨⟨hx, hy⟩, he⟩ => by
          rw [(show isa.eval .b x = x.cf from rfl), hx.2.2.2.2] at he
          simp only [Option.some.injEq, decide_eq_true_eq] at he
          exact ⟨⟨hx, he⟩, hy, by rw [← p5]; exact he⟩) fun _ _ h => h
      by_cases hc : (s₁.gpr .r8).toNat < 256
      swap
      · exact RelCT.of_false fun a b h => hc h.1.2
      refine Levels.relSeq (B₁ := fun s => A s₁ s ∧ (s₁.gpr .r8).toNat < 256)
        (B₂ := fun s => A s₂ s ∧ (s₂.gpr .r8).toNat < 256) (Levels.taintR [.rsp] (fun x y ⟨hx, hy⟩ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hx.1.1, hy.1.1, p7]) (by taint_decide))
        (fun a ⟨ha, hc⟩ => WP.mono (preload_ok hK₁ ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1⟩) fun s h => ⟨h, hc⟩)
        (fun b ⟨hb, hc⟩ => WP.mono (preload_ok hK₂ ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩) fun s h => ⟨h, hc⟩) ?_
      refine RelCT.frame (R := fun _ _ => True) (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => by
        rw [hx.1 _ (by decide) (by decide) (by decide), hy.1 _ (by decide) (by decide) (by decide), p7]) ?_
      refine RelCT.mono (body_ct hS T ht F (L := SL.of p stack s₁) (g₁ := s₁.gpr) (m₁ := s₁.mem) (g₂ := s₂.gpr)
        (m₂ := s₂.mem) ?_) (fun a b ⟨x, y, ⟨⟨hx, _⟩, ⟨hy, _⟩⟩, ea, eb⟩ => ?_) fun _ _ _ => trivial
      · exact ⟨⟨hp, hz, hh, rfl, rfl⟩, by simp only [SL.of]; omega, by simp only [SL.of]; omega,
          of_ok hp hK₁ h80 h62 hc⟩
      · subst ea eb
        obtain ⟨g1, h10, h11, hax, hm, hr, hw⟩ := hx
        obtain ⟨g1', h10', h11', hax', hm', hr', hw'⟩ := hy
        exact ⟨pushed_ok hK₁ h80 g1 h10 h11 hax hm hr hw, by
          rw [of_eq hpub]; exact pushed_ok hK₂ h80 g1' h10' h11' hax' hm' hr' hw'⟩
    · exact Levels.taintR [] (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1


/-! ## The contract -/

/-- The memory of `sgSat`: the stack arguments `0x10000` and `2 ^ 32`. -/
def sgMem : Mem := fun a =>
  if a = BitVec.ofNat 64 (2 ^ 64 - 22) then 1 else if a = BitVec.ofNat 64 (2 ^ 64 - 12) then 1 else 0

theorem sgMem_0 : sgMem.readW (BitVec.ofNat 64 (2 ^ 64 - 24)) 64 = 0x10000 := by decide
theorem sgMem_1 : sgMem.readW (BitVec.ofNat 64 (2 ^ 64 - 16)) 64 = BitVec.ofNat 64 (2 ^ 32) := by decide

/-- A state of `signContract`'s precondition: the stack at the top of memory,
the signature at `0x10000` and the scratch at `2 ^ 32`. -/
def sgSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => BitVec.ofNat 64 (2 ^ 64 - 32)
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := sgMem
  rd := [⟨0x1000, p.skLen⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, p.n⟩, ⟨BitVec.ofNat 64 (2 ^ 64 - 24), 16⟩]
  wr := [⟨0x10000, p.sigLen⟩, ⟨BitVec.ofNat 64 (2 ^ 32), scratchWords * 8⟩]

theorem sgSat_arg0 (p : Params) : stackArg (sgSat p) 0 = 0x10000 := sgMem_0
theorem sgSat_arg1 (p : Params) : stackArg (sgSat p) 1 = BitVec.ofNat 64 (2 ^ 32) := sgMem_1

theorem sg_implies {p : Params} (hp : VerifyTop.VPar p) (n : Nat) (hs : n + 1 < 2 ^ 63) :
    (sgK p (n + 1)).Implies (Spec.SlhDsa.signContract p X86_64.abi (n + 1)) := by
  refine ⟨fun s h => ?_, fun s s' _ h => ?_, fun s₁ s₂ _ _ h => ?_, ⟨sgSat p, ?_⟩⟩
  · sig_pre [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, X86_64.abi, VG.X86_64.argRegs, List.range,
      List.range.loop] at h
    sig_split h
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27
      a28 a29 a30 a31 a32 a33 a34
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
      a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, h⟩
  · sig_post [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, X86_64.abi, VG.X86_64.argRegs, List.range,
      List.range.loop]
    exact h
  · sig_pub [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, X86_64.abi, VG.X86_64.argRegs, List.range,
      List.range.loop] at h
    obtain ⟨hsp, -, hdi, hsi, hdx, hcx, h8, h9, a0, a1⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, a0, a1⟩
  · have hsk : p.skLen ≤ 128 := by simp only [Params.skLen]; rcases hp.n with h | h | h <;> omega
    have hn : p.n ≤ 32 := by rcases hp.n with h | h | h <;> omega
    have hsl := hp.sigLt
    have hsw : scratchWords * 8 = 65536 := rfl
    sig_pre [Spec.SlhDsa.signContract, Spec.SlhDsa.signSig, X86_64.abi, VG.X86_64.argRegs, List.range,
      List.range.loop, sgSat_arg0, sgSat_arg1]
    have ea : stackArgAddr (sgSat p) 0 = BitVec.ofNat 64 (2 ^ 64 - 24) := rfl
    have e1 : (0x1000 : Addr).toNat = 0x1000 := rfl
    have e2 : (0x2000 : Addr).toNat = 0x2000 := rfl
    have e3 : (0x3000 : Addr).toNat = 0x3000 := rfl
    have e4 : (0x4000 : Addr).toNat = 0x4000 := rfl
    have e5 : (0x10000 : Addr).toNat = 0x10000 := rfl
    have e6 : (BitVec.ofNat 64 (2 ^ 32)).toNat = 2 ^ 32 := rfl
    have e7 : (BitVec.ofNat 64 (2 ^ 64 - 24)).toNat = 2 ^ 64 - 24 := rfl
    have e8 : (BitVec.ofNat 64 (2 ^ 64 - 32)).toNat = 2 ^ 64 - 32 := rfl
    have e0 : (0 : BitVec 64).toNat = 0 := rfl
    have e9 : (BitVec.ofNat 64 (2 ^ 64 - 32) - BitVec.ofNat 64 (n + 1)).toNat = 2 ^ 64 - 32 - (n + 1) := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e8, BitVec.toNat_ofNat]; omega), e8, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    sig_and_intros
    all_goals try rw [ea]
    all_goals first
      | omega
      | (apply Offset.disjoint_of_le <;> dsimp only <;> omega)
      | (apply Region.Disjoint.symm; apply Offset.disjoint_of_le <;> dsimp only <;> omega)
      | rfl

/-! ## `Verified` -/

/-- `vg_slhdsa_shake_*_sign` for a SHAKE parameter set `p`, any implementation
`T` of `thash4` and any FORS signing function `F` meets `signContract` in constant time. -/
theorem sign_verified' {p : Params} (hS : VerifyTop.S6 p) (hz : Wots4.Sz p) (hh : XmssTree.Hps p.hp)
    (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns} (ht : f.t4 = T.code)
    (F : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f)) {stack : Nat} (hst : T.stack + 104 ≤ stack)
    (hFs : F.stack + 80 ≤ stack) (h62 : stack < 2 ^ 62) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Shake.sign p f) (Spec.SlhDsa.signContract p X86_64.abi stack) := by
  obtain ⟨n, rfl⟩ : ∃ n, stack = n + 1 := ⟨stack - 1, by omega⟩
  exact Verified.of_correct (fun s h => sign_wp hS.par hz hh T ht F hst hFs h62 h)
    (sign_ct hS hz hh T ht F hst hFs h62) (sg_implies hS.par n (by omega))

end VG.Proof.SlhDsa.X86_64.SignTop
