module

public import VerifiedGarbage.Proof.AesCbc.X86_64.CT
public import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.X86_64.CT
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Body
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Block
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CBC on x86-64: groups of four blocks

The decryptions whose blocks can be deciphered independently (CBC's and
CFB128's) take four blocks at a time while at least four are left, by one
call of the block function each, and the rest one at a time
(`Impl.AesCbc.X86_64.groups`).

* `blk_call4`, `blk_rel4`: a call of a block function on four blocks `D` in
  place, with working space `S`, as `blk_call` and `blk_rel` on one.
* `groups_wp`: if one run of `group` takes the loop invariant (`LInv`) from
  `k` blocks to `k + 4` and sets CF when fewer than four are left
  (`GroupOk`), and `one` takes it from `k` to `k + 1` (`BodyOk`), `groups`
  takes it from no blocks to all of them; `batched_wp`, the whole function.
* `groups_rel`, `batched_ct`: the same for constant time, from `GroupCt` and
  `BodyCt`; `group_ct`, for a group of code before the call, the call, and
  code after it.
* `xorAt_ok`, `callArgs4_ok`: the straight-line pieces of the groups.
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)

/-! ## A call of a block function on four blocks -/

theorem four_toNat : (4 : BitVec 64).toNat = 4 := rfl

/-- What a call of a block function on four blocks needs. -/
structure CallPre4 (s : State) (W D S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = 4
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 64⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 64⟩ : Region).Disjoint ⟨S, 2048⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 64⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 64 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 64⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 64⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on four blocks leaves. -/
structure CallPost4 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 64⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : ∀ j < 4, bytesAt s'.mem (D + BitVec.ofNat 64 (16 * j)) 16 =
    (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * j)))).toList

theorem CallPre4.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre4 s W D S R) :
    (Proof.Aes.blocksX86_64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 64⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, four_toNat, Nat.reduceMul]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.stkD, h.stkS, h.wrap, h.rounds⟩

/-- Block `j` of `n` after a function of states replaced each. -/
theorem bytesAt_of_statesAt_n {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {j : Nat} (hj : j < n) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * j)) 16 =
      (g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)))).toList := by
  have := congrArg (·[j]?) h
  simp only [Spec.Aes.statesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at this
  rw [bytesAt_toList, this]

theorem blk_call4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre4 s W D S R) :
    WP isa (.call b.name b.code) s (CallPost4 f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksX86_64 f) ok nosp (by rw [depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨D, 64⟩, ⟨S, 2048⟩]) h.blk_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, fun j hj => ?_⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hR, four_toNat] at hpost
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eW := bytesAt_frame fE (p := W) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkW.sub_right (Region.sub_prefix hRb)).symm)
    (by omega)
  have eD := bytesAt_frame fE (p := D + BitVec.ofNat 64 (16 * j)) (n := 16)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkD.sub_right (Offset.sub_base _ (by omega))).symm) (by decide)
  rw [← hm₂, bytesAt_of_statesAt_n hpost hj, eW, ← ofFn_bytesAt, eD, ofFn_bytesAt]

/-- Calls of a block function on four blocks, with the same arguments in
both runs, are constant time. -/
theorem blk_rel4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W D S : Addr, ∃ R : Nat,
      CallPre4 s₁ W D S R ∧ CallPre4 s₂ W D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call b.name b.code) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The straight-line pieces -/

/-- The block at `Q` (at `src + e`) XORed into the block at `P` (at `dst + d`). -/
theorem xorAt_ok (s : State) {dst src : Reg} {d e : Nat} {P Q : Addr}
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (hsrc : src ≠ .rax) (hdst : dst ≠ .rax) :
    ∃ s', runBlock isa (xorAt dst d src e) s = some s' ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, xorAt, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hsrc, hdst, hp, hp8, hq, hq8, rp, rp8, rq, rq8, wp, wp8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

/-- The arguments of the block function for the four blocks at `r13`. -/
theorem callArgs4_ok (s : State) :
    ∃ s', runBlock isa callArgs4 s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r13 ∧
      s'.gpr .rcx = 4 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [callArgs4, runBlock_cons, runStep_some, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

/-! ## Regions of a group -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.data_sub4 {k : Nat} (hk : k + 4 ≤ N s₀) : Region.Sub ⟨blk s₀ k, 64⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

omit hp in
/-- Block `k + j` as an offset of block `k`. -/
theorem UPre.blk_add {k j : Nat} : blk s₀ k + BitVec.ofNat 64 (16 * j) = blk s₀ (k + j) := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j)) (by omega)]

omit hp in
theorem UPre.blk_add8 {k j : Nat} :
    blk s₀ k + BitVec.ofNat 64 (16 * j + 8) = blk s₀ (k + j) + BitVec.ofNat 64 8 := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega),
    Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega)]

/-- The arguments of a call on blocks `k` to `k + 3`, with the working space
at the start of the scratch buffer. -/
theorem UPre.callPre4 {k : Nat} (hk : k + 4 ≤ N s₀) {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = blk s₀ k)
    (rcx : s.gpr .rcx = 4) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre4 s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub4 hk)
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.data_sub4 hk)).sub_right (Region.sub_prefix (by decide))
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_data.sub_right (UPre.data_sub4 hk)
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := by have := hp.data_wrap; rw [hp.blk_toNat (by omega)]; omega
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The arguments of a call on the four blocks of `gR`, with the working
space at the start of the scratch buffer. -/
theorem UPre.callPre4G {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = S s₀ + BitVec.ofNat 64 2112)
    (rcx : s.gpr .rcx = 4) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre4 s (W s₀) (S s₀ + BitVec.ofNat 64 2112) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_scr.sub_right (UPre.scr_sub (by decide))
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := by
    have := hp.scr_wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2112, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2112, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- Block `i` before a step from `k ≤ i`, from the invariant. -/
theorem LInv.blockAt {M : Mode} {s₀ : State} {k i : Nat} {s : State} (h : LInv M s₀ k s) (hki : k ≤ i)
    (hi : i < N s₀) :
    bytesAt s.mem (blk s₀ i) 16 = (blks s₀)[i]'(by simp [Spec.Cbc.blocksAt]; exact hi) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have := congrArg (·[i]?) h.data
  simp only [List.getElem?_eq_getElem (show i < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hi),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ i by omega), hl, List.getElem?_drop,
    Nat.add_sub_cancel' hki,
    List.getElem?_eq_getElem (show i < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hi)] at this
  show bytesAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * i)) 16 = _
  rw [← getElem_blocksAt _ _ hi]
  exact Option.some.inj this

/-! ## The regions of a group -/

/-- Slot `j` of the four blocks a group keeps (in `gR`). -/
abbrev sl (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (gOff + 16 * j)

theorem sl8 (s₀ : State) (j : Nat) :
    S s₀ + BitVec.ofNat 64 (gOff + 16 * j + 8) = sl s₀ j + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]

theorem cSl (s₀ : State) {j : Nat} (hj : j < 4) : (scrR s₀).Contains (sl s₀ j) 8 :=
  Offset.contains_base _ (by simp only [gOff]; omega) (by simp only [gOff]; omega)

theorem cSl8 (s₀ : State) {j : Nat} (hj : j < 4) : (scrR s₀).Contains (sl s₀ j + BitVec.ofNat 64 8) 8 := by
  rw [← sl8]; exact Offset.contains_base _ (by simp only [gOff]; omega) (by simp only [gOff]; omega)

theorem sl_sub (s₀ : State) {j : Nat} (hj : j < 4) : Region.Sub ⟨sl s₀ j, 16⟩ (gR s₀) :=
  Offset.sub _ (by simp only [gOff]; omega) (by simp only [gOff]; omega)

section
variable {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
include hp hk

theorem UPre.dBB {a b : Nat} (ha : a < 4) (hb : b < 4) (hab : a ≠ b) :
    (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨blk s₀ (k + b), 16⟩ :=
  hp.blk_disjoint (by omega) (by omega) (by omega)

theorem UPre.dBT {a b : Nat} (ha : a < 4) (hb : b < 4) :
    (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨sl s₀ b, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega))).sub_right (UPre.scr_sub (by simp only [gOff]; omega))

theorem UPre.dBI {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.blk_iv (by omega)

theorem UPre.dBS {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega))).sub_right (Region.sub_prefix (by decide))

theorem UPre.dBG {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint (gR s₀) :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega))).sub_right (UPre.scr_sub (by decide))

theorem UPre.dBK {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint (stkR s₀) :=
  hp.stk_data.symm.sub_left (UPre.data_sub (by omega))

theorem UPre.dT64 {b : Nat} (hb : b < 4) : (⟨sl s₀ b, 16⟩ : Region).Disjoint ⟨blk s₀ k, 64⟩ :=
  ((hp.data_scr.sub_left (UPre.data_sub4 hk)).sub_right (UPre.scr_sub (by simp only [gOff]; omega))).symm

theorem UPre.dI64 : (ivR s₀).Disjoint ⟨blk s₀ k, 64⟩ := hp.iv_data.sub_right (UPre.data_sub4 hk)

end

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dTT {a b : Nat} (ha : a < 4) (hb : b < 4) (hab : a ≠ b) :
    (⟨sl s₀ a, 16⟩ : Region).Disjoint ⟨sl s₀ b, 16⟩ :=
  Offset.disjoint _ (by simp only [gOff]; omega) (by simp only [gOff]; omega) (by simp only [gOff]; omega)

theorem UPre.dTI {b : Nat} (hb : b < 4) : (⟨sl s₀ b, 16⟩ : Region).Disjoint (ivR s₀) :=
  (hp.iv_scr.sub_right (UPre.scr_sub (by simp only [gOff]; omega))).symm

theorem UPre.dTS {b : Nat} (hb : b < 4) : (⟨sl s₀ b, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by simp only [gOff]; omega) (by have := hp.scr_wrap; simp only [gOff]; omega)

theorem UPre.dTK {b : Nat} (hb : b < 4) : (⟨sl s₀ b, 16⟩ : Region).Disjoint (stkR s₀) :=
  (hp.stk_scr.sub_right (UPre.scr_sub (by simp only [gOff]; omega))).symm

theorem UPre.dIS : (ivR s₀).Disjoint ⟨S s₀, 2048⟩ := hp.iv_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.dIG : (ivR s₀).Disjoint (gR s₀) := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.dIK : (ivR s₀).Disjoint (stkR s₀) := hp.stk_iv.symm

end

theorem all_cons {p : Region → Prop} {a : Region} {l : List Region} (ha : p a) (hl : ∀ r ∈ l, p r) :
    ∀ r ∈ a :: l, p r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ha
  · exact hl r hr

theorem all_nil {p : Region → Prop} : ∀ r ∈ ([] : List Region), p r := fun _ h => by simp at h

theorem copyMem_other (m : Mem) {P Q p : Addr} (h : (⟨p, 16⟩ : Region).Disjoint ⟨P, 16⟩) :
    bytesAt (copyMem m P Q) p 16 = bytesAt m p 16 :=
  bytesAt_frame (copyMem_frame m P Q) (all_cons h all_nil) (by decide)

theorem xorMem_other (m : Mem) {P Q p : Addr} (h : (⟨p, 16⟩ : Region).Disjoint ⟨P, 16⟩) :
    bytesAt (xorMem m P Q) p 16 = bytesAt m p 16 :=
  bytesAt_frame (xorMem_frame m P Q) (all_cons h all_nil) (by decide)

theorem copyMem_frameG {s₀ : State} (m : Mem) {j : Nat} (hj : j < 4) (Q : Addr) :
    Frame [gR s₀] m (copyMem m (sl s₀ j) Q) :=
  (copyMem_frame m _ Q).sub (all_cons ⟨gR s₀, by simp, sl_sub s₀ hj⟩ all_nil)

theorem blk_sub64 {s₀ : State} {k j : Nat} (hj : j < 4) :
    Region.Sub ⟨blk s₀ (k + j), 16⟩ ⟨blk s₀ k, 64⟩ :=
  Offset.sub _ (by omega) (by omega)

theorem xorMem_frameB {s₀ : State} {k : Nat} (m : Mem) {j : Nat} (hj : j < 4) (Q : Addr) :
    Frame [⟨blk s₀ k, 64⟩] m (xorMem m (blk s₀ (k + j)) Q) :=
  (xorMem_frame m _ Q).sub (all_cons ⟨_, by simp, blk_sub64 hj⟩ all_nil)

/-- On to the block after the four, with CF set if fewer than four are left. -/
theorem advance4_regs {s₀ : State} {k : Nat} (hk : k + 4 ≤ N s₀) {s : State}
    (h13 : s.gpr .r13 = blk s₀ k) (h14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa advance4 s = some s' ∧ s'.gpr .r13 = blk s₀ (k + 4) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + 4)) ∧ s'.cf = some (decide (N s₀ - (k + 4) < 4)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hN := (s₀.gpr .r8).isLt
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  have dec : BitVec.ofNat 64 (N s₀ - k) - 4 = BitVec.ofNat 64 (N s₀ - (k + 4)) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, advance4, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, e64, e4]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags, cf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, h13, h14, dec]
  refine ⟨?_, trivial, ?_, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩
  · rw [Offset.add_add_eq _ (c := 16 * (k + 4)) (by omega)]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN), four_toNat]

/-- The blocks after four of them changed. -/
theorem blocksAt_set4 {m m' : Mem} {p : Addr} {n k : Nat}
    (h : ∀ j < n, (j < k ∨ k + 4 ≤ j) →
      bytesAt m' (p + BitVec.ofNat 64 (16 * j)) 16 = bytesAt m (p + BitVec.ofNat 64 (16 * j)) 16) :
    Spec.Cbc.blocksAt m' p n =
      (((((Spec.Cbc.blocksAt m p n).set k (bytesAt m' (p + BitVec.ofNat 64 (16 * k)) 16)).set (k + 1)
        (bytesAt m' (p + BitVec.ofNat 64 (16 * (k + 1))) 16)).set (k + 1 + 1)
          (bytesAt m' (p + BitVec.ofNat 64 (16 * (k + 1 + 1))) 16)).set (k + 1 + 1 + 1)
            (bytesAt m' (p + BitVec.ofNat 64 (16 * (k + 1 + 1 + 1))) 16)) := by
  apply List.ext_getElem (by simp [length_blocksAt])
  intro j h₁ _
  rw [length_blocksAt] at h₁
  simp only [List.getElem_set, getElem_blocksAt _ _ h₁]
  by_cases e₃ : k + 1 + 1 + 1 = j
  · rw [ite_eq_left e₃, e₃]
  rw [ite_eq_right e₃]
  by_cases e₂ : k + 1 + 1 = j
  · rw [ite_eq_left e₂, e₂]
  rw [ite_eq_right e₂]
  by_cases e₁ : k + 1 = j
  · rw [ite_eq_left e₁, e₁]
  rw [ite_eq_right e₁]
  by_cases e₀ : k = j
  · rw [ite_eq_left e₀, e₀]
  rw [ite_eq_right e₀]
  exact h j h₁ (by omega)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The blocks after a step that changed only blocks `k` to `k + 3`, the
chaining value, the scratch buffer but the saved registers and the stack. -/
theorem UPre.blocksAt_step4 {m m' : Mem} {k : Nat} (hk : k + 4 ≤ N s₀)
    (hf : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] m m')
    {ys : List (List Byte)} (hy : Spec.Cbc.blocksAt m (Dp s₀) (N s₀) = ys ++ (blks s₀).drop k)
    (hl : ys.length = k) :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      ys ++ [bytesAt m' (blk s₀ (k + 0)) 16, bytesAt m' (blk s₀ (k + 1)) 16, bytesAt m' (blk s₀ (k + 2)) 16,
        bytesAt m' (blk s₀ (k + 3)) 16] ++ (blks s₀).drop (k + 4) := by
  have hn : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  rw [blocksAt_set4 fun j hj hjk => bytesAt_frame hf (fun r hr => ?_) (by decide), hy,
    set_prefix _ _ _ hl (by omega), set_prefix _ _ _ (by simp [hl]) (by omega),
    set_prefix _ _ _ (by simp [hl]) (by omega), set_prefix _ _ _ (by simp [hl]) (by omega)]
  · simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hd := hp.data_wrap
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
    · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (UPre.scr_sub (by decide))
    · exact hp.stk_data.symm.sub_left (UPre.data_sub hj)

omit hp in
/-- The frame of a group, in the regions the invariant allows. -/
theorem stepFrame4 {k : Nat} (hk : k + 4 ≤ N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub4 hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨gR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

omit hp in
/-- The frame of a group, in the regions the function writes. -/
theorem UPre.bigStep {m m' : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] m m') :
    Frame (Big s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

end

/-! ## The loop of groups -/

/-- One run of `group` takes the invariant from `k` blocks to `k + 4` when at
least four are left, and sets CF if fewer than four are then left. -/
def GroupOk (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 4 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa group s fun s' => LInv M s₀ (k + 4) s' ∧ s'.cf = some (decide (N s₀ - (k + 4) < 4))

/-- The invariant holds of a state with the same registers, memory and
regions. -/
theorem LInv.congr {M : Mode} {s₀ : State} {k : Nat} {s s' : State} (h : LInv M s₀ k s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    LInv M s₀ k s' where
  rbx := by rw [hg]; exact h.rbx
  rbp := by rw [hg]; exact h.rbp
  r12 := by rw [hg]; exact h.r12
  r13 := by rw [hg]; exact h.r13
  r14 := by rw [hg]; exact h.r14
  r15 := by rw [hg]; exact h.r15
  rsp := by rw [hg]; exact h.rsp
  rd := by rw [hrd]; exact h.rd
  wr := by rw [hwr]; exact h.wr
  frame := by rw [hm]; exact h.frame
  data := by rw [hm]; exact h.data
  iv := by rw [hm]; exact h.iv

theorem cmp4_wp {M : Mode} {s₀ : State} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block [.alu .cmp .r14 (.imm 4)]) s fun s' =>
      LInv M s₀ k s' ∧ s'.cf = some (decide (N s₀ - k < 4)) := by
  have hN := (s₀.gpr .r8).isLt
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, e4, Option.bind_some]
    rfl, ?_, ?_⟩
  · exact h.congr rfl rfl rfl rfl
  · rw [cf_arithFlags, h.r14, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN), four_toNat]

theorem test14_wp {M : Mode} {s₀ : State} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block [.alu .test .r14 (.reg .r14)]) s fun s' =>
      LInv M s₀ k s' ∧ s'.zf = some (decide (N s₀ - k = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_, ?_⟩
  · exact h.congr rfl rfl rfl rfl
  · rw [zf_arithFlags, BitVec.and_self, h.r14, beq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN)]

/-- The groups, from `k₀` blocks: the invariant after some `k` blocks with
fewer than four left. -/
theorem groupLoop_wp {M : Mode} {group : Prog isa} (hg : GroupOk M group) {s₀ : State} (hp : UPre s₀)
    {k₀ : Nat} (hk₀ : k₀ ≤ N s₀) {s : State} (h : LInv M s₀ k₀ s)
    (hcf : s.cf = some (decide (N s₀ - k₀ < 4))) :
    WP isa (.ite .b (.block []) (.loop group .ae)) s fun s' =>
      ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s' := by
  refine WP.ite (decide (N s₀ - k₀ < 4)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨k₀, hk₀, by simpa using hb, h⟩
  · let I : Nat → State → Prop := fun m s => ∃ k, m = N s₀ - k ∧ k + 4 ≤ N s₀ ∧ LInv M s₀ k s
    have hstep : ∀ m s, I m s → WP isa group s (fun s' =>
        (eval .ae s' = some false ∧ ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨k, rfl, hk, hI⟩
      refine WP.mono (hg hp hk hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : N s₀ - (k + 4) < 4
      · exact .inl ⟨by simp [eval, hcf', hlt], k + 4, hk, hlt, hI'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (k + 4), by omega, k + 4, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀ - k₀) s ⟨k₀, rfl, by simp at hb; omega, h⟩

/-- `groups group one` takes the invariant from no blocks to all of them. -/
theorem groups_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one)
    {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ 0 s) :
    WP isa (groups group one) s (LInv M s₀ (N s₀)) := by
  refine WP.seq (WP.mono (cmp4_wp h) fun s₁ ⟨h₁, cf₁⟩ => ?_)
  refine WP.seq (WP.mono (groupLoop_wp hg hp (Nat.zero_le _) h₁ cf₁) fun s₂ ⟨k, hk, _, h₂⟩ => ?_)
  refine WP.seq (WP.mono (test14_wp h₂) fun s₃ ⟨h₃, zf₃⟩ => ?_)
  refine WP.ite (decide (N s₀ - k = 0)) (by simp [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have : k = N s₀ := by simp at hz; omega
    exact WP.block_nil (this ▸ h₃)
  · exact loop_ok hb hp (by simp at hz; omega) h₃

theorem batched_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one) {s₀ : State}
    (h0 : (modeX86_64 M).pre s₀) :
    WP isa (batched group one) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 M).post s₀ s' :=
  ends_wp h0 fun hp _ _ h => groups_wp hg hb hp h

/-! ## Constant time -/

/-- One run of `group` from `k` blocks is constant time. -/
def GroupCt (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modeX86_64 M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) group fun _ _ => True

/-- What is known between the code before the call of a group and the call,
on the four blocks at `D`. -/
structure Mid4 (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre4 s (W s₀) D (S s₀) (R s₀)
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem Mid4.of {s₀ : State} {k : Nat} {D : Addr} {s s₁ : State} {M : Mode} (h : LInv M s₀ k s)
    (pre : CallPre4 s₁ (W s₀) D (S s₀) (R s₀)) (saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) :
    Mid4 s₀ k D s₁ :=
  ⟨pre, by rw [saved .r12 (by simp [calleeSaved]), h.r12], by rw [saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [saved .r14 (by simp [calleeSaved]), h.r14], by rw [saved .r15 (by simp [calleeSaved]), h.r15],
    by rw [saved .rsp (by simp [calleeSaved]), h.rsp]⟩

theorem After.of4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {D : Addr}
    {s s' : State} (h : Mid4 s₀ k D s) (hc : CallPost4 f s (W s₀) D (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .r12 (by simp [calleeSaved]), h.r12], by rw [hc.saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [hc.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hc.saved .r15 (by simp [calleeSaved]), h.r15]⟩

/-- A group: code before the call (`pre`), the call of `b` on the four blocks
at `D s₀ k` (public), and code after it (`post`), constant time when `pre`'s
addresses and branches depend only on the registers the invariant pins and
`post`'s on `r12` to `r15`. -/
theorem group_ct {M : Mode} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (modeX86_64 M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    {b : Impl.Aes.X86_64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 4 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s (Mid4 s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeX86_64 M).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint)
    (P := fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid4 s₀ k (D s₀ k)) (F₂ := Mid4 s₀' k (D s₀' k)) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel4 ok ct (P := fun s₁ s₂ => Mid4 s₀ k (D s₀ k) s₁ ∧ Mid4 s₀' k (D s₀' k) s₂)
      fun s₁ s₂ h =>
      ⟨_, _, _, _, h.1.pre, by
        rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call4 ok nosp depth h.1.pre) fun _ hc => After.of4 h.1 hc,
       WP.mono (blk_call4 ok nosp depth h.2.pre) fun _ hc => After.of4 h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r13, h.2.r13, pub_blk hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]
      · rw [h.1.r15, h.2.r15, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-- The loop's relation, with the number of iterations left. -/
def GRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂

/-- Both runs after `k` blocks, with fewer than four left. -/
def GDone (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂

theorem groupLoop_ct {M : Mode} {group : Prog isa} (hg : GroupOk M group) (hc : GroupCt M group)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeX86_64 M).pub s₀ s₀') (n : Nat) :
    RelCT isa (GRel M s₀ s₀' n) (.loop group .ae) (GDone M s₀ s₀') := by
  refine RelCT.loop (M := isa) (GRel M s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : GRel M s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k + 4 ≤ N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp
    (F₁ := fun (s' : State) => LInv M s₀ (k + 4) s' ∧ s'.cf = some (decide (N s₀ - (k + 4) < 4)))
    (F₂ := fun (s' : State) => LInv M s₀' (k + 4) s' ∧ s'.cf = some (decide (N s₀' - (k + 4) < 4)))
    fun _ _ h => ⟨hg hp h.1 h.2.1, hg hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ => ?_
  rw [← hN] at c₂
  have e₁ : isa.eval .ae s₁ = some (!decide (N s₀ - (k + 4) < 4)) := by
    show s₁.cf.map _ = _; rw [c₁]; rfl
  have e₂ : isa.eval .ae s₂ = some (!decide (N s₀ - (k + 4) < 4)) := by
    show s₂.cf.map _ = _; rw [c₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have : N s₀ - (k + 4) < 4 := by simpa using hf
    exact ⟨k + 4, hk, this, l₁, l₂⟩
  · rw [e₁] at ht
    have : ¬ N s₀ - (k + 4) < 4 := by simpa using ht
    exact ⟨N s₀ - (k + 4), by omega, k + 4, rfl, by omega, l₁, l₂⟩

theorem groups_rel {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeX86_64 M).pub s₀ s₀') :
    RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) (groups group one)
      fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b := by
  have hN := pub_N hq
  obtain ⟨_, hcmp⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block [.alu .cmp .r14 (.imm 4)]) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, htest⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block [.alu .test .r14 (.reg .r14)]) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r14 {k : Nat} {a b : State} (ha : LInv M s₀ k a) (hb : LInv M s₀' k b) : a.gpr .r14 = b.gpr .r14 := by
    rw [ha.r14, hb.r14, hN]
  -- `cmp r14, 4`.
  have cmp := (RelCT.taint (A := taint) (P := fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact r14 h.1 h.2) hcmp).wp
    (F₁ := fun (s : State) => LInv M s₀ 0 s ∧ s.cf = some (decide (N s₀ - 0 < 4)))
    (F₂ := fun (s : State) => LInv M s₀' 0 s ∧ s.cf = some (decide (N s₀' - 0 < 4)))
    fun a b h => ⟨cmp4_wp h.1, cmp4_wp h.2⟩
  -- The groups, if at least four blocks.
  have loop : RelCT isa (fun a b => (LInv M s₀ 0 a ∧ a.cf = some (decide (N s₀ - 0 < 4))) ∧
      (LInv M s₀' 0 b ∧ b.cf = some (decide (N s₀' - 0 < 4))))
      (.ite .b (.block []) (.loop group .ae)) (GDone M s₀ s₀') := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.cf = b.cf; rw [h.1.2, h.2.2, hN]
    · have nil' := (RelCT.taint (A := taint)
        (P := fun a b => ((LInv M s₀ 0 a ∧ a.cf = some (decide (N s₀ - 0 < 4))) ∧
          (LInv M s₀' 0 b ∧ b.cf = some (decide (N s₀' - 0 < 4)))) ∧ isa.eval .b a = some true) _
        (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil).wp
        (F₁ := fun a => LInv M s₀ 0 a ∧ N s₀ - 0 < 4) (F₂ := LInv M s₀' 0) fun a b h =>
          ⟨WP.block_nil ⟨h.1.1.1, by
            have := h.2; change a.cf = _ at this; rw [h.1.1.2] at this; simpa using this⟩,
           WP.block_nil h.1.2.1⟩
      exact nil'.mono (fun _ _ h => h) fun _ _ h => ⟨0, Nat.zero_le _, h.2.1.2, h.2.1.1, h.2.2⟩
    · exact (groupLoop_ct hg hgc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, by
        have := h.2; change a.cf = _ at this; rw [h.1.1.2] at this
        have : ¬ (N s₀ - 0 < 4) := by simpa using this
        omega, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  -- The blocks left, one at a time.
  have tail : RelCT isa (GDone M s₀ s₀')
      (.seq (.block [.alu .test .r14 (.reg .r14)]) (.ite .e (.block []) (.loop one .ne)))
      fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b := by
    refine (RelCT.exists_ fun k => ?_).mono (fun a b (h : GDone M s₀ s₀' a b) => h) fun _ _ h => h
    by_cases hk : k ≤ N s₀
    swap
    · exact RelCT.of_false fun _ _ h => hk h.1
    have test := (RelCT.taint (A := taint)
      (P := fun a b => k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k a ∧ LInv M s₀' k b) _
      (fun a b h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact r14 h.2.2.1 h.2.2.2) htest).wp
      (F₁ := fun (s : State) => LInv M s₀ k s ∧ s.zf = some (decide (N s₀ - k = 0)))
      (F₂ := fun (s : State) => LInv M s₀' k s ∧ s.zf = some (decide (N s₀' - k = 0)))
      fun a b h => ⟨test14_wp h.2.2.1, test14_wp h.2.2.2⟩
    have rest : RelCT isa (fun a b => (LInv M s₀ k a ∧ a.zf = some (decide (N s₀ - k = 0))) ∧
        (LInv M s₀' k b ∧ b.zf = some (decide (N s₀' - k = 0))))
        (.ite .e (.block []) (.loop one .ne)) fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b := by
      refine RelCT.ite (fun a b h => ?_) ?_ ?_
      · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
      · have nil' := (RelCT.taint (A := taint)
          (P := fun a b => ((LInv M s₀ k a ∧ a.zf = some (decide (N s₀ - k = 0))) ∧
            (LInv M s₀' k b ∧ b.zf = some (decide (N s₀' - k = 0)))) ∧ isa.eval .e a = some true) _
          (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil).wp
          (F₁ := LInv M s₀ (N s₀)) (F₂ := LInv M s₀' (N s₀')) fun a b h => by
            have e : k = N s₀ := by
              have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
              have : N s₀ - k = 0 := by simpa using this
              omega
            exact ⟨WP.block_nil (e ▸ h.1.1.1), WP.block_nil (by rw [← hN, ← e]; exact h.1.2.1)⟩
        exact nil'.mono (fun _ _ h => h) fun _ _ h => h.2
      · exact (loop_ct hb hbc hp hp' hq (N s₀ - k)).mono (fun a b h => ⟨k, rfl, by
          have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
          have : ¬ (N s₀ - k = 0) := by simpa using this
          omega, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    exact (test.mono (fun _ _ h => h) fun _ _ h => h.2).seq rest
  exact (cmp.mono (fun _ _ h => h) fun _ _ h => h.2).seq (loop.seq tail)

theorem batched_ct {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one) :
    ConstantTime isa (modeX86_64 M).pre (modeX86_64 M).pub (batched group one) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' _ => groups_rel hg hgc hb hbc hp hp' hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.X86_64
