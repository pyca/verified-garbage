module

public import VerifiedGarbage.Proof.AesCbc.AArch64.CT
public import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.AArch64.CT
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Body
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: the groups of four blocks, which only CBC decryption takes, out of the modules the other modes import.

/-!
# AES-CBC on AArch64: groups of four blocks

The decryption, whose blocks can be deciphered independently, takes four
blocks at a time while at least four are left, by one call of the block
function each, and the rest one at a time (`Impl.AesCbc.AArch64.groups`).

* `blk_call4`, `blk_rel4`: a call of a block function on four blocks `D` in
  place, with working space `S`, as `blk_call` and `blk_rel` on one.
* `groups_wp`: if one run of `group` takes the loop invariant (`LInv`) from
  `k` blocks to `k + 4` and leaves `x9` one when fewer than four are left
  (`GroupOk`), and `one` takes it from `k` to `k + 1` (`BodyOk`), `groups`
  takes it from no blocks to all of them; `batched_wp`, the whole function.
* `groups_rel`, `batched_ct`: the same for constant time, from `GroupCt` and
  `BodyCt`; `group_ct`, for a group of code before the call, the call, and
  code after it.
* `decGroup_ok`: one run of `decGroup` takes the loop invariant from `k`
  blocks to `k + 4`, for any implementation of the block functions
  (`BlocksImpl`): the four ciphertext blocks `Cⱼ` are saved (the first three
  in the slots of `gR`, the fourth where a single block's is, `Sv`),
  deciphered in place by one call, and each XORed with `Cⱼ₋₁` (the chaining
  value for the first, the slot before for the others), and the fourth
  becomes the chaining value. `decGroup_ct`: it is constant time.
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-! ## Fewer than four blocks left -/

/-- The sign of `x - 4`, for `x` below `2⁶³`: whether `x` is less than four. -/
theorem sign_sub4 {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 4) >>> 63 = BitVec.ofNat 64 (if x < 4 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := x) (by omega_using [hx]),
    Nat.mod_eq_of_lt (a := 4) (by decide)]
  split
  · rw [BitVec.toNat_ofNat]; omega_arith
  · rw [BitVec.toNat_ofNat]; omega_arith

/-- `x9` is one if fewer than four of the blocks after the first `k` are
left, and zero otherwise. -/
abbrev Few (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .x9 = BitVec.ofNat 64 (if N s₀ - k < 4 then 1 else 0)

theorem eval_few_nonzero {s₀ : State} {k : Nat} {s : State} (h : Few s₀ k s) :
    isa.eval (.nonzero .x .x9) s = some (decide (N s₀ - k < 4)) := by
  show some (s.read .x .x9 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  by_cases hx : N s₀ - k < 4
  · rw [ite_eq_left hx]; simp [hx]
  · rw [ite_eq_right hx]; simp [hx]

theorem eval_few_zero {s₀ : State} {k : Nat} {s : State} (h : Few s₀ k s) :
    isa.eval (.zero .x .x9) s = some (!decide (N s₀ - k < 4)) := by
  show some (s.read .x .x9 == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  by_cases hx : N s₀ - k < 4
  · rw [ite_eq_left hx]; simp [hx]
  · rw [ite_eq_right hx]; simp [hx]

theorem few_ok (s : State) :
    ∃ s', runBlock isa few s = some s' ∧ s'.gpr .x9 = (s.gpr .x23 - BitVec.ofNat 64 4) >>> 63 ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    rw [few, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h₁ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁]

/-- There are fewer than `2⁶³` blocks. -/
theorem UPre.left_lt {s₀ : State} (hp : UPre s₀) (k : Nat) : N s₀ - k < 2 ^ 63 := by
  have := hp.data_wrap
  omega_using [this]

/-- The invariant holds of a state that differs in `x9` alone. -/
theorem LInv.congr9 {M : Mode} {s₀ : State} {k : Nat} {s s' : State} (h : LInv M s₀ k s)
    (hg : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LInv M s₀ k s' where
  x19 := by rw [hg _ (by decide)]; exact h.x19
  x20 := by rw [hg _ (by decide)]; exact h.x20
  x21 := by rw [hg _ (by decide)]; exact h.x21
  x22 := by rw [hg _ (by decide)]; exact h.x22
  x23 := by rw [hg _ (by decide)]; exact h.x23
  x24 := by rw [hg _ (by decide)]; exact h.x24
  other := fun r hr h19 h20 h21 h22 h23 h24 h30 => by
    rw [hg r (preserved_ne hr).1]; exact h.other r hr h19 h20 h21 h22 h23 h24 h30
  sp := by rw [hsp]; exact h.sp
  rd := by rw [hrd]; exact h.rd
  wr := by rw [hwr]; exact h.wr
  frame := by rw [hm]; exact h.frame
  data := by rw [hm]; exact h.data
  iv := by rw [hm]; exact h.iv

theorem few_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block few) s fun s' => LInv M s₀ k s' ∧ Few s₀ k s' := by
  obtain ⟨s', run, x9', keep, sp', mem', rd', wr'⟩ := few_ok s
  refine WP.of_runBlock ⟨s', run, h.congr9 keep sp' mem' rd' wr', ?_⟩
  rw [Few, x9', h.x23, sign_sub4 (hp.left_lt k)]

/-! ## A call of a block function on four blocks -/

theorem four_toNat : (4 : BitVec 64).toNat = 4 := rfl

/-- What a call of a block function on four blocks needs. -/
structure CallPre4 (s : State) (W D S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = 4
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 64⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 64⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 64 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 64⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 64⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on four blocks leaves. -/
structure CallPost4 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 64⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : ∀ j < 4, bytesAt s'.mem (D + BitVec.ofNat 64 (16 * j)) 16 =
    (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * j)))).toList

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre4.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre4 s W D S R) :
    (Proof.Aes.blocksAArch64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 64⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, four_toNat, Nat.reduceMul]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.wrap, h.rounds⟩

/-- Block `j` of `n` after a function of states replaced each. -/
theorem bytesAt_of_statesAt_n {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {j : Nat} (hj : j < n) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * j)) 16 =
      (g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)))).toList := by
  have := congrArg (·[j]?) h
  simp only [Spec.Aes.statesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at this
  rw [bytesAt_toList, this]

theorem blk_call4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre4 s W D S R) :
    WP isa (.call b.name b.code) s (CallPost4 f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksAArch64 f) ok (rd := [⟨W, 240⟩])
    (wr := [⟨D, 64⟩, ⟨S, 2048⟩]) h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, fun j hj => ?_⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, four_toNat] at hpost
  exact bytesAt_of_statesAt_n hpost hj

/-- Calls of a block function on four blocks, with the same arguments in
both runs, are constant time. -/
theorem blk_rel4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    {W D S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre4 s₁ W D S R ∧ CallPre4 s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call b.name b.code) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 64⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The straight-line pieces -/

/-- The block at `Q` (at `src + e`) XORed into the block at `P` (at `dst + d`). -/
theorem xorAt_ok (s : State) {dst src : Reg} {d e : Nat} {P Q : Addr}
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (hsrc : src ≠ .x9) (hsrc' : src ≠ .x10) (hdst : dst ≠ .x9) (hdst' : dst ≠ .x10)
    (hd : d % 8 = 0 ∧ d < 32768) (hd8 : (d + 8) % 8 = 0 ∧ d + 8 < 32768)
    (he : e % 8 = 0 ∧ e < 32768) (he8 : (e + 8) % 8 = 0 ∧ e + 8 < 32768) :
    ∃ s', runBlock isa (xorAt dst d src e) s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorAt, hsrc, hsrc', hdst, hdst', hd, hd8, he, he8, hp, hp8, hq, hq8, rp, rp8, rq, rq8,
    wp, wp8], ?_⟩
  refine ⟨fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [xorMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

/-- The arguments of the block function for the four blocks at `x22`. -/
theorem callArgs4_ok (s : State) :
    ∃ s', runBlock isa callArgs4 s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x22 ∧
      s'.gpr .x3 = 4 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [callArgs4], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- On to the block after the four, with `x9` one if fewer than four are left. -/
theorem advance4_regs {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀) {s : State}
    (h22 : s.gpr .x22 = blk s₀ k) (h23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa advance4 s = some s' ∧ s'.gpr .x22 = blk s₀ (k + 4) ∧
      s'.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + 4)) ∧ Few s₀ (k + 4) s' ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have dec : BitVec.ofNat 64 (N s₀ - k) - BitVec.ofNat 64 4 = BitVec.ofNat 64 (N s₀ - (k + 4)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [hk]), Nat.sub_sub]
  refine ⟨_, by
    rw [advance4, List.cons_append, List.cons_append, List.nil_append, few, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons, exec_lsr_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, State.read, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, h22]
    rw [Offset.add_add_eq _ (c := 16 * (k + 4)) (by omega_using [])]
  · simp only [gpr_write, State.read, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, h23, dec]
  · simp only [Few, gpr_write, State.read, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, h23, dec]
    exact sign_sub4 (hp.left_lt _)
  · simp [gpr_write, h₁, h₂, h₃]

/-! ## Regions of a group -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.data_sub4 {k : Nat} (hk : k + 4 ≤ N s₀) : Region.Sub ⟨blk s₀ k, 64⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

omit hp in
/-- Block `k + j` as an offset of block `k`. -/
theorem UPre.blk_add {k j : Nat} : blk s₀ k + BitVec.ofNat 64 (16 * j) = blk s₀ (k + j) := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j)) (by omega_using [])]

omit hp in
theorem UPre.blk_add8 {k j : Nat} :
    blk s₀ k + BitVec.ofNat 64 (16 * j + 8) = blk s₀ (k + j) + BitVec.ofNat 64 8 := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega_using []),
    Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega_using [])]

/-- The arguments of a call on blocks `k` to `k + 3`, with the working space
at the start of the scratch buffer. -/
theorem UPre.callPre4 {k : Nat} (hk : k + 4 ≤ N s₀) {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = blk s₀ k)
    (x3 : s.gpr .x3 = 4) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre4 s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub4 hk)
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.data_sub4 hk)).sub_right (Region.sub_prefix (by decide))
  wrap := by have := hp.data_wrap; rw [hp.blk_toNat (by omega_using [hk])]; omega_using [hk, this]
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hk]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega_using [hk]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- Block `i` before a step from `k ≤ i`, from the invariant. -/
theorem LInv.blockAt {M : Mode} {s₀ : State} {k i : Nat} {s : State} (h : LInv M s₀ k s) (hki : k ≤ i)
    (hi : i < N s₀) :
    bytesAt s.mem (blk s₀ i) 16 = (blks s₀)[i]'(by simp [Spec.Cbc.blocksAt]; exact hi) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hki, hi]
  have := congrArg (·[i]?) h.data
  simp only [List.getElem?_eq_getElem (show i < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hi),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ i by omega_using [hki, hl]), hl, List.getElem?_drop,
    Nat.add_sub_cancel' hki,
    List.getElem?_eq_getElem (show i < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hi)] at this
  show bytesAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * i)) 16 = _
  rw [← getElem_blocksAt _ _ hi]
  exact Option.some.inj this

/-- Slot `j` of the first three blocks a group keeps (in `gR`). -/
abbrev sl (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (gOff + 16 * j)

theorem sl8 (s₀ : State) (j : Nat) :
    S s₀ + BitVec.ofNat 64 (gOff + 16 * j + 8) = sl s₀ j + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]

theorem cSl (s₀ : State) {j : Nat} (hj : j < 3) : (scrR s₀).Contains (sl s₀ j) 8 :=
  Offset.contains_base _ (by simp only [gOff]; omega_using [hj]) (by simp only [gOff]; omega_using [hj])

theorem cSl8 (s₀ : State) {j : Nat} (hj : j < 3) : (scrR s₀).Contains (sl s₀ j + BitVec.ofNat 64 8) 8 := by
  rw [← sl8]; exact Offset.contains_base _ (by simp only [gOff]; omega_using [hj]) (by simp only [gOff]; omega_using [hj])

theorem sl_sub (s₀ : State) {j : Nat} (hj : j < 3) : Region.Sub ⟨sl s₀ j, 16⟩ (gR s₀) :=
  Offset.sub _ (by simp only [gOff]; omega_using []) (by simp only [gOff]; omega_using [hj])

section
variable {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
include hp hk

theorem UPre.dBB {a b : Nat} (ha : a < 4) (hb : b < 4) (hab : a ≠ b) :
    (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨blk s₀ (k + b), 16⟩ :=
  hp.blk_disjoint (by omega_using [hk, ha]) (by omega_using [hk, hb]) (by omega_using [hab])

theorem UPre.dBT {a b : Nat} (ha : a < 4) (hb : b < 3) :
    (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨sl s₀ b, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega_using [hk, ha]))).sub_right
    (UPre.scr_sub (by simp only [gOff]; omega_using [hb]))

theorem UPre.dBV {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  hp.blk_sv (by omega_using [hk, ha])

theorem UPre.dBI {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.blk_iv (by omega_using [hk, ha])

theorem UPre.dBS {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint ⟨S s₀, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega_using [hk, ha]))).sub_right (Region.sub_prefix (by decide))

theorem UPre.dBG {a : Nat} (ha : a < 4) : (⟨blk s₀ (k + a), 16⟩ : Region).Disjoint (gR s₀) :=
  (hp.data_scr.sub_left (UPre.data_sub (by omega_using [hk, ha]))).sub_right (UPre.scr_sub (by decide))

theorem UPre.dT64 {b : Nat} (hb : b < 3) : (⟨sl s₀ b, 16⟩ : Region).Disjoint ⟨blk s₀ k, 64⟩ :=
  ((hp.data_scr.sub_left (UPre.data_sub4 hk)).sub_right
    (UPre.scr_sub (by simp only [gOff]; omega_using [hb]))).symm

theorem UPre.dV64 : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨blk s₀ k, 64⟩ :=
  ((hp.data_scr.sub_left (UPre.data_sub4 hk)).sub_right (UPre.scr_sub (by decide))).symm

theorem UPre.dI64 : (ivR s₀).Disjoint ⟨blk s₀ k, 64⟩ := hp.iv_data.sub_right (UPre.data_sub4 hk)

end

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem UPre.dTT {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    (⟨sl s₀ a, 16⟩ : Region).Disjoint ⟨sl s₀ b, 16⟩ :=
  Offset.disjoint _ (by simp only [gOff]; omega_using [hab]) (by simp only [gOff]; omega_using [ha])
    (by simp only [gOff]; omega_using [hb])

omit hp in
theorem UPre.dTV {b : Nat} (hb : b < 3) : (⟨sl s₀ b, 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  Offset.disjoint _ (by simp only [gOff]; omega_using []) (by simp only [gOff]; omega_using [hb]) (by decide)

theorem UPre.dTI {b : Nat} (hb : b < 3) : (⟨sl s₀ b, 16⟩ : Region).Disjoint (ivR s₀) :=
  (hp.iv_scr.sub_right (UPre.scr_sub (by simp only [gOff]; omega_using [hb]))).symm

theorem UPre.dTS {b : Nat} (hb : b < 3) : (⟨sl s₀ b, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by simp only [gOff]; omega_using [])
    (by have := hp.scr_wrap; simp only [gOff]; omega_using [hb])

theorem UPre.dIS : (ivR s₀).Disjoint ⟨S s₀, 2048⟩ := hp.iv_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.dIS' : (ivR s₀).Disjoint ⟨S s₀, 2064⟩ := hp.iv_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.dIG : (ivR s₀).Disjoint (gR s₀) := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

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
  Proof.Cmac.bytesAt_frame (copyMem_frame m P Q) (all_cons h all_nil) (by decide)

theorem xorMem_other (m : Mem) {P Q p : Addr} (h : (⟨p, 16⟩ : Region).Disjoint ⟨P, 16⟩) :
    bytesAt (xorMem m P Q) p 16 = bytesAt m p 16 :=
  Proof.Cmac.bytesAt_frame (xorMem_frame m P Q) (all_cons h all_nil) (by decide)

theorem copyMem_frameG {s₀ : State} (m : Mem) {j : Nat} (hj : j < 3) (Q : Addr) :
    Frame [⟨S s₀, 2064⟩, gR s₀] m (copyMem m (sl s₀ j) Q) :=
  (copyMem_frame m _ Q).sub (all_cons ⟨gR s₀, by simp, sl_sub s₀ hj⟩ all_nil)

theorem copyMem_frameV {s₀ : State} (m : Mem) (Q : Addr) :
    Frame [⟨S s₀, 2064⟩, gR s₀] m (copyMem m (Sv s₀) Q) :=
  (copyMem_frame m _ Q).sub (all_cons ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩ all_nil)

theorem blk_sub64 {s₀ : State} {k j : Nat} (hj : j < 4) :
    Region.Sub ⟨blk s₀ (k + j), 16⟩ ⟨blk s₀ k, 64⟩ :=
  Offset.sub _ (by omega_using []) (by omega_using [hj])

theorem xorMem_frameB {s₀ : State} {k : Nat} (m : Mem) {j : Nat} (hj : j < 4) (Q : Addr) :
    Frame [⟨blk s₀ k, 64⟩] m (xorMem m (blk s₀ (k + j)) Q) :=
  (xorMem_frame m _ Q).sub (all_cons ⟨_, by simp, blk_sub64 hj⟩ all_nil)

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
  exact h j h₁ (by omega_using [e₃, e₂, e₁, e₀])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The blocks after a step that changed only blocks `k` to `k + 3`, the
chaining value and the scratch buffer but the saved registers. -/
theorem UPre.blocksAt_step4 {m m' : Mem} {k : Nat} (hk : k + 4 ≤ N s₀)
    (hf : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀] m m')
    {ys : List (List Byte)} (hy : Spec.Cbc.blocksAt m (Dp s₀) (N s₀) = ys ++ (blks s₀).drop k)
    (hl : ys.length = k) :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      ys ++ [bytesAt m' (blk s₀ (k + 0)) 16, bytesAt m' (blk s₀ (k + 1)) 16, bytesAt m' (blk s₀ (k + 2)) 16,
        bytesAt m' (blk s₀ (k + 3)) 16] ++ (blks s₀).drop (k + 4) := by
  have hn : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  rw [blocksAt_set4 fun j hj hjk => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide), hy,
    set_prefix _ _ _ hl (by omega_using [hk, hn]), set_prefix _ _ _ (by simp [hl]) (by omega_using [hk, hn]),
    set_prefix _ _ _ (by simp [hl]) (by omega_using [hk, hn]), set_prefix _ _ _ (by simp [hl]) (by omega_using [hk, hn])]
  · simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hd := hp.data_wrap
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, hd]) (by omega_using [hk, hd])
    · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
    · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (UPre.scr_sub (by decide))

omit hp in
/-- The frame of a group, in the regions the invariant allows. -/
theorem stepFrame4 {k : Nat} (hk : k + 4 ≤ N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub4 hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨gR s₀, by simp, fun _ h => h⟩

end

/-! ## The loop of groups -/

/-- One run of `group` takes the invariant from `k` blocks to `k + 4` when at
least four are left, and leaves `x9` one if fewer than four are then left. -/
def GroupOk (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 4 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa group s fun s' => LInv M s₀ (k + 4) s' ∧ Few s₀ (k + 4) s'

/-- The groups, from `k₀` blocks: the invariant after some `k` blocks with
fewer than four left. -/
theorem groupLoop_wp {M : Mode} {group : Prog isa} (hg : GroupOk M group) {s₀ : State} (hp : UPre s₀)
    {k₀ : Nat} (hk₀ : k₀ ≤ N s₀) {s : State} (h : LInv M s₀ k₀ s) (hf : Few s₀ k₀ s) :
    WP isa (.ite (.nonzero .x .x9) (.block []) (.loop group (.zero .x .x9))) s fun s' =>
      ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s' := by
  refine WP.ite (decide (N s₀ - k₀ < 4)) (eval_few_nonzero hf) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨k₀, hk₀, by simpa using hb, h⟩
  · let I : Nat → State → Prop := fun m s => ∃ k, m = N s₀ - k ∧ k + 4 ≤ N s₀ ∧ LInv M s₀ k s
    have hstep : ∀ m s, I m s → WP isa group s (fun s' =>
        (isa.eval (.zero .x .x9) s' = some false ∧ ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s') ∨
        (isa.eval (.zero .x .x9) s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨k, rfl, hk, hI⟩
      refine WP.mono (hg hp hk hI) fun s' ⟨hI', hf'⟩ => ?_
      by_cases hlt : N s₀ - (k + 4) < 4
      · exact .inl ⟨by rw [eval_few_zero hf']; simp [hlt], k + 4, hk, hlt, hI'⟩
      · exact .inr ⟨by rw [eval_few_zero hf']; simp [hlt], N s₀ - (k + 4), by omega_using [hk], k + 4, rfl,
          by omega_using [hlt], hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀ - k₀) s ⟨k₀, rfl, by simp at hb; omega_using [hb], h⟩

/-- `groups group one` takes the invariant from no blocks to all of them. -/
theorem groups_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one)
    {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ 0 s) :
    WP isa (groups group one) s (LInv M s₀ (N s₀)) := by
  refine WP.seq (WP.mono (few_wp hp h) fun s₁ ⟨h₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (groupLoop_wp hg hp (Nat.zero_le _) h₁ f₁) fun s₂ ⟨k, hk, _, h₂⟩ => ?_)
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_zero_x23 (x := N s₀ - k) (by omega_using [hN]) h₂.x23
  by_cases hz : N s₀ - k = 0
  · refine WP.ite true (by rw [ev]; simp [hz]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    have : k = N s₀ := by omega_using [hk, hz]
    exact this ▸ h₂
  · exact WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h) fun _ =>
      loop_ok hb hp (by omega_using [hz]) h₂

theorem batched_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one) {s₀ : State}
    (h0 : (modeAArch64 M).pre s₀) :
    WP isa (batched group one) s₀ fun s' => GprAbi s₀ s' ∧ (modeAArch64 M).post s₀ s' :=
  ends_wp h0 fun hp _ _ h => groups_wp hg hb hp h

/-! ## Constant time -/

/-- One run of `group` from `k` blocks is constant time. -/
def GroupCt (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modeAArch64 M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) group fun _ _ => True

/-- What is known between the code before the call of a group and the call,
on the four blocks at `D`. -/
structure Mid4 (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre4 s (W s₀) D (S s₀) (R s₀)
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = blk s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  sp : s.sp = s₀.sp

theorem Mid4.of {s₀ : State} {k : Nat} {D : Addr} {s s₁ : State} {M : Mode} (h : LInv M s₀ k s)
    (pre : CallPre4 s₁ (W s₀) D (S s₀) (R s₀)) (saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r)
    (sp : s₁.sp = s.sp) : Mid4 s₀ k D s₁ :=
  ⟨pre, by rw [saved .x21 (by simp [preserved]), h.x21], by rw [saved .x22 (by simp [preserved]), h.x22],
    by rw [saved .x23 (by simp [preserved]), h.x23], by rw [saved .x24 (by simp [preserved]), h.x24],
    by rw [sp, h.sp]⟩

theorem After.of4 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {D : Addr}
    {s s' : State} (h : Mid4 s₀ k D s) (hc : CallPost4 f s (W s₀) D (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .x21 (by simp [preserved]) (by decide), h.x21],
    by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.x23],
    by rw [hc.saved .x24 (by simp [preserved]) (by decide), h.x24], by rw [hc.sp, h.sp]⟩

/-- A group: code before the call (`pre`), the call of `b` on the four blocks
at `D s₀ k` (public), and code after it (`post`), constant time when `pre`'s
addresses and branches depend only on the registers the invariant pins and
`post`'s on `x21` to `x24`. -/
theorem group_ct {M : Mode} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (modeAArch64 M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    {b : Impl.Aes.AArch64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 4 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s (Mid4 s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeAArch64 M).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint)
    (P := fun s₁ s₂ => k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := Mid4 s₀ k (D s₀ k)) (F₂ := Mid4 s₀' k (D s₀' k)) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel4 ok ct (P := fun s₁ s₂ => Mid4 s₀ k (D s₀ k) s₁ ∧ Mid4 s₀' k (D s₀' k) s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call4 ok nf h.1.pre) fun _ hc => After.of4 h.1 hc,
       WP.mono (blk_call4 ok nf h.2.pre) fun _ hc => After.of4 h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x21, h.2.x21, pub_Iv hq]
      · rw [h.1.x22, h.2.x22, pub_blk hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]
      · rw [h.1.x24, h.2.x24, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-- The loop's relation, with the number of iterations left. -/
def GRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k + 4 ≤ N s₀ ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂

/-- Both runs after `k` blocks, with fewer than four left. -/
def GDone (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k s₁ ∧ LInv M s₀' k s₂

theorem groupLoop_ct {M : Mode} {group : Prog isa} (hg : GroupOk M group) (hc : GroupCt M group)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeAArch64 M).pub s₀ s₀') (n : Nat) :
    RelCT isa (GRel M s₀ s₀' n) (.loop group (.zero .x .x9)) (GDone M s₀ s₀') := by
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
    (F₁ := fun (s' : State) => LInv M s₀ (k + 4) s' ∧ Few s₀ (k + 4) s')
    (F₂ := fun (s' : State) => LInv M s₀' (k + 4) s' ∧ Few s₀' (k + 4) s')
    fun _ _ h => ⟨hg hp h.1 h.2.1, hg hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ => ?_
  have e₁ := eval_few_zero c₁
  have e₂ := eval_few_zero c₂
  rw [← hN] at e₂
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have : N s₀ - (k + 4) < 4 := by simpa using hf
    exact ⟨k + 4, hk, this, l₁, l₂⟩
  · rw [e₁] at ht
    have : ¬ N s₀ - (k + 4) < 4 := by simpa using ht
    exact ⟨N s₀ - (k + 4), by omega_using [hk], k + 4, rfl, by omega_using [this], l₁, l₂⟩

theorem groups_rel {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeAArch64 M).pub s₀ s₀') :
    RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) (groups group one)
      fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b := by
  have hN := pub_N hq
  have hbd : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hfew⟩ : ∃ h, (taint.check (Taint.ofRegs [.x23]) (.block few) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  -- `x9`, whether fewer than four blocks are left.
  have fw := (RelCT.taint (A := taint) (P := fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.x23, h.2.x23, hN]) hfew).wp
    (F₁ := fun (s : State) => LInv M s₀ 0 s ∧ Few s₀ 0 s)
    (F₂ := fun (s : State) => LInv M s₀' 0 s ∧ Few s₀' 0 s)
    fun a b h => ⟨few_wp hp h.1, few_wp hp' h.2⟩
  -- The groups, if at least four blocks.
  have loop : RelCT isa (fun a b => (LInv M s₀ 0 a ∧ Few s₀ 0 a) ∧ (LInv M s₀' 0 b ∧ Few s₀' 0 b))
      (.ite (.nonzero .x .x9) (.block []) (.loop group (.zero .x .x9))) (GDone M s₀ s₀') := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · rw [eval_few_nonzero h.1.2, eval_few_nonzero h.2.2, hN]
    · have nil' := (RelCT.taint (A := taint)
        (P := fun a b => ((LInv M s₀ 0 a ∧ Few s₀ 0 a) ∧ (LInv M s₀' 0 b ∧ Few s₀' 0 b)) ∧
          isa.eval (.nonzero .x .x9) a = some true) _
        (fun a b h => agree_of (by rw [h.1.1.1.sp, h.1.2.1.sp, pub_sp hq]) fun r hr => by simp at hr) hnil).wp
        (F₁ := fun a => LInv M s₀ 0 a ∧ N s₀ - 0 < 4) (F₂ := LInv M s₀' 0) fun a b h =>
          ⟨WP.block_nil ⟨h.1.1.1, by
            have := h.2; rw [eval_few_nonzero h.1.1.2] at this; simpa using this⟩,
           WP.block_nil h.1.2.1⟩
      exact nil'.mono (fun _ _ h => h) fun _ _ h => ⟨0, Nat.zero_le _, h.2.1.2, h.2.1.1, h.2.2⟩
    · exact (groupLoop_ct hg hgc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, by
        have := h.2; rw [eval_few_nonzero h.1.1.2] at this
        have : ¬ (N s₀ - 0 < 4) := by simpa using this
        omega_using [this], h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  -- The blocks left, one at a time.
  have tail : RelCT isa (GDone M s₀ s₀')
      (.ite (.zero .x .x23) (.block []) (.loop one (.nonzero .x .x23)))
      fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b := by
    refine (RelCT.exists_ fun k => ?_).mono (fun a b (h : GDone M s₀ s₀' a b) => h) fun _ _ h => h
    by_cases hk : k ≤ N s₀
    swap
    · exact RelCT.of_false fun _ _ h => hk h.1
    have ev {s : State} (h : LInv M s₀ k s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ - k = 0)) :=
      eval_zero_x23 (by omega_using [hbd]) h.x23
    have ev' {s : State} (h : LInv M s₀' k s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ - k = 0)) :=
      eval_zero_x23 (by omega_using [hbd]) (by rw [h.x23, ← hN])
    refine RelCT.ite (fun a b h => by rw [ev h.2.2.1, ev' h.2.2.2]) ?_ ?_
    · have nil' := (RelCT.taint (A := taint)
        (P := fun a b => (k ≤ N s₀ ∧ N s₀ - k < 4 ∧ LInv M s₀ k a ∧ LInv M s₀' k b) ∧
          isa.eval (.zero .x .x23) a = some true) _
        (fun a b h => agree_of (by rw [h.1.2.2.1.sp, h.1.2.2.2.sp, pub_sp hq]) fun r hr => by simp at hr)
        hnil).wp
        (F₁ := LInv M s₀ (N s₀)) (F₂ := LInv M s₀' (N s₀')) fun a b h => by
          have e : k = N s₀ := by
            have := h.2; rw [ev h.1.2.2.1] at this
            have : N s₀ - k = 0 := by simpa using this
            omega_using [hk, this]
          exact ⟨WP.block_nil (e ▸ h.1.2.2.1), WP.block_nil (by rw [← hN, ← e]; exact h.1.2.2.2)⟩
      exact nil'.mono (fun _ _ h => h) fun _ _ h => h.2
    · exact (loop_ct hb hbc hp hp' hq (N s₀ - k)).mono (fun a b h => ⟨k, rfl, by
        have := h.2; rw [ev h.1.2.2.1] at this
        have : ¬ (N s₀ - k = 0) := by simpa using this
        omega_using [this], h.1.2.2.1, h.1.2.2.2⟩) fun _ _ h => h
  exact (fw.mono (fun _ _ h => h) fun _ _ h => h.2).seq (loop.seq tail)

theorem batched_ct {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one) :
    ConstantTime isa (modeAArch64 M).pre (modeAArch64 M).pub (batched group one) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' _ => groups_rel hg hgc hb hbc hp hp' hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## CBC decryption: the pieces of the group -/

/-- Closes the disjointness goals between the regions of a group. -/
macro "cbc_gd" : tactic => `(tactic| first
  | with_reducible exact UPre.dBB ‹_› ‹_› (by omega) (by omega) (by omega)
  | with_reducible exact UPre.dBT ‹_› ‹_› (by omega) (by omega)
  | with_reducible exact (UPre.dBT ‹_› ‹_› (by omega) (by omega)).symm
  | with_reducible exact UPre.dBV ‹_› ‹_› (by omega)
  | with_reducible exact (UPre.dBV ‹_› ‹_› (by omega)).symm
  | with_reducible exact UPre.dTT (by omega) (by omega) (by omega)
  | with_reducible exact UPre.dTV (by omega)
  | with_reducible exact (UPre.dTV (by omega)).symm
  | with_reducible exact UPre.dBI ‹_› ‹_› (by omega)
  | with_reducible exact (UPre.dBI ‹_› ‹_› (by omega)).symm
  | with_reducible exact UPre.dTI ‹_› (by omega)
  | with_reducible exact (UPre.dTI ‹_› (by omega)).symm
  | with_reducible exact UPre.iv_sv ‹_›
  | with_reducible exact (UPre.iv_sv ‹_›).symm)

section
variable {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
include hp hk

/-- Block `j` saved in slot `j`. -/
theorem UPre.saveAt_ok {j : Nat} (hj : j < 3) {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (saveAt j) t = some t' ∧ (∀ r, r ≠ .x9 → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧
      t'.mem = copyMem t.mem (sl s₀ j) (blk s₀ (k + j)) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .x24) (src := .x22) (d := gOff + 16 * j) (e := 16 * j)
    (by rw [x24]) (by rw [x24, sl8]) (by rw [x22, UPre.blk_add]) (by rw [x22, UPre.blk_add8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega_using [hk, hj])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega_using [hk, hj])))
    (by rw [hW]; exact in_rw (by simp) (cSl s₀ hj)) (by rw [hW]; exact in_rw (by simp) (cSl8 s₀ hj))
    (by decide) (by decide) (by simp only [gOff]; omega_using [hj]) (by simp only [gOff]; omega_using [hj])
    (by omega_using [hj]) (by omega_using [hj])

/-- Block 3 saved where a single block's is. -/
theorem UPre.saveLast_ok {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (copy .x24 cOff .x22 48) t = some t' ∧ (∀ r, r ≠ .x9 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = copyMem t.mem (Sv s₀) (blk s₀ (k + 3)) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .x24) (src := .x22) (d := cOff) (e := 48)
    (by rw [x24]; rfl) (by rw [x24]; exact sv8 _)
    (by rw [x22]; exact UPre.blk_add (j := 3)) (by rw [x22]; exact UPre.blk_add8 (j := 3))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + 3) (by omega_using [hk])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + 3) (by omega_using [hk])))
    (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Block 0 XORed with the chaining value. -/
theorem UPre.xor0_ok {t : State} (x21 : t.gpr .x21 = Iv s₀) (x22 : t.gpr .x22 = blk s₀ k)
    (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa xorInto t = some t' ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = xorMem t.mem (blk s₀ (k + 0)) (Iv s₀) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact xorInto_ok t (P := blk s₀ (k + 0)) (Q := Iv s₀) x22 x21
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + 0) (by omega_using [hk])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + 0) (by omega_using [hk])))
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + 0) (by omega_using [hk])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + 0) (by omega_using [hk])))

/-- Block `j + 1` XORed with slot `j`. -/
theorem UPre.fixAt_ok {j : Nat} (hj : j < 3) {t : State} (x22 : t.gpr .x22 = blk s₀ k)
    (x24 : t.gpr .x24 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (fixAt j) t = some t' ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = xorMem t.mem (blk s₀ (k + (j + 1))) (sl s₀ j) ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact xorAt_ok t (dst := .x22) (src := .x24) (d := 16 * (j + 1)) (e := gOff + 16 * j)
    (by rw [x22, UPre.blk_add]) (by rw [x22, UPre.blk_add8]) (by rw [x24]) (by rw [x24, sl8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by rw [hR]; exact in_rw (by simp) (cSl s₀ hj)) (by rw [hR]; exact in_rw (by simp) (cSl8 s₀ hj))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + (j + 1)) (by omega_using [hk, hj])))
    (by decide) (by decide) (by decide) (by decide)
    (by omega_using [hj]) (by omega_using [hj]) (by simp only [gOff]; omega_using [hj])
    (by simp only [gOff]; omega_using [hj])

omit hk in
/-- The saved block 3 copied to the chaining value. -/
theorem UPre.last_ok {t : State} (x21 : t.gpr .x21 = Iv s₀) (x24 : t.gpr .x24 = S s₀)
    (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (copy .x21 0 .x24 cOff) t = some t' ∧ (∀ r, r ≠ .x9 → t'.gpr r = t.gpr r) ∧
      t'.sp = t.sp ∧ t'.mem = copyMem t.mem (Iv s₀) (Sv s₀) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .x21) (src := .x24) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
    (by rw [x21]; simp) (by rw [x21]) (by rw [x24]; rfl) (by rw [x24]; exact sv8 _)
    (by rw [hR]; exact in_rw (by simp) cSv0) (by rw [hR]; exact in_rw (by simp) cSv8)
    (by rw [hW]; exact in_rw (by simp) cIv0) (by rw [hW]; exact in_rw (by simp) cIv8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end

/-! ## CBC decryption: before the call -/

/-- What the code before the call leaves. -/
structure DecA4 (s₀ : State) (k : Nat) (s t : State) : Prop where
  pre : CallPre4 t (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨S s₀, 2064⟩, gR s₀] s.mem t.mem
  slot : ∀ j < 3, bytesAt t.mem (sl s₀ j) 16 = bytesAt s.mem (blk s₀ (k + j)) 16
  last : bytesAt t.mem (Sv s₀) 16 = bytesAt s.mem (blk s₀ (k + 3)) 16

theorem decA4_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block (decSave ++ callArgs4)) s (DecA4 s₀ k s) := by
  obtain ⟨t₁, run₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := hp.saveAt_ok hk (j := 0) (by decide) h.x22 h.x24 h.rd h.wr
  obtain ⟨t₂, run₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := hp.saveAt_ok hk (j := 1) (by decide)
    (by rw [g₁ _ (by decide), h.x22]) (by rw [g₁ _ (by decide), h.x24]) (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  obtain ⟨t₃, run₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := hp.saveAt_ok hk (j := 2) (by decide)
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h.x22]) (by rw [g₂ _ (by decide), g₁ _ (by decide), h.x24])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr])
  obtain ⟨t₄, run₄, g₄, sp₄, m₄, rd₄, wr₄⟩ := hp.saveLast_ok hk
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.x22])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.x24])
    (by rw [rd₃, rd₂, rd₁, h.rd]) (by rw [wr₃, wr₂, wr₁, h.wr])
  obtain ⟨t₅, run₅, x0₅, x1₅, x2₅, x3₅, x4₅, cs₅, sp₅, mem₅, rd₅, wr₅⟩ := callArgs4_ok t₄
  have g (r : Reg) (hr : r ≠ .x9) : t₄.gpr r = s.gpr r := by
    rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  have rd₄' : t₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : t₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  show WP isa (.block (saveAt 0 ++ saveAt 1 ++ saveAt 2 ++ copy .x24 cOff .x22 48 ++ callArgs4)) s _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, WP.of_runBlock ⟨t₂, run₂, WP.of_runBlock ⟨t₃, run₃,
    WP.of_runBlock ⟨t₄, run₄, WP.of_runBlock ⟨t₅, run₅, ?_⟩⟩⟩⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : t₅.gpr r = s.gpr r := by
    rw [cs₅ r hr, g r (preserved_ne hr).1]
  refine ⟨hp.callPre4 hk (by rw [x0₅, g _ (by decide), h.x19]) (by rw [x1₅, g _ (by decide), h.x20])
    (by rw [x2₅, g _ (by decide), h.x22]) x3₅ (by rw [x4₅, g _ (by decide), h.x24])
    (by rw [rd₅, rd₄', h.rd]) (by rw [wr₅, wr₄', h.wr]),
    keep, by rw [sp₅, sp₄, sp₃, sp₂, sp₁], by rw [rd₅, rd₄'], by rw [wr₅, wr₄'], ?_, fun j hj => ?_, ?_⟩
  · rw [mem₅, m₄, m₃, m₂, m₁]
    exact (copyMem_frameG _ (j := 0) (by decide) _).trans ((copyMem_frameG _ (j := 1) (by decide) _).trans
      ((copyMem_frameG _ (j := 2) (by decide) _).trans (copyMem_frameV _ _)))
  · rw [mem₅]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [m₄, copyMem_other, m₃, copyMem_other, m₂, copyMem_other, m₁, copyMem_bytes] <;> cbc_gd
    · rw [m₄, copyMem_other, m₃, copyMem_other, m₂, copyMem_bytes, m₁, copyMem_other] <;> cbc_gd
    · rw [m₄, copyMem_other, m₃, copyMem_bytes, m₂, copyMem_other, m₁, copyMem_other] <;> cbc_gd
  · rw [mem₅, m₄, copyMem_bytes, m₃, copyMem_other, m₂, copyMem_other, m₁, copyMem_other] <;> cbc_gd

/-! ## CBC decryption: the group -/

theorem decGroup_ok (v : BlocksImpl) : GroupOk (cbcMode false) (decGroup v.dec) := by
  intro s₀ hp k hk s h
  have len : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  refine WP.seq (WP.mono (decA4_wp hp hk h) fun t₅ a => ?_)
  refine WP.seq (WP.mono (blk_call4 v.decOk v.decNoFrames a.pre) fun t₆ c => ?_)
  have g₆ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : t₆.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have rd₆ : t₆.rd = s₀.rd := by rw [c.rd, a.rd, h.rd]
  have wr₆ : t₆.wr = s₀.wr := by rw [c.wr, a.wr, h.wr]
  have x21₆ : t₆.gpr .x21 = Iv s₀ := by rw [g₆ _ (by simp [preserved]) (by decide), h.x21]
  have x22₆ : t₆.gpr .x22 = blk s₀ k := by rw [g₆ _ (by simp [preserved]) (by decide), h.x22]
  have x24₆ : t₆.gpr .x24 = S s₀ := by rw [g₆ _ (by simp [preserved]) (by decide), h.x24]
  obtain ⟨t₇, run₇, g₇, sp₇, m₇, rd₇, wr₇⟩ := hp.xor0_ok hk x21₆ x22₆ rd₆ wr₆
  obtain ⟨t₈, run₈, g₈, sp₈, m₈, rd₈, wr₈⟩ := hp.fixAt_ok hk (j := 0) (by decide)
    (by rw [g₇ _ (by decide) (by decide), x22₆]) (by rw [g₇ _ (by decide) (by decide), x24₆])
    (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆])
  obtain ⟨t₉, run₉, g₉, sp₉, m₉, rd₉, wr₉⟩ := hp.fixAt_ok hk (j := 1) (by decide)
    (by rw [g₈ _ (by decide) (by decide), g₇ _ (by decide) (by decide), x22₆])
    (by rw [g₈ _ (by decide) (by decide), g₇ _ (by decide) (by decide), x24₆])
    (by rw [rd₈, rd₇, rd₆]) (by rw [wr₈, wr₇, wr₆])
  obtain ⟨t₁₀, run₁₀, g₁₀, sp₁₀, m₁₀, rd₁₀, wr₁₀⟩ := hp.fixAt_ok hk (j := 2) (by decide)
    (by rw [g₉ _ (by decide) (by decide), g₈ _ (by decide) (by decide), g₇ _ (by decide) (by decide), x22₆])
    (by rw [g₉ _ (by decide) (by decide), g₈ _ (by decide) (by decide), g₇ _ (by decide) (by decide), x24₆])
    (by rw [rd₉, rd₈, rd₇, rd₆]) (by rw [wr₉, wr₈, wr₇, wr₆])
  have g₁₀' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) : t₁₀.gpr r = t₆.gpr r := by
    rw [g₁₀ r h9 h10, g₉ r h9 h10, g₈ r h9 h10, g₇ r h9 h10]
  obtain ⟨t₁₁, run₁₁, g₁₁, sp₁₁, m₁₁, rd₁₁, wr₁₁⟩ := hp.last_ok
    (by rw [g₁₀' _ (by decide) (by decide), x21₆]) (by rw [g₁₀' _ (by decide) (by decide), x24₆])
    (by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆]) (by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆])
  obtain ⟨t₁₂, run₁₂, x22₁₂, x23₁₂, few₁₂, keep₁₂, sp₁₂, m₁₂, rd₁₂, wr₁₂⟩ := advance4_regs hp (s := t₁₁) hk
    (by rw [g₁₁ _ (by decide), g₁₀' _ (by decide) (by decide), x22₆])
    (by rw [g₁₁ _ (by decide), g₁₀' _ (by decide) (by decide), g₆ _ (by simp [preserved]) (by decide), h.x23])
  show WP isa (.block (xorInto ++ fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ copy .x21 0 .x24 cOff ++ advance4)) t₆ _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.of_runBlock ⟨t₇, run₇, WP.of_runBlock ⟨t₈, run₈, WP.of_runBlock ⟨t₉, run₉,
    WP.of_runBlock ⟨t₁₀, run₁₀, WP.of_runBlock ⟨t₁₁, run₁₁, WP.of_runBlock ⟨t₁₂, run₁₂, ?_⟩⟩⟩⟩⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      t₁₂.gpr r = s.gpr r := by
    rw [keep₁₂ r h22 h23 (preserved_ne hr).1, g₁₁ r (preserved_ne hr).1,
      g₁₀' r (preserved_ne hr).1 (preserved_ne hr).2, g₆ r hr h30]
  -- Memory.
  have fAll : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀] s.mem t₁₂.mem := by
    rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇]
    refine (a.frame.sub ?_).trans ((c.frame.sub ?_).trans (((xorMem_frameB _ (by decide) _).sub ?_).trans
      (((xorMem_frameB _ (by decide) _).sub ?_).trans (((xorMem_frameB _ (by decide) _).sub ?_).trans
        (((xorMem_frameB _ (by decide) _).sub ?_).trans ((copyMem_frame _ _ _).sub ?_))))))
    all_goals intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
      · exact ⟨gR s₀, by simp, fun _ h => h⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    all_goals subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₄ : Frame (Big s₀) s₀.mem t₅.mem :=
    (UPre.big_of h.frame).trans (UPre.bigStep (a.frame.sub (all_cons ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
      (all_cons ⟨gR s₀, by simp, fun _ h => h⟩ all_nil))))
  have hb (j : Nat) (hj : j < 4) :
      bytesAt s.mem (blk s₀ (k + j)) 16 = (blks s₀)[k + j]'(by rw [len]; omega_using [hk, hj]) :=
    h.blockAt (by omega_using []) (by omega_using [hk, hj])
  -- The blocks after the call, and the slots and chaining value it left.
  have d (j : Nat) (hj : j < 4) : bytesAt t₆.mem (blk s₀ (k + j)) 16 =
      Spec.Cbc.aesInvWith (R s₀) (wK s₀) ((blks s₀)[k + j]'(by rw [len]; omega_using [hk, hj])) := by
    have := c.out j hj
    rw [UPre.blk_add] at this
    rw [this, ← aesInvWith_state, UPre.sched_bytes hp big₄,
      Proof.Cmac.bytesAt_frame a.frame (all_cons (hp.dBS hk hj) (all_cons (hp.dBG hk hj) all_nil)) (by decide),
      hb j hj]
  have sv (j : Nat) (hj : j < 3) :
      bytesAt t₆.mem (sl s₀ j) 16 = (blks s₀)[k + j]'(by rw [len]; omega_using [hk, hj]) := by
    rw [Proof.Cmac.bytesAt_frame c.frame (all_cons (hp.dT64 hk hj) (all_cons (hp.dTS hj) all_nil)) (by decide),
      a.slot j hj, hb j (by omega_using [hj])]
  have svL : bytesAt t₆.mem (Sv s₀) 16 = (blks s₀)[k + 3]'(by rw [len]; omega_using [hk]) := by
    rw [Proof.Cmac.bytesAt_frame c.frame (all_cons (hp.dV64 hk) (all_cons hp.sv_scr all_nil)) (by decide),
      a.last, hb 3 (by decide)]
  have iv₆ : bytesAt t₆.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame c.frame (all_cons (hp.dI64 hk) (all_cons hp.dIS all_nil)) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (all_cons hp.dIS' (all_cons hp.dIG all_nil)) (by decide), h.iv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false]
  -- The blocks and the chaining value after the group.
  have o0 : bytesAt t₁₂.mem (blk s₀ (k + 0)) 16 = Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (wK s₀)
      ((blks s₀)[k + 0]'(by rw [len]; omega_using [hk]))) (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [m₁₂, m₁₁, copyMem_other, m₁₀, xorMem_other, m₉, xorMem_other, m₈, xorMem_other, m₇, xorMem_bytes,
      d 0 (by decide), iv₆] <;> cbc_gd
  have o1 : bytesAt t₁₂.mem (blk s₀ (k + 1)) 16 = Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (wK s₀)
      ((blks s₀)[k + 1]'(by rw [len]; omega_using [hk]))) ((blks s₀)[k + 0]'(by rw [len]; omega_using [hk])) := by
    rw [m₁₂, m₁₁, copyMem_other, m₁₀, xorMem_other, m₉, xorMem_other, m₈, xorMem_bytes, m₇, xorMem_other,
      xorMem_other, d 1 (by decide), sv 0 (by decide)] <;> cbc_gd
  have o2 : bytesAt t₁₂.mem (blk s₀ (k + 2)) 16 = Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (wK s₀)
      ((blks s₀)[k + 2]'(by rw [len]; omega_using [hk]))) ((blks s₀)[k + 1]'(by rw [len]; omega_using [hk])) := by
    rw [m₁₂, m₁₁, copyMem_other, m₁₀, xorMem_other, m₉, xorMem_bytes, m₈, xorMem_other, xorMem_other, m₇,
      xorMem_other, xorMem_other, d 2 (by decide), sv 1 (by decide)] <;> cbc_gd
  have o3 : bytesAt t₁₂.mem (blk s₀ (k + 3)) 16 = Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (wK s₀)
      ((blks s₀)[k + 3]'(by rw [len]; omega_using [hk]))) ((blks s₀)[k + 2]'(by rw [len]; omega_using [hk])) := by
    rw [m₁₂, m₁₁, copyMem_other, m₁₀, xorMem_bytes, m₉, xorMem_other, xorMem_other, m₈, xorMem_other,
      xorMem_other, m₇, xorMem_other, xorMem_other, d 3 (by decide), sv 2 (by decide)] <;> cbc_gd
  have ivF : bytesAt t₁₂.mem (Iv s₀) 16 = (blks s₀)[k + 3]'(by rw [len]; omega_using [hk]) := by
    rw [m₁₂, m₁₁, copyMem_bytes, m₁₀, xorMem_other, m₉, xorMem_other, m₈, xorMem_other, m₇, xorMem_other,
      svL] <;> cbc_gd
  -- The mode.
  have take4 : (blks s₀).take (k + 4) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega_using [hk])] ++
      [(blks s₀)[k + 1]'(by rw [len]; omega_using [hk])] ++ [(blks s₀)[k + 2]'(by rw [len]; omega_using [hk])] ++
      [(blks s₀)[k + 3]'(by rw [len]; omega_using [hk])] := by
    have t₀ : (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₁ : (blks s₀).take (k + 2) = (blks s₀).take (k + 1) ++ [(blks s₀)[k + 1]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₂ : (blks s₀).take (k + 3) = (blks s₀).take (k + 2) ++ [(blks s₀)[k + 2]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    have t₃ : (blks s₀).take (k + 4) = (blks s₀).take (k + 3) ++ [(blks s₀)[k + 3]'(by rw [len]; omega_using [hk])] :=
      take_succ_blks s₀ (by omega_using [hk])
    rw [t₃, t₂, t₁, t₀]
  have hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega_using [hk]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨⟨x19', x20', x21', x22₁₂, x23₁₂, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩, few₁₂⟩
  · rw [sp₁₂, sp₁₁, sp₁₀, sp₉, sp₈, sp₇, c.sp, a.sp, h.sp]
  · rw [rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆]
  · rw [wr₁₂, wr₁₁, wr₁₀, wr₉, wr₈, wr₇, wr₆]
  · exact h.frame.trans (stepFrame4 hk fAll)
  · rw [hp.blocksAt_step4 hk fAll h.data hl, o0, o1, o2, o3]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false]
    rw [take4, decrypt_snoc, decrypt_snoc, decrypt_snoc, decrypt_snoc, next_snoc, next_snoc, next_snoc]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [ivF]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take4, next_snoc]

/-! ## CBC decryption: constant time -/

theorem decGroupPre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block (decSave ++ callArgs4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroupPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block (decFix ++ advance4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_ct (v : BlocksImpl) : GroupCt (cbcMode false) (decGroup v.dec) :=
  fun hp hp' hq k => group_ct (fun hq k => pub_blk hq k) v.decOk v.decCt v.decNoFrames
    decGroupPre_taint decGroupPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA4_wp hp hk h) fun _ a => Mid4.of h a.pre a.saved a.sp) hp hp' hq k

end VG.Proof.AesCbc.AArch64
