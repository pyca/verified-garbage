module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CBC on PPC64LE: groups of eight blocks

The modes whose blocks can be ciphered independently (CBC and CFB128
decryption, XTS) take eight blocks at a time while at least eight are left,
by one call of the block function each, which runs its eight-block loop, and
the rest one at a time (`Impl.AesCbc.PPC64LE.groups`).

* `blk_call8`, `blk_rel8`: a call of a block function on eight blocks `D`
  in place, from the blocks functions' contract with their frame
  (`Proof.Aes.PPC64LE.blocksFramed`): only `D` changes, so the scratch
  buffer, which a group's slots are in, does not.
* `xorAt_wp`: the block at an offset of a register XORed into another.
* `saveSlots_wp`, `fixSlots_wp`: slot 0 the chaining value and slot `j + 1`
  block `k + j`; and each of the eight blocks XORed with its slot.
* `group_step`: the invariant (`LInv`) after `k + 8` blocks, from the eight
  blocks a group wrote, for a mode that extends its output one block at a
  time by a function of the block and the chaining value (`Steps`).
* `groups_wp`: if one run of `group` takes the invariant from `k` blocks to
  `k + 8` (`GroupOk`), and `one` takes it from `k` to `k + 1` (`BodyOk`),
  `groups` takes it from no blocks to all of them; `batched_wp`, the whole
  function.
* `group_ct`, `groups_rel`, `batched_ct`: the same for constant time.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

/-! ## A call of a block function on eight blocks -/

theorem eight_toNat : (BitVec.ofNat 64 8).toNat = 8 := rfl

/-- What a call of a block function on eight blocks needs. -/
structure CallPre8 (s : State) (W D S : Addr) (R : Nat) : Prop where
  r3 : s.gpr .r3 = W
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 8
  r7 : s.gpr .r7 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 128⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 128⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 128 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 128⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 128⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on eight blocks leaves. -/
structure CallPost8 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 128⟩] s.mem s'.mem
  out : ∀ j < 8, bytesAt s'.mem (D + BitVec.ofNat 64 (16 * j)) 16 =
    (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * j)))).toList

theorem CallPre8.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre8 s W D S R) :
    (Proof.Aes.PPC64LE.blocksFramed f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 128⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.PPC64LE.blocksFramed, Proof.Aes.blocksPPC64LE, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, hR, eight_toNat, Nat.reduceMul]
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

theorem blk_call8 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.PPC64LE.blocksFramed f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.PPC64LE.blocksFramed f).post s s')
    (nf : c.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre8 s W D S R) :
    WP isa (.call name c) s (CallPost8 f s W D R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.PPC64LE.blocksFramed f) ok (rd := [⟨W, 240⟩]) (wr := [⟨D, 128⟩, ⟨S, 2048⟩])
    h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp _ hcs _ ⟨hpost, hfr⟩
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, hR, eight_toNat] at hpost hfr
  exact ⟨hrd, hwr, hsp, hcs, hfr, fun j hj => bytesAt_of_statesAt_n hpost hj⟩

/-- Calls of a block function on eight blocks, with the same arguments in
both runs, are constant time. -/
theorem blk_rel8 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    {P : State → State → Prop} {W D S : Addr} {R : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre8 s₁ W D S R ∧ CallPre8 s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 128⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre (f := f), h₂.blk_pre (f := f), ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The straight-line pieces -/

/-- The block at `Q` (at `src + e`) XORed into the block at `P` (at `dst + d`). -/
theorem xorAt_wp {dst src : Reg} {d e : Nat} {s : State} {P Q : Addr} {rest : List Instr}
    {Φ : State → Prop} (hd : dst ≠ .r0) (hs : src ≠ .r0) (hd9 : dst ≠ .r9) (hd10 : dst ≠ .r10)
    (hs9 : src ≠ .r9) (hs10 : src ≠ .r10)
    (hdo : d + 8 < 2 ^ 15 ∧ d % 8 = 0) (heo : e + 8 < 2 ^ 15 ∧ e % 8 = 0)
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = xorMem s.mem P Q →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (xorAt dst d src e ++ rest)) s Φ := by
  simp only [xorAt, List.cons_append, List.nil_append]
  refine wp_ld hd ⟨by omega, by omega⟩ hp rp fun s₁ u₁ => ?_
  refine wp_ld hs ⟨by omega, by omega⟩ (by rw [u₁.other _ hs9, hq])
    (by rw [u₁.rd, u₁.wr]; exact rq) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_std hd ⟨by omega, by omega⟩
    (by rw [u₃.other _ hd9, u₂.other _ hd10, u₁.other _ hd9, hp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wp) fun s₄ u₄ => ?_
  have g₄ (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) : s₄.gpr r = s.gpr r := by
    rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  refine wp_ld hd ⟨by omega, by omega⟩ (by rw [g₄ _ hd9 hd10, hp8])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rp8) fun s₅ u₅ => ?_
  refine wp_ld hs ⟨by omega, by omega⟩ (by rw [u₅.other _ hs9, g₄ _ hs9 hs10, hq8])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rq8)
    fun s₆ u₆ => ?_
  refine wp_xor fun s₇ u₇ => ?_
  refine wp_std hd ⟨by omega, by omega⟩
    (by rw [u₇.other _ hd9, u₆.other _ hd10, u₅.other _ hd9, g₄ _ hd9 hd10, hp8])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact wp8) fun s₈ u₈ => ?_
  refine k s₈ (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₈.gpr, u₇.other _ h9, u₆.other _ h10, u₅.other _ h9, g₄ _ h9 h10]
  · rw [u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.other _ (by decide), u₆.mem, u₅.gpr, u₅.mem, u₄.mem,
      u₃.gpr, u₃.mem, u₂.gpr, u₂.other _ (by decide), u₂.mem, u₁.gpr, u₁.mem]
    rfl
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The invariant after a group -/

/-- Block `i` on entry, or none past the end. -/
abbrev blkOf (s₀ : State) (i : Nat) : List Byte := (blks s₀).getD i []

/-- A mode that extends its output one block at a time, by `F R w x c` of
the block `x` and the chaining value `c` before it. -/
def Steps (M : Mode) (F : Nat → List Byte → List Byte → List Byte → List Byte) : Prop :=
  ∀ R w iv xs x, M.out R w iv (xs ++ [x]) = M.out R w iv xs ++ [F R w x (M.chain R w iv xs)]

theorem getElem?_blks {s₀ : State} {i : Nat} (hi : i < N s₀) : (blks s₀)[i]? = some (blkOf s₀ i) := by
  rw [blkOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hi)]
  rfl

theorem take_succ_blkOf (s₀ : State) {i : Nat} (hi : i < N s₀) :
    (blks s₀).take (i + 1) = (blks s₀).take i ++ [blkOf s₀ i] := by
  rw [List.take_add_one, getElem?_blks hi]
  rfl

theorem length_outK (M : Mode) (s₀ : State) {i : Nat} (hi : i ≤ N s₀) : (outK M s₀ i).length = i := by
  rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega

theorem outK_succ {M : Mode} {F : Nat → List Byte → List Byte → List Byte → List Byte} (hF : Steps M F)
    (s₀ : State) {i : Nat} (hi : i < N s₀) :
    outK M s₀ (i + 1) = outK M s₀ i ++ [F (R s₀) (wK s₀) (blkOf s₀ i) (chainK M s₀ i)] := by
  rw [outK, take_succ_blkOf s₀ hi, hF]

/-- Block `i` of the mode's output. -/
theorem outK_get {M : Mode} {F : Nat → List Byte → List Byte → List Byte → List Byte} (hF : Steps M F)
    (s₀ : State) {n i : Nat} (hn : n ≤ N s₀) (hi : i < n) :
    (outK M s₀ n)[i]? = some (F (R s₀) (wK s₀) (blkOf s₀ i) (chainK M s₀ i)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [outK_succ hF s₀ (by omega)]
    by_cases h : i < n
    · rw [List.getElem?_append_left (by rw [length_outK M s₀ (by omega)]; exact h), ih (by omega) h]
    · have : i = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [length_outK M s₀ (by omega)]),
        length_outK M s₀ (by omega), Nat.sub_self]
      rfl

theorem getElem?_blocksAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Cbc.blocksAt m p n)[i]? = some (bytesAt m (p + BitVec.ofNat 64 (16 * i)) 16) := by
  simp [Spec.Cbc.blocksAt, List.getElem?_range hi]

/-- The invariant after `k + 8` blocks, from the invariant after `k`: the
registers, a frame of the eight blocks, the chaining value and the scratch
buffer, and each of the eight blocks the mode's. -/
theorem group_step {M : Mode} {F : Nat → List Byte → List Byte → List Byte → List Byte} (hF : Steps M F)
    {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s t : State} (h : LInv M s₀ k s)
    (r14 : t.gpr .r14 = W s₀) (r15 : t.gpr .r15 = s₀.gpr .r4) (r16 : t.gpr .r16 = Iv s₀)
    (r17 : t.gpr .r17 = blk s₀ (k + 8)) (r18 : t.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + 8)))
    (r19 : t.gpr .r19 = S s₀) (keep : ∀ r ∈ preserved, r ∉ vars → t.gpr r = s.gpr r)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (hf : Frame [⟨blk s₀ k, 128⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem t.mem)
    (hout : ∀ j < 8, bytesAt t.mem (blk s₀ (k + j)) 16 =
      F (R s₀) (wK s₀) (blkOf s₀ (k + j)) (chainK M s₀ (k + j)))
    (hiv : bytesAt t.mem (Iv s₀) 16 = chainK M s₀ (k + 8)) : LInv M s₀ (k + 8) t := by
  have hd := hp.data_wrap
  have hsub : Region.Sub ⟨blk s₀ k, 128⟩ (dataR s₀) := Offset.sub_base _ (by omega)
  refine ⟨r14, r15, r16, r17, r18, r19, fun r hr hv => (keep r hr hv).trans (h.keep r hr hv),
    rd.trans h.rd, wr.trans h.wr, h.frame.trans (hf.sub fun r hr => ?_), ?_, hiv⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, hsub⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
  · have hl : (outK M s₀ k).length = k := length_outK M s₀ (by omega)
    apply List.ext_getElem?
    intro i
    by_cases hi : i < N s₀
    swap
    · rw [List.getElem?_eq_none (by rw [length_blocksAt]; omega), List.getElem?_eq_none (by
        rw [List.length_append, length_outK M s₀ hk, List.length_drop]; simp [Spec.Cbc.blocksAt]; omega)]
    rw [getElem?_blocksAt _ _ hi]
    have hs := congrArg (·[i]?) h.data
    simp only [getElem?_blocksAt _ _ hi] at hs
    by_cases hlo : k + 8 ≤ i
    · -- After the group: unchanged.
      rw [List.getElem?_append_right (by rw [length_outK M s₀ hk]; omega), length_outK M s₀ hk,
        List.getElem?_drop, Nat.add_sub_cancel' hlo]
      rw [List.getElem?_append_right (by omega), hl, List.getElem?_drop, Nat.add_sub_cancel' (by omega)] at hs
      rw [← hs]
      refine congrArg some (bytesAt_frame hf (fun r hr => ?_) (by decide))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact hp.iv_data.symm.sub_left (UPre.data_sub hi)
      · exact (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (Region.sub_prefix (by decide))
    rw [List.getElem?_append_left (by rw [length_outK M s₀ hk]; omega), outK_get hF s₀ hk (by omega)]
    by_cases hlt : i < k
    · -- Before the group: unchanged, and the mode's already.
      rw [List.getElem?_append_left (by omega), outK_get hF s₀ (by omega) hlt] at hs
      rw [← hs]
      refine congrArg some (bytesAt_frame hf (fun r hr => ?_) (by decide))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact hp.iv_data.symm.sub_left (UPre.data_sub hi)
      · exact (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (Region.sub_prefix (by decide))
    · -- In the group.
      have := hout (i - k) (by omega)
      rw [Nat.add_sub_cancel' (by omega)] at this
      exact congrArg some this

/-! ## The slots of a group -/

/-- Slot `j` of a group, in the scratch buffer. -/
abbrev sl (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (slot j)

theorem sl8 (s₀ : State) (j : Nat) :
    S s₀ + BitVec.ofNat 64 (slot j + 8) = sl s₀ j + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]

theorem blk_add (s₀ : State) {k j : Nat} : blk s₀ k + BitVec.ofNat 64 (16 * j) = blk s₀ (k + j) := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j)) (by omega)]

theorem blk_add8 (s₀ : State) {k j : Nat} :
    blk s₀ k + BitVec.ofNat 64 (16 * j + 8) = blk s₀ (k + j) + BitVec.ofNat 64 8 := by
  rw [blk, blk, Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega),
    Offset.add_add_eq _ (c := 16 * (k + j) + 8) (by omega)]

theorem cSl (s₀ : State) {j : Nat} (hj : j ≤ 8) : (scrR s₀).Contains (sl s₀ j) 8 :=
  Offset.contains_base _ (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem cSl8 (s₀ : State) {j : Nat} (hj : j ≤ 8) : (scrR s₀).Contains (sl s₀ j + BitVec.ofNat 64 8) 8 := by
  rw [← sl8]; exact Offset.contains_base _ (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem dSS (s₀ : State) {a b : Nat} (ha : a ≤ 8) (hb : b ≤ 8) (hab : a ≠ b) :
    (⟨sl s₀ a, 16⟩ : Region).Disjoint ⟨sl s₀ b, 16⟩ :=
  Offset.disjoint _ (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem sl_sub (s₀ : State) {j : Nat} (hj : j ≤ 8) : Region.Sub ⟨sl s₀ j, 16⟩ ⟨S s₀, 144⟩ :=
  Offset.sub_base _ (by simp only [slot]; omega)

theorem sl_sub1 (s₀ : State) {j : Nat} (h1 : 1 ≤ j) (hj : j ≤ 8) : Region.Sub ⟨sl s₀ j, 16⟩ ⟨sl s₀ 1, 128⟩ :=
  Offset.sub _ (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem slR_sub (s₀ : State) : Region.Sub ⟨S s₀, 144⟩ ⟨S s₀, 2064⟩ := Region.sub_prefix (by decide)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.dBS {i j : Nat} (hi : i < N s₀) (hj : j ≤ 8) :
    (⟨blk s₀ i, 16⟩ : Region).Disjoint ⟨sl s₀ j, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (UPre.scr_sub (by simp only [slot]; omega))

theorem UPre.dBG {i : Nat} (hi : i < N s₀) : (⟨blk s₀ i, 16⟩ : Region).Disjoint ⟨S s₀, 144⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (Region.sub_prefix (by decide))

theorem UPre.dBG1 {i : Nat} (hi : i < N s₀) : (⟨blk s₀ i, 16⟩ : Region).Disjoint ⟨sl s₀ 1, 128⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hi)).sub_right (UPre.scr_sub (by simp only [slot]; omega))

theorem UPre.dIS {j : Nat} (hj : j ≤ 8) : (ivR s₀).Disjoint ⟨sl s₀ j, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by simp only [slot]; omega))

theorem UPre.dIG : (ivR s₀).Disjoint ⟨S s₀, 144⟩ := hp.iv_scr.sub_right (Region.sub_prefix (by decide))

theorem UPre.dBB {i j : Nat} (hi : i < N s₀) (hj : j < N s₀) (hij : i ≠ j) :
    (⟨blk s₀ i, 16⟩ : Region).Disjoint ⟨blk s₀ j, 16⟩ := hp.blk_disjoint hi hj hij

/-- Block `i`, from blocks `k` to `k + m`. -/
theorem UPre.dB_run {k m i : Nat} (hi : i < N s₀) (h : i < k ∨ k + m ≤ i) (hm : k + m ≤ N s₀) :
    (⟨blk s₀ i, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16 * m⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem UPre.dSB {j k m : Nat} (hj : j ≤ 8) (hm : k + m ≤ N s₀) :
    (⟨sl s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16 * m⟩ :=
  ((hp.data_scr.sub_left (Offset.sub_base _ (by omega))).sub_right
    (UPre.scr_sub (by simp only [slot]; omega))).symm

theorem UPre.dIB {k m : Nat} (hm : k + m ≤ N s₀) : (ivR s₀).Disjoint ⟨blk s₀ k, 16 * m⟩ :=
  hp.iv_data.sub_right (Offset.sub_base _ (by omega))

end

theorem blk_sub_run (s₀ : State) {k m : Nat} : Region.Sub ⟨blk s₀ (k + m), 16⟩ ⟨blk s₀ k, 16 * (m + 1)⟩ :=
  Offset.sub _ (by omega) (by omega)

theorem copyMem_other (m : Mem) {P Q p : Addr} (h : (⟨p, 16⟩ : Region).Disjoint ⟨P, 16⟩) :
    bytesAt (copyMem m P Q) p 16 = bytesAt m p 16 :=
  bytesAt_frame (copyMem_frame m P Q) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by decide)

theorem xorMem_other (m : Mem) {P Q p : Addr} (h : (⟨p, 16⟩ : Region).Disjoint ⟨P, 16⟩) :
    bytesAt (xorMem m P Q) p 16 = bytesAt m p 16 :=
  bytesAt_frame (xorMem_frame m P Q) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by decide)

theorem one_disj_sub {r : Region} {R : Region} (h : Region.Sub r R) :
    ∀ r' ∈ [r], ∃ R' ∈ [R], Region.Sub r' R' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨R, by simp, h⟩

theorem one_disj {r : Region} {P : Addr} {n : Nat} (hd : (⟨P, n⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-! ## Saving the slots, and XORing them in -/

/-- The blocks `k` to `k + m - 1` at `r17` copied to slots `1` to `m`. -/
theorem copies_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (m : Nat) (hm : m ≤ 8) (hk : k + m ≤ N s₀)
    {t : State} (r17 : t.gpr .r17 = blk s₀ k) (r19 : t.gpr .r19 = S s₀)
    (hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]) (hW : t.wr = [ivR s₀, dataR s₀, scrR s₀])
    {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t', (∀ r, r ≠ .r9 → t'.gpr r = t.gpr r) → t'.rd = t.rd → t'.wr = t.wr →
      Frame [⟨sl s₀ 1, 128⟩] t.mem t'.mem →
      (∀ j < m, bytesAt t'.mem (sl s₀ (j + 1)) 16 = bytesAt t.mem (blk s₀ (k + j)) 16) →
      WP isa (.block rest) t' Φ) :
    WP isa (.block ((List.range m).flatMap (fun j => copy .r19 (slot (j + 1)) .r17 (16 * j)) ++ rest)) t Φ := by
  induction m generalizing rest Φ with
  | zero =>
    exact cont t (fun _ _ => rfl) rfl rfl (Frame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    refine ih (by omega) (by omega) fun t₁ g₁ rd₁ wr₁ f₁ e₁ => ?_
    have hR₁ : t₁.rd ++ t₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₁, wr₁, hR]
    have hW₁ : t₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, hW]
    refine copy_wp (P := sl s₀ (m + 1)) (Q := blk s₀ (k + m)) (by decide) (by decide) (by decide) (by decide)
      ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩ ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide), r19]) (by rw [g₁ _ (by decide), r19, sl8])
      (by rw [g₁ _ (by decide), r17, blk_add]) (by rw [g₁ _ (by decide), r17, blk_add8])
      (by rw [hR₁]; exact in_rw (by simp) (hp.cBlk0 (k := k + m) (by omega)))
      (by rw [hR₁]; exact in_rw (by simp) (hp.cBlk8 (k := k + m) (by omega)))
      (by rw [hW₁]; exact in_rw (by simp) (cSl s₀ (by omega)))
      (by rw [hW₁]; exact in_rw (by simp) (cSl8 s₀ (by omega)))
      fun t₂ g₂ mem₂ rd₂ wr₂ => cont t₂ (fun r hr => by rw [g₂ r hr, g₁ r hr]) (by rw [rd₂, rd₁])
        (by rw [wr₂, wr₁]) ?_ fun j hj => ?_
    · rw [mem₂]
      exact f₁.trans ((copyMem_frame _ _ _).sub (one_disj_sub (sl_sub1 s₀ (by omega) (by omega))))
    · rw [mem₂]
      by_cases hjm : j < m
      · rw [copyMem_other _ (dSS s₀ (by omega) (by omega) (by omega)), e₁ j hjm]
      · have : j = m := by omega
        subst this
        rw [copyMem_bytes _ (hp.dBS (by omega) (by omega)).symm,
          bytesAt_frame f₁ (one_disj (hp.dBG1 (by omega))) (by decide)]

/-- Block `i` before a step from `k ≤ i`, from the invariant. -/
theorem LInv.blockAt {M : Mode} {s₀ : State} {k i : Nat} {s : State} (h : LInv M s₀ k s) (hki : k ≤ i)
    (hi : i < N s₀) : bytesAt s.mem (blk s₀ i) 16 = blkOf s₀ i := by
  have hl : (outK M s₀ k).length = k := length_outK M s₀ (by omega)
  have := congrArg (·[i]?) h.data
  simp only [getElem?_blocksAt _ _ hi, List.getElem?_append_right (show (outK M s₀ k).length ≤ i by omega),
    hl, List.getElem?_drop, Nat.add_sub_cancel' hki] at this
  rw [Option.some.inj this, blkOf, List.getD_eq_getElem?_getD, getElem?_blocksAt _ _ hi]
  rfl

/-- Slot 0 the chaining value, and blocks `k` to `k + m - 1` slots `1` to `m`. -/
theorem saveSlots_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k m : Nat} (hm : m ≤ 8) (hk : k + m ≤ N s₀)
    {s : State} (h : LInv M s₀ k s) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ s', (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨S s₀, 144⟩] s.mem s'.mem →
      bytesAt s'.mem (sl s₀ 0) 16 = chainK M s₀ k →
      (∀ j < m, bytesAt s'.mem (sl s₀ (j + 1)) 16 = blkOf s₀ (k + j)) →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (saveSlots m ++ rest)) s Φ := by
  have hR := h.regs hp
  have hW := h.wrs hp
  rw [saveSlots, List.append_assoc]
  refine copy_wp (P := sl s₀ 0) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h.r19]) (by rw [h.r19, sl8]) (by rw [h.r16, ofNat_zero_add]) (by rw [h.r16])
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (cSl s₀ (by decide)))
    (by rw [hW]; exact in_rw (by simp) (cSl8 s₀ (by decide))) fun s₁ g₁ mem₁ rd₁ wr₁ => ?_
  refine copies_wp hp m hm hk (by rw [g₁ _ (by decide), h.r17]) (by rw [g₁ _ (by decide), h.r19])
    (by rw [rd₁, wr₁, hR]) (by rw [wr₁, hW]) fun s₂ g₂ rd₂ wr₂ f₂ e₂ => ?_
  refine cont s₂ (fun r hr => by rw [g₂ r hr, g₁ r hr]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_ ?_
    fun j hj => ?_
  · rw [mem₁] at f₂
    refine ((copyMem_frame _ _ _).sub (one_disj_sub (sl_sub s₀ (by decide)))).trans (f₂.sub ?_)
    exact one_disj_sub (Offset.sub_base _ (by simp only [slot]; omega))
  · rw [bytesAt_frame f₂ (one_disj (Offset.disjoint _ (by simp only [slot]; omega)
      (by simp only [slot]; omega) (by simp only [slot]; omega))) (by decide),
      mem₁, copyMem_bytes _ (hp.dIS (by decide)).symm, h.iv]
  · rw [e₂ j hj, mem₁, copyMem_other _ (hp.dBS (by omega) (by decide)), h.blockAt (by omega) (by omega)]

/-- Each of blocks `k` to `k + m - 1` at `r17` XORed with its slot. -/
theorem fixes_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (m : Nat) (hm : m ≤ 8) (hk : k + 8 ≤ N s₀)
    {t : State} (r17 : t.gpr .r17 = blk s₀ k) (r19 : t.gpr .r19 = S s₀)
    (hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]) (hW : t.wr = [ivR s₀, dataR s₀, scrR s₀])
    {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t', (∀ r, r ≠ .r9 → r ≠ .r10 → t'.gpr r = t.gpr r) → t'.rd = t.rd → t'.wr = t.wr →
      Frame [⟨blk s₀ k, 16 * m⟩] t.mem t'.mem →
      (∀ j < m, bytesAt t'.mem (blk s₀ (k + j)) 16 =
        Spec.Cbc.xor (bytesAt t.mem (blk s₀ (k + j)) 16) (bytesAt t.mem (sl s₀ j) 16)) →
      WP isa (.block rest) t' Φ) :
    WP isa (.block ((List.range m).flatMap (fun j => xorAt .r17 (16 * j) .r19 (slot j)) ++ rest)) t Φ := by
  induction m generalizing rest Φ with
  | zero =>
    exact cont t (fun _ _ _ => rfl) rfl rfl (Frame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    refine ih (by omega) fun t₁ g₁ rd₁ wr₁ f₁ e₁ => ?_
    have hR₁ : t₁.rd ++ t₁.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₁, wr₁, hR]
    have hW₁ : t₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₁, hW]
    refine xorAt_wp (P := blk s₀ (k + m)) (Q := sl s₀ m) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨by omega, by omega⟩ ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩
      (by rw [g₁ _ (by decide) (by decide), r17, blk_add]) (by rw [g₁ _ (by decide) (by decide), r17, blk_add8])
      (by rw [g₁ _ (by decide) (by decide), r19]) (by rw [g₁ _ (by decide) (by decide), r19, sl8])
      (by rw [hR₁]; exact in_rw (by simp) (hp.cBlk0 (k := k + m) (by omega)))
      (by rw [hR₁]; exact in_rw (by simp) (hp.cBlk8 (k := k + m) (by omega)))
      (by rw [hR₁]; exact in_rw (by simp) (cSl s₀ (by omega)))
      (by rw [hR₁]; exact in_rw (by simp) (cSl8 s₀ (by omega)))
      (by rw [hW₁]; exact in_rw (by simp) (hp.cBlk0 (k := k + m) (by omega)))
      (by rw [hW₁]; exact in_rw (by simp) (hp.cBlk8 (k := k + m) (by omega)))
      fun t₂ g₂ mem₂ rd₂ wr₂ => cont t₂ (fun r h9 h10 => by rw [g₂ r h9 h10, g₁ r h9 h10])
        (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_ fun j hj => ?_
    · rw [mem₂]
      exact (f₁.sub (one_disj_sub (Region.sub_prefix (by omega)))).trans
        ((xorMem_frame _ _ _).sub (one_disj_sub (blk_sub_run s₀)))
    · rw [mem₂]
      by_cases hjm : j < m
      · rw [xorMem_other _ (hp.dBB (by omega) (by omega) (by omega)), e₁ j hjm]
      · have : j = m := by omega
        subst this
        rw [xorMem_bytes _ (hp.dBS (by omega) (by omega)),
          bytesAt_frame f₁ (one_disj (hp.dB_run (by omega) (.inr (Nat.le_refl _)) (by omega))) (by decide),
          bytesAt_frame f₁ (one_disj (hp.dSB (by omega) (by omega))) (by decide)]

/-! ## The loop of groups -/

theorem ofNat_shr3 {j : Nat} (hj : j < 2 ^ 64) : BitVec.ofNat 64 j >>> 3 = BitVec.ofNat 64 (j / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The invariant holds after a write of `r9`. -/
theorem LInv.upd9 {M : Mode} {s₀ : State} {k : Nat} {s s' : State} {v : BitVec 64} (h : LInv M s₀ k s)
    (u : Upd s s' .r9 v) : LInv M s₀ k s' where
  r14 := (u.other _ (by decide)).trans h.r14
  r15 := (u.other _ (by decide)).trans h.r15
  r16 := (u.other _ (by decide)).trans h.r16
  r17 := (u.other _ (by decide)).trans h.r17
  r18 := (u.other _ (by decide)).trans h.r18
  r19 := (u.other _ (by decide)).trans h.r19
  keep r hr hv := (u.other r (preserved_ne hr).2.2.2.2.2.1).trans (h.keep r hr hv)
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  frame := by rw [u.mem]; exact h.frame
  data := by rw [u.mem]; exact h.data
  iv := by rw [u.mem]; exact h.iv

theorem count_wp {M : Mode} {s₀ : State} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    WP isa (.block countG) s fun s' => LInv M s₀ k s' ∧ s'.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k) / 8) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  unfold countG
  refine wp_lsr (by decide) fun s₁ u₁ => wp_nil ⟨h.upd9 u₁, ?_⟩
  rw [u₁.gpr, h.r18, ofNat_shr3 (by omega)]

theorem div8_lt {j : Nat} (hj : j < 2 ^ 64) : j / 8 < 2 ^ 64 := by omega

/-- One run of `group` takes the invariant from `k` blocks to `k + 8` when at
least eight are left. -/
def GroupOk (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 8 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa group s (LInv M s₀ (k + 8))

/-- The groups, from `k₀` blocks: the invariant after some `k` blocks with
fewer than eight left. -/
theorem groupLoop_wp {M : Mode} {group : Prog isa} (hg : GroupOk M group) {s₀ : State} (hp : UPre s₀)
    {k₀ : Nat} (hk₀ : k₀ ≤ N s₀) {s : State} (h : LInv M s₀ k₀ s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k₀) / 8)) :
    WP isa (.ite (.zero .d .r9) (.block []) (.loop (.seq group (.block countG)) (.nonzero .d .r9))) s
      fun s' => ∃ k, k ≤ N s₀ ∧ N s₀ - k < 8 ∧ LInv M s₀ k s' := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  refine WP.ite (decide ((N s₀ - k₀) / 8 = 0)) (eval_zero_ofNat s .r9 (div8_lt (by omega)) h9)
    (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨k₀, hk₀, by simp at hb; omega, h⟩
  · let I : Nat → State → Prop := fun m s => ∃ k, m = N s₀ - k ∧ k + 8 ≤ N s₀ ∧ LInv M s₀ k s
    have hstep : ∀ m s, I m s → WP isa (.seq group (.block countG)) s (fun s' =>
        (isa.eval (.nonzero .d .r9) s' = some false ∧ ∃ k, k ≤ N s₀ ∧ N s₀ - k < 8 ∧ LInv M s₀ k s') ∨
        (isa.eval (.nonzero .d .r9) s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨k, rfl, hk, hI⟩
      refine WP.seq (WP.mono (hg hp hk hI) fun s₁ h₁ => WP.mono (count_wp h₁) fun s₂ ⟨h₂, r9₂⟩ => ?_)
      have ev := eval_nonzero_ofNat' s₂ .r9 (div8_lt (by omega)) r9₂
      by_cases hlt : (N s₀ - (k + 8)) / 8 = 0
      · exact .inl ⟨by rw [ev]; simp [hlt], k + 8, hk, by omega, h₂⟩
      · exact .inr ⟨by rw [ev]; simp [hlt], N s₀ - (k + 8), by omega, k + 8, rfl, by omega, h₂⟩
    exact WP.loop (M := isa) I hstep (N s₀ - k₀) s ⟨k₀, rfl, by simp at hb; omega, h⟩

/-- `groups group one` takes the invariant from no blocks to all of them. -/
theorem groups_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one)
    {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv M s₀ 0 s) :
    WP isa (groups group one) s (LInv M s₀ (N s₀)) := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  refine WP.seq (WP.mono (count_wp h) fun s₁ ⟨h₁, r9₁⟩ => ?_)
  refine WP.seq (WP.mono (groupLoop_wp hg hp (Nat.zero_le _) h₁ r9₁) fun s₂ ⟨k, hk, _, h₂⟩ => ?_)
  have ev := eval_zero_ofNat s₂ .r18 (k := N s₀ - k) (by omega) h₂.r18
  refine WP.ite (decide (N s₀ - k = 0)) ev (fun hz => ?_) (fun hz => ?_)
  · have : k = N s₀ := by simp at hz; omega
    exact WP.block_nil (this ▸ h₂)
  · exact loop_ok hb hp (by simp at hz; omega) h₂

theorem batched_wp {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hb : BodyOk M one)
    {s₀ : State} (h0 : (modePPC64LE M).pre s₀) : WP isa (batched group one) s₀ (Done M s₀) :=
  ends_wp h0 fun hp _ _ h => groups_wp hg hb hp h

/-! ## The arguments of a call on eight blocks, and on to the next group -/

/-- The arguments of the block function for the eight blocks at `r17`. -/
theorem callArgs8_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r15 → s'.gpr .r5 = s.gpr .r17 →
      s'.gpr .r6 = BitVec.ofNat 64 8 → s'.gpr .r7 = s.gpr .r19 →
      (∀ r, r ∉ argRegs5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block callArgs8) s Φ := by
  unfold callArgs8 mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · simp only [argRegs5, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h3, h4, h5, h6, h7⟩ := hr
    rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- On to the block after the eight. -/
theorem advance8_regs {s₀ : State} {k : Nat} (hk : k + 8 ≤ N s₀) {s : State} {Φ : State → Prop}
    (h17 : s.gpr .r17 = blk s₀ k) (h18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k))
    (h : ∀ s', s'.gpr .r17 = blk s₀ (k + 8) → s'.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + 8)) →
      (∀ r, r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → Φ s') :
    WP isa (.block advance8) s Φ := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  unfold advance8
  refine wp_addi (by decide) (by decide) fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ => wp_nil ?_
  refine h s₂ ?_ ?_ (fun r h₁ h₂ => ?_) ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr, h17, Offset.add_add_eq _ (c := 16 * (k + 8)) (by omega)]
  · rw [u₂.gpr, u₁.other _ (by decide), h18, Offset.ofNat_sub_ofNat (by omega)]; rfl
  · rw [u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

/-- The arguments of a call on blocks `k` to `k + 7`, with the working space
at the start of the scratch buffer. -/
theorem UPre.callPre8 {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = blk s₀ k)
    (r6 : s.gpr .r6 = BitVec.ofNat 64 8) (r7 : s.gpr .r7 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre8 s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (Offset.sub_base _ (by omega))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
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

/-! ## Constant time -/

/-- One run of `group` from `k` blocks is constant time. -/
def GroupCt (M : Mode) (group : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modePPC64LE M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k + 8 ≤ N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂) group fun _ _ => True

/-- What is known between the code before the call of a group and the call,
on the eight blocks at `D` with the working space at `Sc`. -/
structure Mid8 (s₀ : State) (k : Nat) (D Sc : Addr) (s : State) : Prop where
  pre : CallPre8 s (W s₀) D Sc (R s₀)
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  sp : s.sp = s₀.sp

theorem Mid8.of {s₀ : State} {k : Nat} {D Sc : Addr} {s s₁ : State} {M : Mode} (h : LS M s₀ k s)
    (pre : CallPre8 s₁ (W s₀) D Sc (R s₀)) (saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r)
    (hs : s₁.sp = s.sp) : Mid8 s₀ k D Sc s₁ :=
  ⟨pre, by rw [saved .r16 (by decide), h.1.r16], by rw [saved .r17 (by decide), h.1.r17],
    by rw [saved .r18 (by decide), h.1.r18], by rw [saved .r19 (by decide), h.1.r19], hs.trans h.2⟩

theorem After.of8 {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat}
    {D Sc : Addr} {s s' : State} (h : Mid8 s₀ k D Sc s) (hc : CallPost8 f s (W s₀) D (R s₀) s') :
    After s₀ k s' :=
  ⟨by rw [hc.saved .r16 (by decide), h.r16], by rw [hc.saved .r17 (by decide), h.r17],
    by rw [hc.saved .r18 (by decide), h.r18], by rw [hc.saved .r19 (by decide), h.r19],
    hc.sp.trans h.sp⟩

/-- A group: code before the call (`pre`), the call of a block function on
the eight blocks at `D s₀ k` with the working space at `Sc s₀` (both
public), and code after it (`post`), constant time when `pre`'s addresses and
branches depend only on the registers the invariant pins and `post`'s on
`r16` to `r19`. -/
theorem group_ct {M : Mode} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {name : String} {c : Prog isa} {pre post : List Instr} {D : State → Nat → Addr} {Sc : State → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (modePPC64LE M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    (pubSc : ∀ {s₀ s₀' : State}, (modePPC64LE M).pub s₀ s₀' → Sc s₀ = Sc s₀')
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (okF : ∀ s, (Proof.Aes.PPC64LE.blocksFramed f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.PPC64LE.blocksFramed f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    (nf : c.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k + 8 ≤ N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s fun s₁ => CallPre8 s₁ (W s₀) (D s₀ k) (Sc s₀) (R s₀) ∧
        ∀ r ∈ preserved, s₁.gpr r = s.gpr r)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modePPC64LE M).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k + 8 ≤ N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂)
      (.seq (.block pre) (.seq (.call name c) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (taintRegs (P := fun s₁ s₂ => k + 8 ≤ N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, pub_sp hq], LInv.agree hq h.2.1.1 h.2.2.1⟩) hA).wp
    (F₁ := Mid8 s₀ k (D s₀ k) (Sc s₀)) (F₂ := Mid8 s₀' k (D s₀' k) (Sc s₀')) fun _ _ h =>
      ⟨WP.mono (wp_sp (wpA hp h.1 h.2.1.1)) fun _ ⟨⟨a, g⟩, e⟩ => Mid8.of h.2.1 a g e,
       WP.mono (wp_sp (wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2.1)) fun _ ⟨⟨a, g⟩, e⟩ =>
        Mid8.of h.2.2 a g e⟩
  have c := (blk_rel8 (name := name) ok ct
      (P := fun s₁ s₂ => Mid8 s₀ k (D s₀ k) (Sc s₀) s₁ ∧ Mid8 s₀' k (D s₀' k) (Sc s₀') s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pubSc hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call8 (name := name) okF nf h.1.pre) fun _ hc => After.of8 h.1 hc,
       WP.mono (blk_call8 (name := name) okF nf h.2.pre) fun _ hc => After.of8 h.2 hc⟩
  have b := taintRegs (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) [.r16, .r17, .r18, .r19]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r16, h.2.r16, pub_Iv hq]
      · rw [h.1.r17, h.2.r17, pub_blk hq]
      · rw [h.1.r18, h.2.r18, pub_N hq]
      · rw [h.1.r19, h.2.r19, pub_S hq]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem count_taint : ∃ h, (taint.check (Taint.ofRegs [.r18]) (.block countG) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem count_rel {M : Mode} {s₀ s₀' : State} (hq : (modePPC64LE M).pub s₀ s₀') (k : Nat)
    {P : State → State → Prop} (hP : ∀ a b, P a b → LS M s₀ k a ∧ LS M s₀' k b) :
    RelCT isa P (.block countG) fun a b =>
      (LS M s₀ k a ∧ a.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k) / 8)) ∧
      (LS M s₀' k b ∧ b.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k) / 8)) := by
  obtain ⟨_, hc⟩ := count_taint
  have t := taintRegs (P := P) [.r18] (fun a b (h : P a b) => ⟨by rw [(hP a b h).1.2, (hP a b h).2.2, pub_sp hq],
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [(hP a b h).1.1.r18, (hP a b h).2.1.r18, pub_N hq]⟩) hc
  refine (t.wp (F₁ := fun (s : State) => LS M s₀ k s ∧ s.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k) / 8))
    (F₂ := fun (s : State) => LS M s₀' k s ∧ s.gpr .r9 = BitVec.ofNat 64 ((N s₀ - k) / 8)) fun a b (h : P a b) =>
      ⟨WP.mono (wp_sp (count_wp (hP a b h).1.1)) fun s ⟨⟨l, r9⟩, e⟩ => ⟨⟨l, e.trans (hP a b h).1.2⟩, r9⟩,
       WP.mono (wp_sp (count_wp (hP a b h).2.1)) fun s ⟨⟨l, r9⟩, e⟩ =>
        ⟨⟨l, e.trans (hP a b h).2.2⟩, by rw [r9, pub_N hq]⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The groups' loop relation, with the number of iterations left. -/
def GRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k + 8 ≤ N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂

/-- Both runs after `k` blocks, with fewer than eight left. -/
def GDone (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N s₀ ∧ N s₀ - k < 8 ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂

theorem groupLoop_ct {M : Mode} {group : Prog isa} (hg : GroupOk M group) (hc : GroupCt M group)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modePPC64LE M).pub s₀ s₀') (n : Nat) :
    RelCT isa (GRel M s₀ s₀' n) (.loop (.seq group (.block countG)) (.nonzero .d .r9)) (GDone M s₀ s₀') := by
  refine RelCT.loop (M := isa) (GRel M s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : GRel M s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k + 8 ≤ N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp (F₁ := LS M s₀ (k + 8)) (F₂ := LS M s₀' (k + 8))
    fun _ _ h => ⟨WP.mono (wp_sp (hg hp h.1 h.2.1.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.1.2⟩,
      WP.mono (wp_sp (hg hp' (by rw [← hN]; exact h.1) h.2.2.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2.2.2⟩⟩
  have cnt := count_rel hq (k + 8) (P := fun a b => True ∧ LS M s₀ (k + 8) a ∧ LS M s₀' (k + 8) b)
    fun _ _ h => ⟨h.2.1, h.2.2⟩
  refine ((ct.mono (fun _ _ h => h) fun _ _ h => h).seq cnt).mono (fun _ _ h => h.2) fun s₁ s₂ h => ?_
  obtain ⟨⟨l₁, r9₁⟩, ⟨l₂, r9₂⟩⟩ := h
  have e₁ := eval_nonzero_ofNat' s₁ .r9 (div8_lt (by omega)) r9₁
  have e₂ := eval_nonzero_ofNat' s₂ .r9 (div8_lt (by omega)) r9₂
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have : (N s₀ - (k + 8)) / 8 = 0 := by simpa using hf
    exact ⟨k + 8, hk, by omega, l₁, l₂⟩
  · rw [e₁] at ht
    have : (N s₀ - (k + 8)) / 8 ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 8), by omega, k + 8, rfl, by omega, l₁, l₂⟩

theorem groups_rel {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modePPC64LE M).pub s₀ s₀') :
    RelCT isa (fun a b => LS M s₀ 0 a ∧ LS M s₀' 0 b) (groups group one)
      fun a b => LS M s₀ (N s₀) a ∧ LS M s₀' (N s₀') b := by
  have hN := pub_N hq
  have hb₀ : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  obtain ⟨_, hnil⟩ := nil_taint
  have cnt := count_rel hq 0 (P := fun a b => LS M s₀ 0 a ∧ LS M s₀' 0 b) fun _ _ h => h
  -- The groups, if at least eight blocks.
  have loop : RelCT isa (fun a b =>
      (LS M s₀ 0 a ∧ a.gpr .r9 = BitVec.ofNat 64 ((N s₀ - 0) / 8)) ∧
      (LS M s₀' 0 b ∧ b.gpr .r9 = BitVec.ofNat 64 ((N s₀ - 0) / 8)))
      (.ite (.zero .d .r9) (.block []) (.loop (.seq group (.block countG)) (.nonzero .d .r9)))
      (GDone M s₀ s₀') := by
    refine RelCT.ite (fun a b h => by
      rw [eval_zero_ofNat a .r9 (div8_lt (by omega)) h.1.2, eval_zero_ofNat b .r9 (div8_lt (by omega)) h.2.2])
      ?_ ?_
    · have nil' := (taintRegs (P := fun a b => ((LS M s₀ 0 a ∧ a.gpr .r9 = BitVec.ofNat 64 ((N s₀ - 0) / 8)) ∧
          (LS M s₀' 0 b ∧ b.gpr .r9 = BitVec.ofNat 64 ((N s₀ - 0) / 8))) ∧
          isa.eval (.zero .d .r9) a = some true) []
        (fun _ _ h => ⟨by rw [h.1.1.1.2, h.1.2.1.2, pub_sp hq], fun r hr => by simp at hr⟩) hnil).wp
        (F₁ := fun a => LS M s₀ 0 a ∧ N s₀ - 0 < 8) (F₂ := LS M s₀' 0) fun a b h =>
          ⟨WP.block_nil ⟨h.1.1.1, by
            have := h.2; rw [eval_zero_ofNat a .r9 (div8_lt (by omega)) h.1.1.2] at this
            have : (N s₀ - 0) / 8 = 0 := by simpa using this
            omega⟩, WP.block_nil h.1.2.1⟩
      exact nil'.mono (fun _ _ h => h) fun _ _ h => ⟨0, Nat.zero_le _, h.2.1.2, h.2.1.1, h.2.2⟩
    · exact (groupLoop_ct hg hgc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, by
        have := h.2; rw [eval_zero_ofNat a .r9 (div8_lt (by omega)) h.1.1.2] at this
        have : (N s₀ - 0) / 8 ≠ 0 := by simpa using this
        omega, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  -- The blocks left, one at a time.
  have tail : RelCT isa (GDone M s₀ s₀') (.ite (.zero .d .r18) (.block []) (.loop one (.nonzero .d .r18)))
      fun a b => LS M s₀ (N s₀) a ∧ LS M s₀' (N s₀') b := by
    refine (RelCT.exists_ fun k => ?_).mono (fun a b (h : GDone M s₀ s₀' a b) => h) fun _ _ h => h
    by_cases hk : k ≤ N s₀
    swap
    · exact RelCT.of_false fun _ _ h => hk h.1
    have ev {t : State} {s : State} {M' : Mode} (h : LS M' t k s) (ht : N t = N s₀) :
        isa.eval (.zero .d .r18) s = some (decide (N s₀ - k = 0)) := by
      rw [← ht]; exact eval_zero_ofNat s .r18 (by rw [ht]; omega) h.1.r18
    refine RelCT.ite (fun a b h => by rw [ev h.2.2.1 rfl, ev h.2.2.2 hN.symm]) ?_ ?_
    · have nil' := (taintRegs (P := fun a b => (k ≤ N s₀ ∧ N s₀ - k < 8 ∧ LS M s₀ k a ∧ LS M s₀' k b) ∧
          isa.eval (.zero .d .r18) a = some true) []
        (fun _ _ h => ⟨by rw [h.1.2.2.1.2, h.1.2.2.2.2, pub_sp hq], fun r hr => by simp at hr⟩) hnil).wp
        (F₁ := LS M s₀ (N s₀)) (F₂ := LS M s₀' (N s₀')) fun a b h => by
          have e : k = N s₀ := by
            have := h.2; rw [ev h.1.2.2.1 rfl] at this
            have : N s₀ - k = 0 := by simpa using this
            omega
          exact ⟨WP.block_nil (e ▸ h.1.2.2.1), WP.block_nil (by rw [← hN, ← e]; exact h.1.2.2.2)⟩
      exact nil'.mono (fun _ _ h => h) fun _ _ h => h.2
    · exact (loop_ct hb hbc hp hp' hq (N s₀ - k)).mono (fun a b h => ⟨k, rfl, by
        have := h.2; rw [ev h.1.2.2.1 rfl] at this
        have : ¬ (N s₀ - k = 0) := by simpa using this
        omega, h.1.2.2.1, h.1.2.2.2⟩) fun _ _ h => h
  exact (cnt.mono (fun _ _ h => h) fun _ _ h => h).seq (loop.seq tail)

theorem batched_ct {M : Mode} {group one : Prog isa} (hg : GroupOk M group) (hgc : GroupCt M group)
    (hb : BodyOk M one) (hbc : BodyCt M one) :
    ConstantTime isa (modePPC64LE M).pre (modePPC64LE M).pub (batched group one) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' _ => groups_rel hg hgc hb hbc hp hp' hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.PPC64LE
