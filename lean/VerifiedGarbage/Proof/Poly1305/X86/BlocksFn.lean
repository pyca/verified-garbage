module

public import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.X86.Sse2
import VerifiedGarbage.Proof.Framework.X86.Rel2
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Rel2
meta import VerifiedGarbage.Proof.Poly1305.X86.Blocks
meta import VerifiedGarbage.Proof.Poly1305.X86.Lit
meta import VerifiedGarbage.Impl.Poly1305.X86
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Poly1305 on x86 (32-bit): `blocks`, the whole function

`vg_poly1305_blocks`, from its prologue, the pairs of blocks it absorbs from
16 blocks on (`Sse2.lean`), the step of its loop (`body_ok`) and its
epilogue (`Blocks.lean`): it is correct (`blocks_ok`) and constant time
(`blocks_ct`), for the functions that call it (ChaCha20-Poly1305's).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem blocks_eq : blocks = .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)),
    .mov .ecx (.mem (at_ .esp 12)), .alu .cmp .ecx (.imm 16)] : List Instr)))
    (.seq (.ite .b (.block []) (.seq (.block [.shift .shr .ecx 1]) pairs))
      (.seq (.block atEnd) (.seq (.ite .e (.block []) (.loop body .ne)) (.block (reduce ++ restore))))) := rfl

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
      .alu .cmp .ecx (.imm 16)] : List Instr))) s₀ fun s => ∃ F, SetupF s₀ F ∧
        BInv s₀ F 0 s ∧ s.gpr .ecx = arg s₀ 2 ∧ s.cf = some (decide (nb s₀ < 16)) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit
    (by rw [hp.wr]; exact List.mem_singleton_self _)) fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  obtain esp₁ := A₁.gpr .esp (by decide)
  obtain hF' := SetupF.of hF sv co
  obtain fr₁ : Frame [sR (stp s₀), stkR s₀] s₀.mem s₁.mem := frame_stk A₁.frame
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  obtain ecx₃ : s₃.gpr .ecx = arg s₀ 2 := by
    rw [u₃.gpr, u₂.mem, hp.arg_same fr₁ (i := 2) (by decide)]
  refine wp_cmpx (readSrc_imm _ _) fun s₄ k₄ _ cf₄ => WP.block_nil ⟨F, hF', ?_, ?_, ?_⟩
  · have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
    refine ⟨c₁.keep (by rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, ?_, ?_, ?_, ?_, fun k hk _ => ?_, fun hA => ?_⟩
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.gpr, hp.arg_same fr₁ (i := 1) (by decide)]
      simp only [Nat.mul_zero, BitVec.add_zero]
    · rw [hm]; exact fr₁
    · rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd]
    · rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr]
    · rw [hm, words_eq A₁.words hk]
    · exact acc_entry hfit hF' (fun k hk => by rw [hm, words_eq A₁.words (by omega_using [hk])]) hA
  · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), ecx₃]
  · rw [cf₄, ecx₃]; rfl

/-! ## The pairs of blocks -/

theorem shr1_eq (x : BitVec 32) : x >>> 1 = BitVec.ofNat 32 (x.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega_using [this])]

/-- The invariant survives a change of the registers it does not name. -/
theorem BInv.regs {s₀ s s' : State} {F : Nat → Nat} {i : Nat} (h : BInv s₀ F i s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : BInv s₀ F i s' :=
  ⟨h.ctx.keep hedi hwr, hesp.trans h.esp, hesi.trans h.esi, by rw [hm]; exact h.frame, hrd.trans h.rd,
    hwr.trans h.wr, fun k hk hS => by rw [hm]; exact h.keep k hk hS, fun hA => by rw [hm]; exact h.acc hA⟩

private theorem BPre.stk_eq {s₀ : State} (hp : BPre s₀) : below (s₀.gpr .esp) 524 = stkR s₀ := by
  show (⟨(s₀.gpr .esp - BitVec.ofNat 32 524).setWidth 64, 524⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth hp.sp_stk]

/-- The number of pairs into `ecx`: what `pairs` starts from. -/
private theorem blockPairsArg_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} {s : State} (h : BInv s₀ F 0 s)
    (hecx : s.gpr .ecx = arg s₀ 2) (h16 : 16 ≤ nb s₀) :
    WP isa (.block [.shift .shr .ecx 1]) s fun s₂ =>
      BInv s₀ F 0 s₂ ∧ Sse2.PPre (stp s₀) (bp s₀) (nb s₀ / 2) s₂ := by
  have hbf := hp.bl_fit
  obtain ⟨p, hpdef⟩ : ∃ p, p = nb s₀ / 2 := ⟨_, rfl⟩
  rw [← hpdef]
  have hp8 : 2 ≤ p := by omega_using [hpdef, h16]
  have hpl : 32 * p ≤ 16 * nb s₀ := by omega_using [hpdef]
  refine wp_shr (by decide) fun s₂ u₂ => WP.block_nil ?_
  have hI₂ : BInv s₀ F 0 s₂ := h.regs (u₂.other _ (by decide)) (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.mem u₂.rd u₂.wr
  have hsub : Region.Sub (Proof.Aes.X86.reg32 (bp s₀) (32 * p)) (blR s₀) := Region.sub_prefix hpl
  exact ⟨hI₂,
    { ctx := hI₂.ctx
      esi := by rw [hI₂.esi]; simp only [Nat.mul_zero, BitVec.add_zero]
      ecx := by rw [u₂.gpr, hecx, hpdef]; exact shr1_eq _
      two := hp8
      dfit := by omega_using [hbf, hpl]
      din := fun d hd => by
        rw [hI₂.rd, hI₂.wr, hp.rd, addr_eq (by omega_using [hd, hpl, hbf])]
        exact ⟨blR s₀, by simp only [List.cons_append, List.nil_append, List.mem_cons, true_or],
          Offset.contains_base _ (by omega_using [hd, hpl]) (by omega_using [hd, hpl, hbf])⟩
      sp := by rw [hI₂.esp]; exact hp.sp_stk
      ss := by rw [hI₂.esp, hp.stk_eq]; exact hp.stk_st
      sd := by rw [hI₂.esp, hp.stk_eq]; exact hp.stk_bl.sub_right hsub
      ds := hp.st_bl.sub_right hsub }⟩

theorem blks_zero (s₀ : State) : blks s₀ 0 = [] := by
  simp only [blks, Nat.mul_zero, bytesAt, List.range_zero, List.map_nil]

/-- The pairs of blocks, from the first block. -/
private theorem blockPairsRun_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {p : Nat}
    {s₂ : State} (hI : BInv s₀ F 0 s₂) (hP : Sse2.PPre (stp s₀) (bp s₀) p s₂) (hpl : 2 * p ≤ nb s₀) :
    WP isa pairs s₂ (BInv s₀ F (2 * p)) := by
  have hbf := hp.bl_fit
  have hsub : Region.Sub (Proof.Aes.X86.reg32 (bp s₀) (32 * p)) (blR s₀) :=
    Region.sub_prefix (by omega_using [hpl])
  refine WP.mono (Sse2.pairs_ok hP.ctx hP.esi hP.ecx hP.two hP.dfit hP.din hP.sp hP.ss hP.sd hP.ds
    (C := A0 s₀ < P) (X := A0 s₀)
    (fun hA => ⟨hF.coefs' fun k hk hS => hI.keep k hk hS, (hI.acc hA).1, by
      have := (hI.acc hA).2
      rwa [blks_zero, Poly1305.absorbAll_nil] at this⟩))
    fun s' ⟨g, esi, rd, wr, fr, same, hv⟩ => ?_
  rw [hI.esp, hp.stk_eq] at fr
  refine ⟨hI.ctx.keep (g _ (by decide) (by decide)) wr, by rw [g _ (by decide) (by decide)]; exact hI.esp,
    by rw [esi, show 16 * (2 * p) = 32 * p by omega_using []], hI.frame.trans fr, by rw [rd]; exact hI.rd,
    by rw [wr]; exact hI.wr, fun k hk hS' => (same k hk hS').trans (hI.keep k hk hS'), fun hA => ?_⟩
  obtain ⟨h4, hv'⟩ := hv hA
  refine ⟨h4, ?_⟩
  have eb : bytesAt s₂.mem ((bp s₀).setWidth 64) (32 * p) = bytesAt s₀.mem ((bp s₀).setWidth 64) (32 * p) :=
    Sse2.bytesAt_frame hI.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_bl.sub_right hsub).symm
      · exact (hp.stk_bl.sub_right hsub).symm) (by omega_using [hbf, hpl])
  rw [hv', eb]
  show _ = Poly1305.absorbAll (Rn s₀) (A0 s₀) (bytesAt s₀.mem ((bp s₀).setWidth 64) (16 * (2 * p))) % P
  rw [show 16 * (2 * p) = 32 * p by omega_using []]

/-- From 16 blocks on, the pairs of blocks. -/
theorem blockPairs_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hL : BInv s₀ F 0 s) (hcx : s.gpr .ecx = arg s₀ 2) (hcf : s.cf = some (decide (nb s₀ < 16))) :
    WP isa (.ite .b (.block []) (.seq (.block [.shift .shr .ecx 1]) pairs)) s fun s' =>
      ∃ i, i ≤ nb s₀ ∧ nb s₀ - i < 16 ∧ BInv s₀ F i s' := by
  refine WP.ite (decide (nb s₀ < 16)) (by simp only [eval, hcf])
    (fun hb => WP.block_nil ⟨0, Nat.zero_le _, by simpa using hb, hL⟩) (fun hb => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
  exact WP.seq (WP.mono (blockPairsArg_ok hp hL hcx hb) fun s₂ ⟨hI₂, hP₂⟩ =>
    WP.mono (blockPairsRun_ok hp hF hI₂ hP₂ (by omega_using [])) fun s' h' =>
      ⟨2 * (nb s₀ / 2), by omega_using [], by omega_using [], h'⟩)

/-! ## The blocks left -/

theorem endAt_eq {bp : BitVec 32} {n i : Nat} (hi : i ≤ n) :
    BitVec.ofNat 32 (16 * n) + bp - (bp + BitVec.ofNat 32 (16 * i)) = BitVec.ofNat 32 (16 * (n - i)) := by
  apply BitVec.eq_of_toNat_eq
  have := bp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hi]

/-- Whether block `i` is the end of the blocks. -/
theorem atEndAt_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} {i : Nat} (hi : i ≤ nb s₀)
    (hlt : nb s₀ - i < 16) {s : State} (hL : BInv s₀ F i s) :
    WP isa (.block atEnd) s fun s' => BInv s₀ F i s' ∧ s'.zf = some (decide (i = nb s₀)) := by
  refine WP.mono (atEnd_ok (n := arg s₀ 2) (b := arg s₀ 1)
    (by rw [hL.esp]; exact hp.arg_same hL.frame (i := 2) (by decide))
    (by rw [hL.esp]; exact hp.arg_same hL.frame (i := 1) (by decide))
    (by rw [hL.rd, hL.wr, hL.esp]; exact hp.argIn (i := 2) (by decide))
    (by rw [hL.rd, hL.wr, hL.esp]; exact hp.argIn (i := 1) (by decide))) fun s₃ ⟨k₃, z₃⟩ => ?_
  refine ⟨hL.regs k₃.gpr' k₃.gpr' k₃.gpr' k₃.2.1 k₃.2.2.1 k₃.2.2.2, ?_⟩
  rw [z₃, hL.esi, endAt_eq hi, ofNat32_beq_zero (by omega_using [hlt])]
  exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hi], fun h => by omega_using [h]⟩)

/-- The blocks from block `i` on, one at a time. -/
theorem loopPart_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {i : Nat}
    (hi : i ≤ nb s₀) {s : State} (hL : BInv s₀ F i s) (hz : s.zf = some (decide (i = nb s₀))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s (BInv s₀ F (nb s₀)) := by
  refine WP.ite (decide (i = nb s₀)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : i = nb s₀ := by simpa using h
    subst h0
    exact WP.block_nil (M := isa) hL
  · have hlt : i < nb s₀ := by
      have : i ≠ nb s₀ := by simpa using h
      omega_using [hi, this]
    let Inv : Nat → State → Prop := fun m s => ∃ j, m = nb s₀ - j ∧ j < nb s₀ ∧ BInv s₀ F j s
    obtain hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ BInv s₀ F (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨j, rfl, hj, hL⟩
      refine WP.mono (body_ok hp hF hj hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hj', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (j + 1), by omega_using [hj'], j + 1, rfl, hj', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀ - i) s ⟨i, rfl, hlt, hL⟩

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  rw [blocks_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨F, hF, hL₀, hcx, hcf⟩ => ?_)
  refine WP.seq (WP.mono (blockPairs_ok hp hF hL₀ hcx hcf) fun s₂ ⟨i, hi, hlt, hL⟩ => ?_)
  refine WP.seq (WP.mono (atEndAt_ok hp hi hlt hL) fun s₃ ⟨hL₃, hz⟩ => ?_)
  exact WP.seq (WP.mono (loopPart_ok hp hF hi hL₃ hz) fun s₄ hc => blocks_epilogue_ok hp hF hc)

/-! ## Constant time -/

/-- The taint with the stack arguments public, and the registers `rs`
besides `esp` (and the flags, if `fl`). The analysis starts from
`blocksτ [] false`. -/
def blocksτ (rs : List Reg) (fl : Bool) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := fl, argLen := 16 }

theorem blocks_wf {s : State} (hp : BPre s) (rs : List Reg) (fl : Bool) :
    VG.X86.Taint.Wf (blocksτ rs fl) s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [blocksτ]; omega_using [hs], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_singleton]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_st hp.arg_st

/-- Two states that satisfy the precondition, with the same `esp`,
arguments and registers `rs`, agree on what `blocksτ rs false` says is public. -/
theorem blocks_agree {s₁ s₂ : State} (hp₁ : BPre s₁) (hp₂ : BPre s₂) (hesp : s₁.gpr .esp = s₂.gpr .esp)
    (ha : ∀ i < 3, arg s₁ i = arg s₂ i) {rs : List Reg} (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (blocksτ rs false) s₁ s₂ := by
  refine ⟨⟨fun r hr' => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, blocks_wf hp₁ rs false,
    blocks_wf hp₂ rs false, VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi]))
      h4 hk⟩
  simp only [blocksτ, RegSet.mem_ofList, List.mem_cons] at hr'
  rcases hr' with rfl | hr'
  · exact hesp
  · exact hr r hr'

/-- The precondition holds of a state with the same `esp`, arguments and
regions. -/
theorem BPre.congr {s₀ t₀ : State} (hp : BPre s₀) (g : t₀.gpr .esp = s₀.gpr .esp) (hrd : t₀.rd = s₀.rd)
    (hwr : t₀.wr = s₀.wr) (ha : ∀ i < 3, arg t₀ i = arg s₀ i) : BPre t₀ := by
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have eB : blR t₀ = blR s₀ := by
    show (⟨(arg t₀ 1).setWidth 64, 16 * (arg t₀ 2).toNat⟩ : Region) = _; rw [a1, a2]
  have eS : sR (stp t₀) = sR (stp s₀) := by show sR (arg t₀ 0) = _; rw [a0]
  have eA : argAddr t₀ 0 = argAddr s₀ 0 := by
    show (t₀.gpr .esp + _).setWidth 64 = _; rw [g]; rfl
  have eR : retR t₀ = retR s₀ := by show (⟨(t₀.gpr .esp).setWidth 64, 4⟩ : Region) = _; rw [g]
  have eK : stkR t₀ = stkR s₀ := by
    show (⟨(t₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 524, 524⟩ : Region) = _; rw [g]
  exact
    { rd := by rw [hrd, eB, eA]; exact hp.rd
      wr := by rw [hwr, eS]; exact hp.wr
      st_bl := by rw [eS, eB]; exact hp.st_bl
      arg_st := by rw [eA, eS]; exact hp.arg_st
      ret_st := by rw [eR, eS]; exact hp.ret_st
      st_fit := by show (arg t₀ 0).toNat + 128 ≤ _; rw [a0]; exact hp.st_fit
      bl_fit := by show (arg t₀ 1).toNat + 16 * (arg t₀ 2).toNat ≤ _; rw [a1, a2]; exact hp.bl_fit
      sp_fit := by rw [g]; exact hp.sp_fit
      stk_st := by rw [eK, eS]; exact hp.stk_st
      stk_bl := by rw [eK, eB]; exact hp.stk_bl
      sp_stk := by rw [g]; exact hp.sp_stk }

/-- A state in the middle of `blocks` satisfies the precondition, with the
arguments of the state on entry. -/
theorem BInv.mid {s₀ s : State} {F : Nat → Nat} {i : Nat} (hp : BPre s₀) (h : BInv s₀ F i s) :
    BPre s ∧ ∀ j < 3, arg s j = arg s₀ j := by
  have ha : ∀ j < 3, arg s j = arg s₀ j := fun j hj => by
    show s.mem.readW (addr (s.gpr .esp) (4 + 4 * j)) 32 = _
    rw [h.esp]; exact hp.arg_same h.frame hj
  exact ⟨hp.congr h.esp h.rd h.wr ha, ha⟩

/-- Two runs of `blocks` from states that satisfy the precondition, with
the same `esp` and arguments, leak the same. The taint analysis checks the
code before and after the pairs of blocks, from taints that it shows the
states to agree on (`rel_check`): `esp`, the pointers `esi` and `edi`, and
the stack arguments; the two runs of `pairs` are related by `Sse2.pairs_rel`,
from states the correctness proof describes, and the states they end in
satisfy the precondition again, with the same arguments (`BInv.mid`). -/
private theorem blocks_rel {a b : State} (ha : BPre a) (hb : BPre b) (hesp : a.gpr .esp = b.gpr .esp)
    (harg : ∀ i < 3, arg a i = arg b i) : RelCT isa (Eq2 a b) blocks (fun _ _ => True) := by
  have est : stp b = stp a := (harg 0 (by decide)).symm
  have ebp : bp b = bp a := (harg 1 (by decide)).symm
  have enb : nb b = nb a := congrArg BitVec.toNat (harg 2 (by decide)).symm
  have tEnd : ∃ h, (VG.X86.taint.check (blocksτ [.esi, .edi] false)
      (.seq (.block atEnd) (.seq (.ite .e (.block []) (.loop body .ne)) (.block (reduce ++ restore)))) h).isSome =
        true := ⟨_, by taint_decide⟩
  rw [blocks_eq]
  refine rel_seqR (rel_check (blocksτ [.esi, .edi, .ecx] true)
      (blocks_agree ha hb hesp harg (rs := []) fun _ h => absurd h List.not_mem_nil) ⟨_, by taint_decide⟩)
    (prologue_ok ha) (prologue_ok hb) fun x₁ y₁ A₁ ⟨F₁, hF₁, I₁, cx₁, cf₁⟩ ⟨F₂, hF₂, I₂, cx₂, cf₂⟩ => ?_
  rw [enb] at cf₂
  refine rel_then (R := VG.X86.Taint.Agree (blocksτ [.esi, .edi] false)) ?_
    fun x₃ y₃ A₃ => rel_checkT A₃ tEnd
  -- The pairs, taken by both runs or by neither.
  refine rel_iteR (b := decide (nb a < 16)) cf₁ cf₂ (fun _ => RelCT.nil fun u v huv => by
    obtain ⟨rfl, rfl⟩ := huv
    exact VG.X86.taint.le_sound (τ := blocksτ [.esi, .edi] false) (by decide) A₁) fun hbq => ?_
  have h16 : 16 ≤ nb a := by simpa using hbq
  refine rel_seqR (rel_taint [] (fun _ h => absurd h List.not_mem_nil) ⟨_, by taint_decide⟩)
    (blockPairsArg_ok ha I₁ cx₁ h16) (blockPairsArg_ok hb I₂ cx₂ (by rw [enb]; exact h16))
    fun x₄ y₄ _ ⟨D₁, P₁⟩ ⟨D₂, P₂⟩ => ?_
  rw [est, ebp, enb] at P₂
  have hpl : 2 * (nb a / 2) ≤ nb a := by omega_using []
  refine ((Sse2.pairs_rel P₁ P₂ (by rw [D₁.esp, D₂.esp]; exact hesp)).wp
    (F₁ := BInv a F₁ (2 * (nb a / 2))) (F₂ := BInv b F₂ (2 * (nb a / 2)))
    fun u v huv => by
      obtain ⟨rfl, rfl⟩ := huv
      exact ⟨blockPairsRun_ok ha hF₁ D₁ P₁ hpl,
        blockPairsRun_ok hb hF₂ D₂ (by rw [est, ebp]; exact P₂) (by rw [enb]; exact hpl)⟩).mono
    (fun _ _ h => h) fun x' y' ⟨_, K₁, K₂⟩ => ?_
  -- The states after the pairs satisfy the precondition, with the same arguments.
  obtain ⟨hx', ax'⟩ := K₁.mid ha
  obtain ⟨hy', ay'⟩ := K₂.mid hb
  refine blocks_agree hx' hy' (by rw [K₁.esp, K₂.esp]; exact hesp)
    (fun i hi => by rw [ax' i hi, ay' i hi]; exact harg i hi) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [K₁.esi, K₂.esi, ebp]
  · rw [K₁.ctx.edi, K₂.ctx.edi, est]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksX86.pre s) :
    ∃ t s', Exec isa blocks s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.blocksX86.post s s' :=
  blocks_correct (BPre.of s hs)

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksX86.pre Proof.Poly1305.blocksX86.pub
    blocks :=
  ct_of fun _ _ h₁ h₂ hp => blocks_rel (BPre.of _ h₁) (BPre.of _ h₂) hp.1 fun i hi => by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
    rcases this with rfl | rfl | rfl
    exacts [hp.2.1, hp.2.2.1, hp.2.2.2]

end VG.Proof.Poly1305.X86
