module

-- separate module: the frame's blocks before the hypertree, apart from its loop

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopCalls
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkDigits

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the blocks between the calls

Untrusted: everything here is checked by Lean. In `Ctx`: the block before
FORS, which parses the digest's indices and sets the lanes' addresses to
layer 0's tree (`fblock_ok`); the block after it, the first layer and the
first XMSS signature's place (`init_ok`); and the block after each layer's
XMSS signature, the next layer's indices (`next_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave var stk fSig)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_store wp_addi wp_mov32i ea_at)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)

variable {L : SL} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The variables -/

theorem var_rw {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) : InRegions (t.rd ++ t.wr) (L.var i) 8 := by
  obtain ⟨r, hr, h⟩ := var_in hc hi; exact ⟨r, List.mem_append_right _ hr, h⟩

theorem var_sep {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : Mem.Sep (L.var i) (64 / 8) (L.var j) (64 / 8) :=
  Offset.sep L.S (by omega) (by rw [show oKgSave = 34080 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)

/-- Bytes apart from the variables. -/
theorem var_disj (hL : L.Ok) {i : Nat} (hi : i < 4) {a : Addr} {l : Nat}
    (h : Region.Disjoint ⟨a, l⟩ ⟨at' L.S (oKgSave + 48), 32⟩) : ∀ r ∈ [(⟨L.var i, 64 / 8⟩ : Region)],
      Region.Disjoint ⟨a, l⟩ r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (var_sub hL hi)

/-- A store to variable `i`. -/
theorem wp_storeVar (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.gpr = t.gpr → t'.mem = t.mem.writeW (L.var i) (t.gpr r) →
      WP isa (.block is) t' Q) :
    WP isa (.block (.store (var i) r :: is)) t Q := by
  refine wp_store (a := L.var i) (by rw [ea_var, hc.rbx]) (var_in hc hi) fun t' g' m' r' w' => k t' ?_ g' m'
  exact hc.of_frame hL r' w' (by rw [g']) (by rw [g']) (fun _ _ _ _ => by rw [g']) (rs := [⟨at' L.S (oKgSave + 48), 32⟩])
    (by
      rw [m']
      refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
      show Region.Contains ⟨L.S + BitVec.ofNat 64 (oKgSave + 48), 32⟩ (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
      rw [show oKgSave = 34080 from rfl]; exact Offset.contains L.S (by omega) (by omega) (by omega))
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact free_vars hL

/-- A load of variable `i`. -/
theorem wp_loadVar {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) {d : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t', Upd t t' d (t.mem.readW (L.var i) 64) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.mem (var i)) :: is)) t Q :=
  wp_movm (a := L.var i) (by rw [ea_var, hc.rbx]) (var_rw hc hi) k

theorem readVar_write {m : Mem} {i j : Nat} (hi : i < 4) (hj : j < 4) (v : BitVec 64) :
    (m.writeW (L.var j) v).readW (L.var i) 64 = if i = j then v else m.readW (L.var i) 64 := by
  split
  · subst_vars; exact Mem.readW_writeW_self64 _ _ _
  · exact Mem.readW_writeW_sep (var_sep hi hj (by assumption)) (by decide)

/-! ## Before FORS -/

/-- The block before FORS. -/
abbrev fblock (p : Params) : List Instr :=
  Impl.SlhDsa.X86_64.Shake.parseIdx p ++ [.mov32 .r10 (.imm 0), .mov .r9 (.mem (var 0))] ++
    Impl.SlhDsa.X86_64.Shake.treeLanes p .r10 .r9 ++
    [.mov .rdi (.reg .rbx), .mov .rsi (.mem (stk fSig)), .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)),
      .mov .rdx (.mem (var 1))]

theorem fblock_nm (p : Params) : (Code.block (fblock p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Code.allInstrs_eq, instrs, fblock, Impl.SlhDsa.X86_64.Shake.parseIdx, Impl.SlhDsa.X86_64.Shake.treeLanes,
    Impl.SlhDsa.X86_64.setField, Impl.SlhDsa.X86_64.setFieldR, List.all_append, List.all_flatMap, List.all_cons,
    List.all_nil]
  split <;> split <;> simp [loadsMxcsr]

/-- The indices of the digest at `oDigest`. -/
abbrev SL.sd (L : SL) (p : Params) (m : Mem) : List Byte × Nat × Nat :=
  splitDigest p (bytesAt m (at' L.S Layout.oDigest) p.m)

theorem fblock_ok {p : Params} (hp : VPar p) (hL : L.Ok) (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (L.sd p t.mem).2.1 →
      t'.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (L.sd p t.mem).2.2 →
      Adr L t'.mem (Proof.SlhDsa.layerTree 0 (L.sd p t.mem).2.1) → t'.gpr .rdi = L.S →
      t'.gpr .rsi = L.sig + BitVec.ofNat 64 p.n → t'.gpr .rdx = BitVec.ofNat 64 (L.sd p t.mem).2.2 →
      mdAt p t'.mem L.S = mdAt p t.mem L.S →
      (∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → l ≤ 2 ^ 64 → bytesAt t'.mem a l = bytesAt t.mem a l) →
      MxEq t t' → Q t') :
    WP isa (.block (fblock p)) t Q := by
  have hn32 := hL.n32
  have hT : (L.sd p t.mem).2.1 < 2 ^ 64 := by
    simp only [SL.sd, splitDigest]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by have := hp.tb; have := hp.tb'; omega))
  refine WP.mono_mx (fblock_nm p) (Q := fun t' => Ctx L g m₀ t' ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ?_
    fun t' ⟨a, b, c, d, e, f, h, i, j⟩ hm => k t' a b c d e f h i j (MxEq.of_eq hm)
  simp only [fblock, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (parse_ok hp hL hc) fun t₁ ⟨hc₁, h0, h1, hf₁⟩ => ?_)
  refine wp_mov32i fun t₂ u₂ => wp_loadVar (hc₁.regs u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (by
    intro e; subst e; revert hr; decide)) (by decide) fun t₃ u₃ => ?_
  have hc₂ : Ctx L g m₀ t₂ := hc₁.regs u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (by intro e; subst e; revert hr; decide)
  have hc₃ : Ctx L g m₀ t₃ := hc₂.regs u₃.rd u₃.wr u₃.mem fun r hr => u₃.other r (by intro e; subst e; revert hr; decide)
  refine WP.block_append (lanes_ok hL hn (j := 0) (T := (L.sd p t.mem).2.1) (by decide) hT hc₃
    (by rw [u₃.other _ (by decide), u₂.gpr]; rfl) (by rw [u₃.gpr, u₂.mem, h0])
    fun t₄ hc₄ hg₄ ha₄ hf₄ => ?_)
  refine wp_mov fun t₅ u₅ => wp_movm (a := L.SP + BitVec.ofNat 64 24)
    (by rw [stk_ea, u₅.other _ (by decide), hg₄ _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), hc₁.rsp]; rfl) (by rw [u₅.rd, u₅.wr]; exact hc₄.inFr (by omega)) fun t₆ u₆ => ?_
  refine wp_addi fun t₇ u₇ => ?_
  have hc₇ : Ctx L g m₀ t₇ := ((hc₄.regs u₅.rd u₅.wr u₅.mem fun r hr => u₅.other r (by
      intro e; subst e; revert hr; decide)).regs u₆.rd u₆.wr u₆.mem fun r hr => u₆.other r (by
      intro e; subst e; revert hr; decide)).regs u₇.rd u₇.wr u₇.mem fun r hr => u₇.other r (by
      intro e; subst e; revert hr; decide)
  refine wp_loadVar hc₇ (by decide) fun t₈ u₈ => WP.block_nil ?_
  have hc₈ : Ctx L g m₀ t₈ := hc₇.regs u₈.rd u₈.wr u₈.mem fun r hr => u₈.other r (by intro e; subst e; revert hr; decide)
  -- the memory
  have hm₈ : t₈.mem = t₄.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have hm₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have dl : ∀ {o l : Nat}, o + l ≤ 65536 → (o + l ≤ 3296 ∨ 12640 ≤ o) → ∀ r ∈ [KeyGen.lanesR L.S],
      Region.Disjoint ⟨at' L.S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Levels.disj_scr L.S (by simp only [Layout.oA]; omega) h₁ (by simp only [Layout.oA]; omega)
  have vk : ∀ i < 4, t₈.mem.readW (L.var i) 64 = t₁.mem.readW (L.var i) 64 := fun i hi => by
    rw [hm₈, Thash4Avx.readW_frame hf₄ (dl (o := oKgSave + 48 + 8 * i) (by rw [show oKgSave = 34080 from rfl]; omega)
      (by rw [show oKgSave = 34080 from rfl]; omega)), hm₃]
  have hsig : ∀ {a : Addr} {l : Nat}, Region.Sub ⟨a, l⟩ L.SIG → l ≤ 2 ^ 64 → bytesAt t₈.mem a l = bytesAt t.mem a l :=
    fun {a l} hs hl => by
      rw [hm₈, bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.sSig.symm.sub_left hs).sub_right (lanesR_scr hL)) hl, hm₃,
        bytesAt_frame hf₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.sSig.symm.sub_left hs).sub_right (hL.scr_sub (by rw [show oKgSave = 34080 from rfl]; omega))) hl]
  refine ⟨hc₈, by rw [vk 0 (by decide)]; exact h0, by rw [vk 1 (by decide)]; exact h1, by rw [hm₈]; exact ha₄,
    by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, hc₄.rbx], ?_,
    by rw [u₈.gpr, show t₇.mem = t₈.mem by rw [u₈.mem], vk 1 (by decide)]; exact h1, ?_, hsig⟩
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.mem, hc₄.pSig, Levels.sx_ofNat (by omega)]
  · show bytesAt t₈.mem (at' L.S Layout.oDigest) p.mdLen = bytesAt t.mem (at' L.S Layout.oDigest) p.mdLen
    have hmd : p.mdLen ≤ 64 := by have := hp.m; have := hp.m64; omega
    rw [hm₈, bytesAt_frame hf₄ (dl (by simp only [show Layout.oDigest = 30304 from rfl]; omega)
        (by simp only [show Layout.oDigest = 30304 from rfl]; omega)) (by omega), hm₃,
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Levels.disj_scr L.S (by simp only [show Layout.oDigest = 30304 from rfl, show oKgSave = 34080 from rfl]; omega)
          (by simp only [show Layout.oDigest = 30304 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega))
        (by omega)]

/-! ## After FORS -/

/-- The block after FORS. -/
abbrev iblock (p : Params) : List Instr :=
  [.mov32 .rax (.imm 0), .store (var 2) .rax, .mov .rax (.mem (stk fSig)),
    .alu .add .rax (.imm (BitVec.ofNat 32 (p.n + p.forsSigLen))), .store (var 3) .rax]

theorem iblock_nm (p : Params) : (Code.block (iblock p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl

/-- Memory that changed only in the variables. -/
abbrev VarsFrame (L : SL) (m m' : Mem) : Prop := Frame [⟨at' L.S (oKgSave + 48), 32⟩] m m'

theorem varsFrame_write {m : Mem} {i : Nat} (hi : i < 4) (v : BitVec 64) : VarsFrame L m (m.writeW (L.var i) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_
  show Region.Contains ⟨L.S + BitVec.ofNat 64 (oKgSave + 48), 32⟩ (L.S + BitVec.ofNat 64 (oKgSave + 48 + 8 * i)) 8
  rw [show oKgSave = 34080 from rfl]; exact Offset.contains L.S (by omega) (by omega) (by omega)

theorem init_ok {p : Params} (hL : L.Ok) (hfl : p.n + p.forsSigLen < 2 ^ 31) {t : State} (hc : Ctx L g m₀ t)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem.readW (L.var 2) 64 = BitVec.ofNat 64 0 →
      t'.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen) →
      (∀ i < 2, t'.mem.readW (L.var i) 64 = t.mem.readW (L.var i) 64) → VarsFrame L t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (.block (iblock p)) t Q := by
  refine WP.mono_mx (iblock_nm p) (Q := fun t' => Ctx L g m₀ t' ∧ _ ∧ _ ∧ _ ∧ _) ?_
    fun t' ⟨a, b, c, d, e⟩ hm => k t' a b c d e (MxEq.of_eq hm)
  refine wp_mov32i fun t₁ u₁ => ?_
  have hc₁ : Ctx L g m₀ t₁ := hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r (by intro e; subst e; revert hr; decide)
  refine wp_storeVar hL hc₁ (by decide) fun t₂ hc₂ g₂ m₂ => ?_
  refine wp_movm (a := L.SP + BitVec.ofNat 64 24) (by rw [stk_ea, g₂, hc₁.rsp]; rfl) (hc₂.inFr (by omega))
    fun t₃ u₃ => wp_addi fun t₄ u₄ => ?_
  have hc₄ : Ctx L g m₀ t₄ := (hc₂.regs u₃.rd u₃.wr u₃.mem fun r hr => u₃.other r (by
      intro e; subst e; revert hr; decide)).regs u₄.rd u₄.wr u₄.mem fun r hr => u₄.other r (by
      intro e; subst e; revert hr; decide)
  refine wp_storeVar hL hc₄ (by decide) fun t₅ hc₅ g₅ m₅ => WP.block_nil ?_
  have hm₄ : t₄.mem = t₂.mem := by rw [u₄.mem, u₃.mem]
  have hax : t₄.gpr .rax = L.sig + BitVec.ofNat 64 (p.n + p.forsSigLen) := by
    rw [u₄.gpr, u₃.gpr, hc₂.pSig, Levels.sx_ofNat hfl]
  refine ⟨hc₅, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [m₅, hm₄, readVar_write (by decide) (by decide), ite_eq_right (by decide), m₂, readVar_write (by decide) (by decide),
      ite_eq_left rfl, u₁.gpr]; rfl
  · rw [m₅, readVar_write (by decide) (by decide), ite_eq_left rfl, hax]
  · rw [m₅, hm₄, readVar_write (by omega) (by decide), ite_eq_right (by omega), m₂, readVar_write (by omega) (by decide),
      ite_eq_right (by omega), u₁.mem]
  · rw [m₅, hm₄, m₂, u₁.mem]
    exact (varsFrame_write (by decide) _).trans (varsFrame_write (by decide) _)

/-! ## After a layer -/

/-- The block after a layer's XMSS signature. -/
abbrev nblock (p : Params) : List Instr :=
  [.mov .rax (.mem (var 3)), .alu .add .rax (.imm (BitVec.ofNat 32 p.xmssSigLen)), .store (var 3) .rax,
    .mov .rax (.mem (var 0)), .mov .rcx (.reg .rax), .alu .and .rcx (.imm (BitVec.ofNat 32 (2 ^ p.hp - 1))),
    .store (var 1) .rcx, .shift .shr .rax p.hp, .store (var 0) .rax,
    .mov .rax (.mem (var 2)), .alu .add .rax (.imm 1), .store (var 2) .rax,
    .alu .cmp .rax (.imm (BitVec.ofNat 32 p.d))]

theorem nblock_nm (p : Params) : (Code.block (nblock p) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl

theorem and_mask64 {T hp : Nat} (hT : T < 2 ^ 64) (hp9 : hp ≤ 9) :
    BitVec.ofNat 64 T &&& (BitVec.ofNat 32 (2 ^ hp - 1)).signExtend 64 = BitVec.ofNat 64 (T % 2 ^ hp) := by
  have hp' : 2 ^ hp - 1 < 2 ^ 31 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp9; omega
  apply BitVec.eq_of_toNat_eq
  rw [Levels.sx_ofNat hp', BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hT, Nat.mod_eq_of_lt (show 2 ^ hp - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hT)]

theorem shr64 {T k : Nat} (hT : T < 2 ^ 64) : BitVec.ofNat 64 T >>> k = BitVec.ofNat 64 (T >>> k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hT)]

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  show s.zf.map (!·) = _; rw [h]; rfl

theorem next_ok {p : Params} (hL : L.Ok) (hp9 : 1 ≤ p.hp ∧ p.hp ≤ 9) (hd : p.d < 2 ^ 31) (hxs : p.xmssSigLen < 2 ^ 31)
    {t : State} (hc : Ctx L g m₀ t) {j T o : Nat} (hj : j + 1 < 2 ^ 31) (hT : T < 2 ^ 64)
    (h0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 T) (h2 : t.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j)
    (h3 : t.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 o) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (T >>> p.hp) →
      t'.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (T % 2 ^ p.hp) →
      t'.mem.readW (L.var 2) 64 = BitVec.ofNat 64 (j + 1) →
      t'.mem.readW (L.var 3) 64 = L.sig + BitVec.ofNat 64 (o + p.xmssSigLen) →
      isa.eval .ne t' = some (decide (j + 1 ≠ p.d)) → VarsFrame L t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (.block (nblock p)) t Q := by
  refine WP.mono_mx (nblock_nm p) (Q := fun t' => Ctx L g m₀ t' ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ?_
    fun t' ⟨a, b, c, d, e, f, h⟩ hm => k t' a b c d e f h (MxEq.of_eq hm)
  have nc : ∀ {r : Reg}, r = .rax ∨ r = .rcx → ∀ x ∈ calleeSaved, x ≠ r := fun {r} hr x hx => by
    rcases hr with rfl | rfl <;> (intro e; subst e; revert hx; decide)
  refine wp_loadVar hc (by decide) fun t₁ u₁ => wp_addi fun t₂ u₂ => ?_
  have hc₂ : Ctx L g m₀ t₂ := (hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r (nc (.inl rfl) r hr)).regs
    u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (nc (.inl rfl) r hr)
  refine wp_storeVar hL hc₂ (by decide) fun t₃ hc₃ g₃ m₃ => ?_
  refine wp_loadVar hc₃ (by decide) fun t₄ u₄ => wp_mov fun t₅ u₅ => VG.Proof.SlhDsa.X86_64.wp_andi fun t₆ u₆ => ?_
  have hc₆ : Ctx L g m₀ t₆ := ((hc₃.regs u₄.rd u₄.wr u₄.mem fun r hr => u₄.other r (nc (.inl rfl) r hr)).regs
    u₅.rd u₅.wr u₅.mem fun r hr => u₅.other r (nc (.inr rfl) r hr)).regs u₆.rd u₆.wr u₆.mem
      fun r hr => u₆.other r (nc (.inr rfl) r hr)
  refine wp_storeVar hL hc₆ (by decide) fun t₇ hc₇ g₇ m₇ => ?_
  refine Levels.wp_shr (n := p.hp) hp9.1 (by omega) fun t₈ u₈ => ?_
  have hc₈ : Ctx L g m₀ t₈ := hc₇.regs u₈.rd u₈.wr u₈.mem fun r hr => u₈.other r (nc (.inl rfl) r hr)
  refine wp_storeVar hL hc₈ (by decide) fun t₉ hc₉ g₉ m₉ => ?_
  refine wp_loadVar hc₉ (by decide) fun t₁₀ u₁₀ => wp_addi fun t₁₁ u₁₁ => ?_
  have hc₁₁ : Ctx L g m₀ t₁₁ := (hc₉.regs u₁₀.rd u₁₀.wr u₁₀.mem fun r hr => u₁₀.other r (nc (.inl rfl) r hr)).regs
    u₁₁.rd u₁₁.wr u₁₁.mem fun r hr => u₁₁.other r (nc (.inl rfl) r hr)
  refine wp_storeVar hL hc₁₁ (by decide) fun t₁₂ hc₁₂ g₁₂ m₁₂ => ?_
  refine Levels.wp_cmpi fun t₁₃ g₁₃ m₁₃ r₁₃ w₁₃ z₁₃ => WP.block_nil ?_
  have hc₁₃ : Ctx L g m₀ t₁₃ := hc₁₂.regs r₁₃ w₁₃ m₁₃ fun r _ => by rw [g₁₃]
  -- the values
  have hrax₂ : t₂.gpr .rax = L.sig + BitVec.ofNat 64 (o + p.xmssSigLen) := by
    rw [u₂.gpr, u₁.gpr, h3, Levels.sx_ofNat hxs, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have hm₆ : t₆.mem = t₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hm₁₁ : t₁₁.mem = t₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  have r0 : t₃.mem.readW (L.var 0) 64 = BitVec.ofNat 64 T := by
    rw [m₃, readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₂, h0]
  have r2 : t₉.mem.readW (L.var 2) 64 = BitVec.ofNat 64 j := by
    rw [m₉, readVar_write (by decide) (by decide), ite_eq_right (by decide), u₈.mem, m₇,
      readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₆, m₃, readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₂, h2]
  have hrax₄ : t₄.gpr .rax = BitVec.ofNat 64 T := by rw [u₄.gpr, r0]
  have hrcx₆ : t₆.gpr .rcx = BitVec.ofNat 64 (T % 2 ^ p.hp) := by
    rw [u₆.gpr, u₅.gpr, hrax₄, and_mask64 hT hp9.2]
  have hrax₈ : t₈.gpr .rax = BitVec.ofNat 64 (T >>> p.hp) := by
    rw [u₈.gpr, g₇, u₆.other _ (by decide), u₅.other _ (by decide), hrax₄, shr64 hT]
  have hrax₁₁ : t₁₁.gpr .rax = BitVec.ofNat 64 (j + 1) := by
    rw [u₁₁.gpr, u₁₀.gpr, r2, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 by decide,
      BitVec.ofNat_add_ofNat]
  have hrax₁₂ : t₁₂.gpr .rax = BitVec.ofNat 64 (j + 1) := by rw [g₁₂, hrax₁₁]
  refine ⟨hc₁₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₃, m₁₂, readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₁₁, m₉,
      readVar_write (by decide) (by decide), ite_eq_left rfl, hrax₈]
  · rw [m₁₃, m₁₂, readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₁₁, m₉,
      readVar_write (by decide) (by decide), ite_eq_right (by decide), u₈.mem, m₇, readVar_write (by decide) (by decide),
      ite_eq_left rfl, hrcx₆]
  · rw [m₁₃, m₁₂, readVar_write (by decide) (by decide), ite_eq_left rfl, hrax₁₁]
  · rw [m₁₃, m₁₂, readVar_write (by decide) (by decide), ite_eq_right (by decide), hm₁₁, m₉,
      readVar_write (by decide) (by decide), ite_eq_right (by decide), u₈.mem, m₇, readVar_write (by decide) (by decide),
      ite_eq_right (by decide), hm₆, m₃, readVar_write (by decide) (by decide), ite_eq_left rfl, hrax₂]
  · rw [eval_ne z₁₃, hrax₁₂, Levels.sx_ofNat hd]
    congr 1
    by_cases e : j + 1 = p.d
    · rw [e]; simp
    · have h1 : (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d == 0) = false := by
        rw [beq_eq_false_iff_ne, ne_eq]
        intro h; apply e
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.d) (by omega),
          Nat.mod_eq_of_lt (a := j + 1) (by omega), show (0 : BitVec 64).toNat = 0 from rfl] at h'
        omega
      rw [h1]; simp [e]
  · rw [m₁₃, m₁₂, hm₁₁, m₉, u₈.mem, m₇, hm₆, m₃, hm₂]
    exact ((((varsFrame_write (by decide) _).trans (varsFrame_write (by decide) _)).trans
      (varsFrame_write (by decide) _)).trans (varsFrame_write (by decide) _))

end VG.Proof.SlhDsa.X86_64.SignTop
