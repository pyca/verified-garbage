import VerifiedGarbage.Proof.Cast5.X86_64.Round
import VerifiedGarbage.Proof.Cast5.Memory

/-!
# CAST5 on x86-64: a block

The rounds of a block, three at a time (`group`), and the block functions
`encryptBlock` and `decryptBlock`: from the block at `rdx` to its encryption
or decryption there.
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)
open VG.Proof.MlKem.X86_64 (Keep sx_ofNat WP.keep writesOnly wp_countdown)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem s1234_length : s1234.length = 512 := table_length _ _ _ _

/-- What every round of a block reads: the subkeys `k` at `rdi`, the table, and
16 bytes of working space at `r8`, apart from both. -/
structure Ctx (s : State) (k : Spec.Cast5.Schedule) : Prop where
  sched : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  w : InRegions s.wr (s.gpr .r8) 16
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234
  dsched : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r8, 16⟩
  dtab : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r8, 16⟩
  fitS : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64

/-- The context holds in a state that differs only in registers other than
`rdi` and `r8` and in the working space. -/
theorem Ctx.transfer {s u : State} {k : Spec.Cast5.Schedule} (h : Ctx s k)
    (hdi : u.gpr .rdi = s.gpr .rdi) (h8 : u.gpr .r8 = s.gpr .r8) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hsy : u.syms = s.syms) (hf : Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem) :
    Ctx u k := by
  refine ⟨?_, fun j hj => ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hwr, hdi]; exact h.sched
  · rw [hdi, hf.readW (r := ⟨s.gpr .rdi, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact h.dsched)
      (by decide)]
    exact h.key j hj
  · rw [hwr, h8]; exact h.w
  · unfold Readable; rw [hrd, hwr, hsy]; exact h.tab
  · have hi' : i < 512 := by rw [s1234_length] at hi; exact hi
    rw [hsy, hf.readW (r := ⟨s.syms s1234Sym, 4096⟩)
      (Offset.contains_base _ (by omega) (by omega))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact h.dtab)
      (by decide)]
    exact h.held i hi
  · rw [hdi, h8]; exact h.dsched
  · rw [hsy, h8]; exact h.dtab
  · rw [hdi]; exact h.fitS
  · rw [hsy]; exact h.fitT

/-- Round `i`'s precondition, with `r12` at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {k : Spec.Cast5.Schedule} (h : Ctx s k) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : s.gpr .r12 = s.gpr .rdi + BitVec.ofNat 64 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (hbx : s.gpr .rbx = l.setWidth 64) (hbp : s.gpr .rbp = r.setWidth 64) :
    RoundPre s (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have h64 : s.gpr .r12 + BitVec.ofNat 64 64 = s.gpr .rdi + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h12, add_ofNat_add]; congr 2; omega
  refine ⟨hbx, hbp, ?_, ?_, ?_, ?_, h.w, h.tab, h.held⟩
  · rw [h12]; exact CallLay.inRegions_sub h.sched (by omega) (by decide)
  · rw [h12]; exact h.key _ (by omega)
  · rw [h64]; exact CallLay.inRegions_sub h.sched (by omega) (by decide)
  · rw [h64]; exact h.key _ (by omega)

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (k : Spec.Cast5.Schedule) (lr : Spec.Cast5.Word × Spec.Cast5.Word)
    (u : State) : Prop where
  bx : u.gpr .rbx = lr.1.setWidth 64
  bp : u.gpr .rbp = lr.2.setWidth 64
  ctx : Ctx u k
  same : ∀ q, q ∉ roundRegs → q ≠ .r13 → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame [⟨s.gpr .r8, 16⟩] s.mem u.mem

theorem round_step {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s k (Spec.Cast5.round k i lr) v ∧
      v.gpr .r12 = (if up then u.gpr .r12 + 4 else u.gpr .r12 - 4) ∧ v.gpr .r13 = u.gpr .r13 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi h12 h.bx h.bp)) fun v ⟨vbx, vbp, v12, vf, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr hq
  have h8 : u.gpr .r8 = s.gpr .r8 := h.same .r8 (by decide) (by decide)
  refine ⟨⟨vbx, ?_, h.ctx.transfer (g .rdi (by decide)) (g .r8 (by decide)) vrd vwr vsy vf,
    fun q hq h13 => (g q hq).trans (h.same q hq h13), vrd.trans h.rd, vwr.trans h.wr, vsy.trans h.syms,
    h.frame.trans (by rw [← h8]; exact vf)⟩, v12, g .r13 (by decide)⟩
  rw [vbp, fT_eq ht hti]
  rfl

theorem RInv.setReg {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {q : Reg} (hq : q = .r13) (x : BitVec 64) : RInv s k lr (u.setReg q x) := by
  subst hq
  refine ⟨h.bx, h.bp, h.ctx.transfer rfl rfl rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, h.rd, h.wr,
    h.syms, h.frame⟩
  rw [gpr_setReg_of_ne _ _ h13]; exact h.same q hq h13

theorem RInv.setFlags {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (a b c d : Option Bool) : RInv s k lr (u.setFlags a b c d) :=
  ⟨h.bx, h.bp, h.ctx.transfer rfl rfl rfl rfl rfl (Frame.refl _ _), h.same, h.rd, h.wr, h.syms, h.frame⟩

/-- `sub r13, 1`. -/
theorem countDown_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) :
    WP isa (.block [.alu .sub .r13 (imm 1)]) u fun v => RInv s k lr v ∧ v.gpr .r12 = u.gpr .r12 ∧
      v.gpr .r13 = u.gpr .r13 - 1 ∧ v.zf = some (u.gpr .r13 - 1 == 0) := by
  xrun [imm, sx_ofNat (show 1 < 2 ^ 31 by decide)]
  exact ⟨(h.setFlags _ _ _ _).setReg rfl _, rfl, rfl⟩

theorem four : (4 : Addr) = BitVec.ofNat 64 4 := rfl

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {g : Nat} (hg : 3 * g + 3 ≤ 16) (h : RInv s k (encFold k (3 * g) lr) u)
    (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (12 * g)) :
    WP isa (group true) u fun v => RInv s k (encFold k (3 * (g + 1)) lr) v ∧
      v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (12 * (g + 1)) ∧ v.gpr .r13 = u.gpr .r13 - 1 ∧
      v.zf = some (u.gpr .r13 - 1 == 0) := by
  have hdi : ∀ v : State, RInv s k (encFold k (3 * g) lr) u → (∀ lr', RInv s k lr' v → v.gpr .rdi = u.gpr .rdi) :=
    fun v hu lr' hv => (hv.same .rdi (by decide) (by decide)).trans (hu.same .rdi (by decide) (by decide)).symm
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega) (by omega)
    (by rw [h12]; congr 2; omega) true) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega) (by omega)
    (by rw [a₁, ite_eq_left rfl, h12, hdi v₁ h _ h₁, four, add_ofNat_add]; congr 2; omega) true)
    fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega) (by omega)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₂ h _ h₂, four, add_ofNat_add, add_ofNat_add]; congr 2; omega)
    true) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₄ h _ h₄, four, add_ofNat_add, add_ofNat_add,
      add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega]

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {n m : Nat} (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0) (h : RInv s k (decFold k n m lr) u)
    (h12 : u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (n - m - 1))) :
    WP isa (group false) u fun v => RInv s k (decFold k n (m + 3) lr) v ∧
      v.gpr .r12 = u.gpr .r12 - 12 ∧ v.gpr .r13 = u.gpr .r13 - 1 ∧
      v.zf = some (u.gpr .r13 - 1 == 0) := by
  have hdi : ∀ v : State, (∀ lr', RInv s k lr' v → v.gpr .rdi = u.gpr .rdi) :=
    fun v lr' hv => (hv.same .rdi (by decide) (by decide)).trans (h.same .rdi (by decide) (by decide)).symm
  have sub4 (x : Addr) (a : Nat) (ha : 4 ≤ a) :
      x + BitVec.ofNat 64 a - 4 = x + BitVec.ofNat 64 (a - 4) := by
    rw [show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_sub _ ha]
  unfold group
  simp only [Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (round_step h (t := 3) (i := n - m) (by decide) (by omega) (by omega)
    h12 false) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := n - m - 1) (by decide) (by omega) (by omega)
    (by rw [a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₁ _ h₁, sub4 _ _ (by omega)]; congr 2; omega)
    false) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 1) (i := n - m - 2) (by decide) (by omega) (by omega)
    (by rw [a₂, ite_eq_right Bool.false_ne_true, a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₂ _ h₂,
      sub4 _ _ (by omega), sub4 _ _ (by omega)]; congr 2; omega) false) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega,
      show n - (m + 2) = n - m - 2 by omega]
    exact h₄
  · rw [a₄, a₃, a₂, a₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl

/-- What a block needs: the context, `n` rounds in `rsi`, and the block at
`rdx`, apart from the working space. -/
structure BPre (s : State) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s k
  nv : n = 12 ∨ n = 16
  rsi : s.gpr .rsi = BitVec.ofNat 64 n
  data : InRegions s.wr (s.gpr .rdx) 8

theorem bswap32_eq (x : BitVec 32) : bswap32 x = byteRev32 x := rfl

/-- The block loaded, `r12` at the first subkeys, and the count of groups. -/
theorem blockStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.mov .r12 (.reg .rdi)] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx))) u ∧
      u.gpr .r12 = u.gpr .rdi ∧ u.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.zf = some (decide (n = 16)) := by
  have hd0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega)
      (by decide) |>.imp fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  have hd4 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)
  unfold load groups
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, h.rsi, execShift, List.cons_append, List.nil_append,
    sx_ofNat (show 16 < 2 ^ 31 by decide)]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .rdx)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ ?_ rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, rfl, rfl, rfl,
    Frame.refl _ _⟩, ?_, ?_⟩
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · have h1 : q ≠ .r12 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .rbp := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .rbx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_setReg, h13, h1, h2, h3, ite_false]
  · rcases h.nv with rfl | rfl <;> decide
  · rcases h.nv with rfl | rfl <;> decide

/-- `(Rₙ, Lₙ)` stored, then on to the next block. -/
theorem store_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions u.wr (u.gpr .rdx) 8) :
    WP isa (.block store) u fun v =>
      v.mem = (u.mem.writeW (u.gpr .rdx) (byteRev32 lr.2)).writeW (u.gpr .rdx + BitVec.ofNat 64 4)
        (byteRev32 lr.1) ∧
      v.gpr .rdx = u.gpr .rdx + 8 ∧ v.gpr .rcx = u.gpr .rcx - 1 ∧ v.zf = some (u.gpr .rcx - 1 == 0) ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms ∧
      (∀ q, q ≠ .rbx → q ≠ .rbp → q ≠ .rdx → q ≠ .rcx → v.gpr q = u.gpr q) := by
  have hd0 : InRegions u.wr (u.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := hd
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega⟩
  have hd4 : InRegions u.wr (u.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := hd
    exact ⟨g, hg, CallLay.contains_trans hc (by omega) (by decide)⟩
  have hbx := h.bx
  have hbp := h.bp
  unfold store
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, hbx, hbp, setWidth_setWidth_32, bswap32_eq,
    sx_ofNat (show 8 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide)]
  refine ⟨rfl, rfl, rfl, rfl, fun q h1 h2 h3 h4 => ?_⟩
  simp only [h1, h2, h3, h4, ite_false]

/-- `cmp rsi, 16`. -/
theorem cmp16_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {n : Nat} (hn : n = 12 ∨ n = 16) (hsi : u.gpr .rsi = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .rsi (imm 16)]) u fun v => RInv s k lr v ∧ v.gpr = u.gpr ∧
      v.zf = some (decide (n = 16)) := by
  xrun [imm, hsi, sx_ofNat (show 16 < 2 ^ 31 by decide)]
  exact ⟨h.setFlags _ _ _ _, by rcases hn with rfl | rfl <;> decide⟩

/-- What a block function does. -/
def BPost (s : State) (out : Spec.Cast5.Block) (v : State) : Prop :=
  Spec.Cast5.blockAt v.mem (s.gpr .rdx) = out ∧
  Frame [⟨s.gpr .rdx, 8⟩, ⟨s.gpr .r8, 16⟩] s.mem v.mem ∧
  v.gpr .rdx = s.gpr .rdx + 8 ∧ v.gpr .rcx = s.gpr .rcx - 1 ∧ v.zf = some (s.gpr .rcx - 1 == 0) ∧
  v.rd = s.rd ∧ v.wr = s.wr ∧ v.syms = s.syms ∧
  (∀ q, q ∉ roundRegs → q ≠ .r13 → q ≠ .rdx → q ≠ .rcx → v.gpr q = s.gpr q)

/-- The store at the end of a block, from the halves `lr` after its rounds. -/
theorem finish_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions s.wr (s.gpr .rdx) 8) :
    WP isa (.block store) u (BPost s (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have hdx : u.gpr .rdx = s.gpr .rdx := h.same .rdx (by decide) (by decide)
  have hcx : u.gpr .rcx = s.gpr .rcx := h.same .rcx (by decide) (by decide)
  have h8 : u.gpr .r8 = s.gpr .r8 := h.same .r8 (by decide) (by decide)
  refine WP.mono (store_ok h (by rw [h.wr, hdx]; exact hd)) fun v ⟨vm, vdx, vcx, vz, vrd, vwr, vsy, vg⟩ => ?_
  refine ⟨?_, ?_, by rw [vdx, hdx], by rw [vcx, hcx], by rw [vz, hcx], vrd.trans h.rd, vwr.trans h.wr,
    vsy.trans h.syms, fun q hq h13 hdq hcq => ?_⟩
  · rw [vm, hdx, blockAt_write]
  · rw [vm, hdx]
    have c0 : Region.Contains ⟨s.gpr .rdx, 8⟩ (s.gpr .rdx) (32 / 8) := by
      simp [Region.Contains]
    refine (Frame.writeW (Frame.writeW (h.frame.mono fun r hr => ?_) List.mem_cons_self _ c0)
      List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    exact .inr hr
  · rw [vg q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) hdq hcq]
    exact h.same q hq h13

theorem encryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa encryptBlock s
      (BPost s (Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) := by
  set_option linter.unusedVariables false in
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ 3 * (n / 4) ≤ 12 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (blockStart_ok h) fun u ⟨hu, u12, u13, _⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r13) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g v => RInv s k (encFold k (3 * g) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) v ∧
      v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (12 * g))
    (fun g hg v ⟨hv, h12⟩ _ => WP.mono (groupEnc_ok (by omega) hv h12) fun w ⟨hw, w12, w13, wz⟩ =>
      ⟨⟨hw, w12⟩, w13, wz⟩)
    (fun _ h => h) ⟨hu, by rw [u12, Nat.mul_zero, BitVec.add_zero]⟩ u13) fun v ⟨hv, v12⟩ => ?_)
  have hsi : v.gpr .rsi = BitVec.ofNat 64 n := (hv.same .rsi (by decide) (by decide)).trans h.rsi
  refine WP.seq (WP.mono (cmp16_ok hv h.nv hsi) fun w ⟨hw, wg, wz⟩ => ?_)
  have w12 : w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (12 * (n / 4 + 1)) := by rw [wg]; exact v12
  refine WP.seq (WP.ite (decide (n = 16)) wz (fun h16 => ?_) (fun h16 => ?_))
  · have hn : n = 16 := of_decide_eq_true h16
    have w12' : w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (4 * (16 - 1)) := by
      rw [w12, hn]
    refine WP.mono (round_step hw (t := 1) (i := 16) (by decide) (by decide) (by decide) w12' true)
      fun x ⟨hx, _, _⟩ => ?_
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock
          ((Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .rdx))))).2,
          (Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .rdx))))).1) := by
      rw [encryptBlock_eq, hn, show 3 * (16 / 4 + 1) = 15 from rfl, show 16 = 15 + 1 from rfl,
        encFold_succ]
    rw [e]
    exact finish_ok hx h.data
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock
          ((encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))).2,
          (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))).1) := by
      rw [encryptBlock_eq, hn]
    rw [e]
    exact WP.block_nil (finish_ok hw h.data)

/-- The block loaded, `r12` at the last round's subkeys, and the count of groups. -/
theorem decStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.mov .r12 (.reg .rsi), .shift .shl .r12 2, .alu .add .r12 (.reg .rdi),
        .alu .sub .r12 (imm 4)] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx))) u ∧
      u.gpr .r12 = u.gpr .rdi + BitVec.ofNat 64 (4 * (n - 1)) ∧ u.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.zf = some (decide (n = 16)) := by
  have hd0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega)
      (by decide) |>.imp fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  have hd4 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 4) 4 := by
    obtain ⟨g, hg, hc⟩ := h.data
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)
  unfold load groups
  xrun [VG.Proof.Cast5.X86_64.ea_at, imm, hd0, hd4, h.rsi, execShift, List.cons_append, List.nil_append,
    sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 4 < 2 ^ 31 by decide)]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .rdx)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ ?_ rfl rfl rfl (Frame.refl _ _), fun q hq h13 => ?_, rfl, rfl, rfl,
    Frame.refl _ _⟩, ?_, ?_⟩
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_true, ite_false, hdec, bswap32_eq]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · simp only [gpr_setFlags, gpr_setReg, reduceCtorEq, ite_false]
  · have h1 : q ≠ .r12 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .rbp := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .rbx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_setReg, h13, h1, h2, h3, ite_false]
  · rcases h.nv with rfl | rfl <;>
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      omega
  · rcases h.nv with rfl | rfl <;> decide

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

theorem decryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa decryptBlock s
      (BPost s (Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)))) := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases h.nv with rfl | rfl <;> decide
  -- The block's halves.
  obtain ⟨lr, hlr⟩ : ∃ lr, Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) = lr := ⟨_, rfl⟩
  unfold decryptBlock
  refine WP.seq (WP.mono (decStart_ok h) fun u ⟨hu, u12, u13, uz⟩ => ?_)
  rw [hlr] at hu
  -- Round 16 first, if there are 16.
  have first : WP isa (.ite .e (round 1 false) (.block [])) u fun v =>
      RInv s k (decFold k n (n % 3) lr) v ∧ v.gpr .r12 = v.gpr .rdi + BitVec.ofNat 64 (4 * (n - n % 3 - 1)) ∧
      v.gpr .r13 = BitVec.ofNat 64 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) uz (fun h16 => ?_) (fun h16 => ?_)
    · have hn : n = 16 := of_decide_eq_true h16
      refine WP.mono (round_step hu (t := 1) (i := n) (by decide) (by rw [hn]) (by omega)
        (by rw [u12]) false) fun x ⟨hx, x12, x13⟩ => ?_
      have hdi : x.gpr .rdi = u.gpr .rdi :=
        (hx.same .rdi (by decide) (by decide)).trans (hu.same .rdi (by decide) (by decide)).symm
      have hd : decFold k n (n % 3) lr = Spec.Cast5.round k n lr := by
        rw [hn, show 16 % 3 = 0 + 1 from rfl, decFold_succ, decFold_zero, Nat.sub_zero]
      refine ⟨(by rw [hd]; exact hx), ?_, x13.trans u13⟩
      rw [x12, ite_eq_right Bool.false_ne_true, u12, hdi, hn, four, Offset.add_ofNat_sub _ (by decide)]
    · have hn : n = 12 := by
        rcases h.nv with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false h16)
      have hd : decFold k n (n % 3) lr = lr := by rw [hn, show 12 % 3 = 0 from rfl, decFold_zero]
      refine WP.block_nil ⟨(by rw [hd]; exact hu), ?_, u13⟩
      rw [u12, hn]
  refine WP.seq (WP.mono first fun v ⟨hv, v12, v13⟩ => ?_)
  -- Then the groups of three.
  refine WP.seq (WP.mono (wp_countdown (cnt := .r13) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => RInv s k (decFold k n (n % 3 + 3 * g) lr) w ∧
      (n % 3 + 3 * g < n → w.gpr .r12 = w.gpr .rdi + BitVec.ofNat 64 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, w12⟩ _ => WP.mono (groupDec_ok (m := n % 3 + 3 * g) (by omega) (by
        rcases h.nv with rfl | rfl <;> decide) (by omega) hw (w12 (by omega)))
      fun x ⟨hx, x12, x13, xz⟩ =>
        ⟨⟨(show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega) ▸ hx, fun hlt => ?_⟩, x13, xz⟩)
    (fun _ h => h) ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact v12⟩
    v13) fun w ⟨hw, _⟩ => ?_)
  · have hdi : x.gpr .rdi = w.gpr .rdi :=
      (hx.same .rdi (by decide) (by decide)).trans (hw.same .rdi (by decide) (by decide)).symm
    rw [x12, w12 (by omega), hdi, show (12 : Addr) = BitVec.ofNat 64 12 from rfl,
      Offset.add_ofNat_sub _ (by omega)]
    congr 2
    omega
  · rw [hG.2.2.1] at hw
    have e : Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .rdx)) =
        Spec.Cast5.encodeBlock ((decFold k n n lr).2, (decFold k n n lr).1) := by
      rw [decryptBlock_eq, hlr]
    rw [e]
    exact finish_ok hw h.data

end VG.Proof.Cast5.X86_64
