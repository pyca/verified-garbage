import VerifiedGarbage.Proof.Cast5.AArch64.Round
import VerifiedGarbage.Proof.Cast5.Memory

/-!
# CAST5 on AArch64: a block

The rounds of a block, three at a time (`group`), and the block functions
`encryptBlock` and `decryptBlock`: from the block at `x2` to its encryption
or decryption there.
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym)
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem s1234_length : s1234.length = 512 := table_length _ _ _ _

/-- What every round of a block reads: the subkeys `k` at `x0` and the table. -/
structure Ctx (s : State) (k : Spec.Cast5.Schedule) : Prop where
  sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  tab : Readable s (s.syms s1234Sym)
  held : Held s.mem (s.syms s1234Sym) s1234

theorem Ctx.transfer {s u : State} {k : Spec.Cast5.Schedule} (h : Ctx s k)
    (h0 : u.gpr .x0 = s.gpr .x0) (hm : u.mem = s.mem) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsy : u.syms = s.syms) : Ctx u k :=
  ⟨by rw [hrd, hwr, h0]; exact h.sched, fun j hj => by rw [h0, hm]; exact h.key j hj,
    by unfold Readable; rw [hrd, hwr, hsy]; exact h.tab, by rw [hm, hsy]; exact h.held⟩

/-- Round `i`'s precondition, with `x12` at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {k : Spec.Cast5.Schedule} (h : Ctx s k) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : s.gpr .x12 = s.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (h5 : s.gpr .x5 = l.setWidth 64) (h6 : s.gpr .x6 = r.setWidth 64) :
    RoundPre s (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have h64 : s.gpr .x12 + BitVec.ofNat 64 64 = s.gpr .x0 + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h12, add_ofNat_add]; congr 2; omega
  refine ⟨h5, h6, ?_, ?_, ?_, ?_, h.tab, h.held⟩
  · rw [h12]; exact CallLay.inRegions_sub h.sched (by omega) (by decide)
  · rw [h12]; exact h.key _ (by omega)
  · rw [h64]; exact CallLay.inRegions_sub h.sched (by omega) (by decide)
  · rw [h64]; exact h.key _ (by omega)

/-- The registers a block writes. -/
def blockRegs : List Reg := roundRegs ++ [.x7, .x8]

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (k : Spec.Cast5.Schedule) (lr : Spec.Cast5.Word × Spec.Cast5.Word)
    (u : State) : Prop where
  x5 : u.gpr .x5 = lr.1.setWidth 64
  x6 : u.gpr .x6 = lr.2.setWidth 64
  ctx : Ctx u k
  same : ∀ q, q ∉ blockRegs → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  mem : u.mem = s.mem

theorem round_step {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (h12 : u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s k (Spec.Cast5.round k i lr) v ∧
      v.gpr .x12 = (if up then u.gpr .x12 + 4 else u.gpr .x12 - 4) ∧ v.gpr .x7 = u.gpr .x7 ∧
      v.gpr .x8 = u.gpr .x8 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi h12 h.x5 h.x6))
    fun v ⟨v5, v6, v12, vm, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr q hq
  refine ⟨⟨v5, ?_, h.ctx.transfer (g .x0 (by decide)) vm vrd vwr vsy,
    fun q hq => (g q fun e => hq (List.mem_append_left _ e)).trans (h.same q hq), vrd.trans h.rd,
    vwr.trans h.wr, vsy.trans h.syms, vm.trans h.mem⟩, v12, g .x7 (by decide), g .x8 (by decide)⟩
  rw [v6, fT_eq ht hti]
  rfl

/-- `sub x7, x7, 1`. -/
theorem countDown_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) :
    WP isa (.block [.subImm .x .x7 .x7 1]) u fun v => RInv s k lr v ∧ v.gpr .x12 = u.gpr .x12 ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  crun
  refine ⟨h.x5, h.x6, h.ctx.transfer rfl rfl rfl rfl rfl, fun q hq => ?_, h.rd, h.wr, h.syms, h.mem⟩
  have : q ≠ .x7 := fun e => hq (by rw [e]; decide)
  rw [gpr_write_of_ne _ _ _ this]
  exact h.same q hq

theorem four : (4 : Addr) = BitVec.ofNat 64 4 := rfl

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {g : Nat} (hg : 3 * g + 3 ≤ 16) (h : RInv s k (encFold k (3 * g) lr) u)
    (h12 : u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (12 * g)) :
    WP isa (group true) u fun v => RInv s k (encFold k (3 * (g + 1)) lr) v ∧
      v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (12 * (g + 1)) ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  have hdi : ∀ v : State, (∀ lr', RInv s k lr' v → v.gpr .x0 = u.gpr .x0) :=
    fun v lr' hv => (hv.same .x0 (by decide)).trans (h.same .x0 (by decide)).symm
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega) (by omega)
    (by rw [h12]; congr 2; omega) true) fun v₁ ⟨h₁, a₁, b₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega) (by omega)
    (by rw [a₁, ite_eq_left rfl, h12, hdi v₁ _ h₁, four, add_ofNat_add]; congr 2; omega) true)
    fun v₂ ⟨h₂, a₂, b₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega) (by omega)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₂ _ h₂, four, add_ofNat_add, add_ofNat_add]
        congr 2; omega)
    true) fun v₃ ⟨h₃, a₃, b₃, c₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h12, hdi v₄ _ h₄, four,
      add_ofNat_add, add_ofNat_add, add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega]

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {n m : Nat} (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0) (h : RInv s k (decFold k n m lr) u)
    (h12 : u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - m - 1))) :
    WP isa (group false) u fun v => RInv s k (decFold k n (m + 3) lr) v ∧
      v.gpr .x12 = u.gpr .x12 - 12 ∧ v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧
      v.gpr .x8 = u.gpr .x8 := by
  have hdi : ∀ v : State, (∀ lr', RInv s k lr' v → v.gpr .x0 = u.gpr .x0) :=
    fun v lr' hv => (hv.same .x0 (by decide)).trans (h.same .x0 (by decide)).symm
  have sub4 (x : Addr) (a : Nat) (ha : 4 ≤ a) :
      x + BitVec.ofNat 64 a - 4 = x + BitVec.ofNat 64 (a - 4) := by
    rw [show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_sub _ ha]
  unfold group
  simp only [Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (round_step h (t := 3) (i := n - m) (by decide) (by omega) (by omega)
    h12 false) fun v₁ ⟨h₁, a₁, b₁, c₁⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := n - m - 1) (by decide) (by omega) (by omega)
    (by rw [a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₁ _ h₁, sub4 _ _ (by omega)]; congr 2; omega)
    false) fun v₂ ⟨h₂, a₂, b₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono (round_step h₂ (t := 1) (i := n - m - 2) (by decide) (by omega) (by omega)
    (by rw [a₂, ite_eq_right Bool.false_ne_true, a₁, ite_eq_right Bool.false_ne_true, h12, hdi v₂ _ h₂,
      sub4 _ _ (by omega), sub4 _ _ (by omega)]; congr 2; omega) false) fun v₃ ⟨h₃, a₃, b₃, c₃⟩ => ?_)
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega,
      show n - (m + 2) = n - m - 2 by omega]
    exact h₄
  · rw [a₄, a₃, a₂, a₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl

/-- What a block needs: the context, `n` rounds in `x1`, and the block at
`x2`. -/
structure BPre (s : State) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s k
  nv : n = 12 ∨ n = 16
  x1 : s.gpr .x1 = BitVec.ofNat 64 n
  data : InRegions s.wr (s.gpr .x2) 8

theorem rev32_eq (x : BitVec 32) : rev32 x = byteRev32 x := rfl

theorem BPre.ld0 {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 4 := by
  obtain ⟨g, hg, hc⟩ := h.data
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)

theorem BPre.ld4 {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 4) 4 := by
  obtain ⟨g, hg, hc⟩ := h.data
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega) (by decide)

theorem groups_x7 {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 64 n >>> 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n / 4 + 1) := by
  rcases hn with rfl | rfl <;> decide

theorem x8_zero {n : Nat} (hn : n = 12 ∨ n = 16) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 16 == 0) = decide (n = 16) := by
  rcases hn with rfl | rfl <;> decide

/-- The block loaded, `x12` at the first subkeys, and the count of groups. -/
theorem blockStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.addImm .x .x12 .x0 0] : List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2))) u ∧
      u.gpr .x12 = u.gpr .x0 ∧ u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
  have hd0 := h.ld0
  have hd4 := h.ld4
  unfold load groups
  crun [hd0, hd4, h.x1]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .x2)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ rfl rfl rfl rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩, BitVec.add_zero _,
    groups_x7 h.nv⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq, BitVec.add_zero]
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq]
  · simp only [gpr_write, reduceCtorEq, ite_false]
  · have h1 : q ≠ .x5 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .x6 := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .x12 := fun e => hq (by rw [e]; decide)
    have h4 : q ≠ .x7 := fun e => hq (by rw [e]; decide)
    have h5 : q ≠ .x8 := fun e => hq (by rw [e]; decide)
    simp only [gpr_write, h1, h2, h3, h4, h5, ite_false]

/-- `(Rₙ, Lₙ)` stored, then on to the next block. -/
theorem store_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions u.wr (u.gpr .x2) 8) :
    WP isa (.block store) u fun v =>
      v.mem = (u.mem.writeW (u.gpr .x2) (byteRev32 lr.2)).writeW (u.gpr .x2 + BitVec.ofNat 64 4)
        (byteRev32 lr.1) ∧
      v.gpr .x2 = u.gpr .x2 + BitVec.ofNat 64 8 ∧ v.gpr .x3 = u.gpr .x3 - BitVec.ofNat 64 1 ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.syms = u.syms ∧
      (∀ q, q ≠ .x5 → q ≠ .x6 → q ≠ .x2 → q ≠ .x3 → v.gpr q = u.gpr q) := by
  have hd0 : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 0) 4 := CallLay.inRegions_sub hd (by omega) (by decide)
  have hd4 : InRegions u.wr (u.gpr .x2 + BitVec.ofNat 64 4) 4 := CallLay.inRegions_sub hd (by omega) (by decide)
  have h5 := h.x5
  have h6 := h.x6
  unfold store
  crun [hd0, hd4, h5, h6, rev32_eq]
  refine ⟨by rw [BitVec.add_zero], fun q a b c d => ?_⟩
  simp only [a, b, c, d, ite_false]

/-- What a block function does. -/
def BPost (s : State) (out : Spec.Cast5.Block) (v : State) : Prop :=
  Spec.Cast5.blockAt v.mem (s.gpr .x2) = out ∧
  Frame [⟨s.gpr .x2, 8⟩] s.mem v.mem ∧
  v.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 8 ∧ v.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
  v.rd = s.rd ∧ v.wr = s.wr ∧ v.syms = s.syms ∧
  (∀ q, q ∉ blockRegs → q ≠ .x2 → q ≠ .x3 → v.gpr q = s.gpr q)

/-- The store at the end of a block, from the halves `lr` after its rounds. -/
theorem finish_ok {s u : State} {k : Spec.Cast5.Schedule} {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s k lr u) (hd : InRegions s.wr (s.gpr .x2) 8) :
    WP isa (.block store) u (BPost s (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have hdx : u.gpr .x2 = s.gpr .x2 := h.same .x2 (by decide)
  have hcx : u.gpr .x3 = s.gpr .x3 := h.same .x3 (by decide)
  refine WP.mono (store_ok h (by rw [h.wr, hdx]; exact hd)) fun v ⟨vm, vdx, vcx, vrd, vwr, vsy, vg⟩ => ?_
  refine ⟨?_, ?_, by rw [vdx, hdx], by rw [vcx, hcx], vrd.trans h.rd, vwr.trans h.wr,
    vsy.trans h.syms, fun q hq hdq hcq => ?_⟩
  · rw [vm, hdx, h.mem, blockAt_write]
  · rw [vm, hdx, h.mem]
    have c0 : Region.Contains ⟨s.gpr .x2, 8⟩ (s.gpr .x2) (32 / 8) := by
      simp [Region.Contains]
    exact (Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ c0)
      List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega)))
  · rw [vg q (fun e => hq (by rw [e]; decide)) (fun e => hq (by rw [e]; decide)) hdq hcq]
    exact h.same q hq

theorem encryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa encryptBlock s
      (BPost s (Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)))) := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (blockStart_ok h) fun u ⟨hu, u12, u7, u8⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2 hG.1
    (fun g v => RInv s k (encFold k (3 * g) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))) v ∧
      v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (12 * g) ∧ v.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16)
    (fun g hg v ⟨hv, h12, h8⟩ _ => WP.mono (groupEnc_ok (by rcases h.nv with rfl | rfl <;> omega) hv h12)
      fun w ⟨hw, w12, w7, w8⟩ => ⟨⟨hw, w12, w8.trans h8⟩, w7⟩)
    ⟨hu, by rw [u12, Nat.mul_zero, BitVec.add_zero], u8⟩ u7) fun v ⟨hv, v12, v8⟩ => ?_)
  refine WP.seq (WP.ite (decide (n = 16)) (by rw [eval_zero, v8, x8_zero h.nv]) (fun h16 => ?_)
    (fun h16 => ?_))
  · have hn : n = 16 := of_decide_eq_true h16
    have v12' : v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (4 * (16 - 1)) := by
      rw [v12, hn]
    refine WP.mono (round_step hv (t := 1) (i := 16) (by decide) (by decide) (by decide) v12' true)
      fun x ⟨hx, _, _, _⟩ => ?_
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)) =
        Spec.Cast5.encodeBlock
          ((Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .x2))))).2,
          (Spec.Cast5.round k 16 (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock
            (Spec.Cast5.blockAt s.mem (s.gpr .x2))))).1) := by
      rw [encryptBlock_eq, hn, show 3 * (16 / 4 + 1) = 15 from rfl, show 16 = 15 + 1 from rfl,
        encFold_succ]
    rw [e]
    exact finish_ok hx h.data
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    have e : Spec.Cast5.encryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)) =
        Spec.Cast5.encodeBlock
          ((encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))).2,
          (encFold k (3 * (n / 4 + 1)) (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)))).1) := by
      rw [encryptBlock_eq, hn]
    rw [e]
    exact WP.block_nil (finish_ok hv h.data)

theorem dec_x12 {n : Nat} (hn : n = 12 ∨ n = 16) (x : Addr) :
    BitVec.ofNat 64 n <<< 2 + x - BitVec.ofNat 64 4 = x + BitVec.ofNat 64 (4 * (n - 1)) := by
  rcases hn with rfl | rfl <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    omega

/-- The block loaded, `x12` at the last round's subkeys, and the count of groups. -/
theorem decStart_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa (.block (load ++ ([.lsl .x .x12 .x1 2, .add .x .x12 .x12 .x0, .subImm .x .x12 .x12 4] :
        List Instr) ++ groups)) s fun u =>
      RInv s k (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2))) u ∧
      u.gpr .x12 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - 1)) ∧ u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧
      u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
  have hd0 := h.ld0
  have hd4 := h.ld4
  unfold load groups
  crun [hd0, hd4, h.x1]
  have hdec := decodeBlock_blockAt s.mem (s.gpr .x2)
  refine ⟨⟨?_, ?_, h.ctx.transfer ?_ rfl rfl rfl rfl, fun q hq => ?_, rfl, rfl, rfl, rfl⟩, dec_x12 h.nv _,
    groups_x7 h.nv⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq, BitVec.add_zero]
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, hdec, rev32_eq]
  · simp only [gpr_write, reduceCtorEq, ite_false]
  · have h1 : q ≠ .x5 := fun e => hq (by rw [e]; decide)
    have h2 : q ≠ .x6 := fun e => hq (by rw [e]; decide)
    have h3 : q ≠ .x12 := fun e => hq (by rw [e]; decide)
    have h4 : q ≠ .x7 := fun e => hq (by rw [e]; decide)
    have h5 : q ≠ .x8 := fun e => hq (by rw [e]; decide)
    simp only [gpr_write, h1, h2, h3, h4, h5, ite_false]

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

theorem decryptBlock_ok {s : State} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s k n) :
    WP isa decryptBlock s
      (BPost s (Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)))) := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases h.nv with rfl | rfl <;> decide
  obtain ⟨lr, hlr⟩ : ∃ lr, Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (s.gpr .x2)) = lr := ⟨_, rfl⟩
  unfold decryptBlock
  refine WP.seq (WP.mono (decStart_ok h) fun u ⟨hu, u12, u7, u8⟩ => ?_)
  rw [hlr] at hu
  -- Round 16 first, if there are 16.
  have first : WP isa (.ite (.zero .x .x8) (round 1 false) (.block [])) u fun v =>
      RInv s k (decFold k n (n % 3) lr) v ∧ v.gpr .x12 = v.gpr .x0 + BitVec.ofNat 64 (4 * (n - n % 3 - 1)) ∧
      v.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) (by rw [eval_zero, u8, x8_zero h.nv]) (fun h16 => ?_) (fun h16 => ?_)
    · have hn : n = 16 := of_decide_eq_true h16
      refine WP.mono (round_step hu (t := 1) (i := n) (by decide) (by rw [hn]) (by omega)
        (by rw [u12]) false) fun x ⟨hx, x12, x7, _⟩ => ?_
      have hdi : x.gpr .x0 = u.gpr .x0 :=
        (hx.same .x0 (by decide)).trans (hu.same .x0 (by decide)).symm
      have hd : decFold k n (n % 3) lr = Spec.Cast5.round k n lr := by
        rw [hn, show 16 % 3 = 0 + 1 from rfl, decFold_succ, decFold_zero, Nat.sub_zero]
      refine ⟨(by rw [hd]; exact hx), ?_, x7.trans u7⟩
      rw [x12, ite_eq_right Bool.false_ne_true, u12, hdi, hn, four, Offset.add_ofNat_sub _ (by decide)]
    · have hn : n = 12 := by
        rcases h.nv with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false h16)
      have hd : decFold k n (n % 3) lr = lr := by rw [hn, show 12 % 3 = 0 from rfl, decFold_zero]
      refine WP.block_nil ⟨(by rw [hd]; exact hu), ?_, u7⟩
      rw [u12, hn]
  refine WP.seq (WP.mono first fun v ⟨hv, v12, v7⟩ => ?_)
  -- Then the groups of three.
  refine WP.seq (WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => RInv s k (decFold k n (n % 3 + 3 * g) lr) w ∧
      (n % 3 + 3 * g < n → w.gpr .x12 = w.gpr .x0 + BitVec.ofNat 64 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, w12⟩ _ => WP.mono (groupDec_ok (m := n % 3 + 3 * g) (by omega) (by
        rcases h.nv with rfl | rfl <;> decide) (by omega) hw (w12 (by omega)))
      fun x ⟨hx, x12, x7, _⟩ =>
        ⟨⟨(show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega) ▸ hx, fun hlt => ?_⟩, x7⟩)
    ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact v12⟩
    v7) fun w ⟨hw, _⟩ => ?_)
  · have hdi : x.gpr .x0 = w.gpr .x0 :=
      (hx.same .x0 (by decide)).trans (hw.same .x0 (by decide)).symm
    rw [x12, w12 (by omega), hdi, show (12 : Addr) = BitVec.ofNat 64 12 from rfl,
      Offset.add_ofNat_sub _ (by omega)]
    congr 2
    omega
  · rw [hG.2.2.1] at hw
    have e : Spec.Cast5.decryptBlock k n (Spec.Cast5.blockAt s.mem (s.gpr .x2)) =
        Spec.Cast5.encodeBlock ((decFold k n n lr).2, (decFold k n n lr).1) := by
      rw [decryptBlock_eq, hlr]
    rw [e]
    exact finish_ok hw h.data

end VG.Proof.Cast5.AArch64