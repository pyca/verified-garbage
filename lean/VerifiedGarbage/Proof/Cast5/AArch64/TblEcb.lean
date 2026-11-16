module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblBatch
public import VerifiedGarbage.Proof.Blowfish.AArch64.Copy
public import VerifiedGarbage.Proof.Blowfish.AArch64.EcbMain
import VerifiedGarbage.Proof.Blowfish.AArch64.Ecb
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd

/-!
# CAST5 on AArch64: ECB by batches of sixteen blocks

As Blowfish's (`Proof/Blowfish/AArch64/Ecb.lean`, `EcbMain.lean`), whose
registers the code uses after its entry: `wide_ok`, the batches of sixteen
blocks in place while there are that many; `tail_ok`, the blocks left,
through the working space; `ecb_correct`, the function, which saves
`q8`–`q15` in the second half of the working space and restores them.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (c64 c128 constants copy saveRegs restoreRegs wholeLeft tailOff saveOff)
open VG.Spec.Cast5 (Word Schedule Block blockAt)
open VG.Proof.Blowfish.AArch64 (wAt Consts CopyPre CopyInv CopyPost CopyRegs copy_ok wAt_zero scratch_word lsr4
  eval_zero eval_nonzero len_lt_of_disjoint wAt_wAt cat_run strqs_run ldrqs_run constants_run savedReg savedRegs
  saveRegs_eq restoreRegs_eq saveR save_off)
open VG.AArch64.Tbl (VOnly)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p :=
  Proof.Blowfish.AArch64.blockAt_frame hf hd

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p :=
  Proof.Blowfish.AArch64.blockAt_eq_of_readW h

/-- What the batches may assume of the state they start in: the subkeys `k`
readable at `x0`, their number `N` in `x16`, the `n` blocks of data and the
working space writable, apart from each other, the table's address in `x9`
and the constants in `c64` and `c128`. -/
structure Env (s : State) (k : Schedule) (N : Nat) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  consts : Consts s
  x9 : s.gpr .x9 = s.syms planesSym
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  rounds : N = 12 ∨ N = 16
  x16 : s.gpr .x16 = BitVec.ofNat 64 N

theorem Env.len {s : State} {k : Schedule} {N : Nat} (E : Env s k N) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

/-- What the rounds read, in a state whose memory differs from `s`'s only
in regions apart from the subkeys. -/
theorem cpre_of {s u : State} {k : Schedule} (x9 : s.gpr .x9 = s.syms planesSym)
    (sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128)
    (key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0)
    (hc : Consts u) (g0 : u.gpr .x0 = s.gpr .x0) (g9 : u.gpr .x9 = s.gpr .x9) (sy : u.syms = s.syms)
    (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem u.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.gpr .x0, 128⟩ r) : CPre u k :=
  ⟨by rw [g9, sy]; exact x9, hc, by rw [hrd, hwr, g0]; exact sched, fun j hj => by
    rw [g0, hf.readW (r := ⟨s.gpr .x0, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) hd (by decide)]
    exact key j hj⟩

theorem Env.sched {s : State} {k : Schedule} {N : Nat} (E : Env s k N) :
    InRegions (s.rd ++ s.wr) (s.gpr .x0) 128 := by
  rw [E.rd]
  exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩

theorem consts_of {s u : State} (hc : Consts s) (hv : ∀ r, r ∉ roundV → u.v r = s.v r) : Consts u :=
  ⟨fun e he => by rw [hv _ consts_notin_round.1]; exact hc.1 e he,
    fun e he => by rw [hv _ consts_notin_round.2]; exact hc.2 e he⟩

/-! ## The batches of sixteen blocks -/

/-- The registers the batches keep. -/
def WideRegs (r : Reg) : Prop := r ≠ .x1 ∧ r ≠ .x2 ∧ r ∉ batchG

theorem wideRegs_x0 : WideRegs .x0 := ⟨by decide, by decide, by decide⟩
theorem wideRegs_x3 : WideRegs .x3 := ⟨by decide, by decide, by decide⟩
theorem wideRegs_x9 : WideRegs .x9 := ⟨by decide, by decide, by decide⟩
theorem wideRegs_x16 : WideRegs .x16 := ⟨by decide, by decide, by decide⟩

/-- `m` blocks left, a multiple of sixteen fewer than `n`, and at least sixteen. -/
structure WideInv (up : Bool) (k : Schedule) (N : Nat) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 16 ≤ m
  le : m ≤ n
  mod : m % 16 = n % 16
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  syms : s.syms = s₀.syms
  v : ∀ r, r ∉ roundV → s.v r = s₀.v r
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut k N up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩] s₀.mem s.mem

structure WidePost (up : Bool) (k : Schedule) (N : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = BitVec.ofNat 64 (n % 16)
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - n % 16)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  syms : s.syms = s₀.syms
  v : ∀ r, r ∉ roundV → s.v r = s₀.v r
  done : ∀ b < n - n % 16, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut k N up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - n % 16)⟩] s₀.mem s.mem

theorem loop_ok (up : Bool) {k : Schedule} {N : Nat} {s₀ : State} (E : Env s₀ k N) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (hs : WideInv up k N s₀ n m s) :
    WP isa (.loop (.seq (.block [.addImm .x .x4 .x1 0]) (.seq (batch up)
        (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 16, wholeLeft])))
      (.nonzero .x .x8)) s (WidePost up k N s₀ n) := by
  refine WP.loop (M := isa) (WideInv up k N s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hge := h.ge
  have hle := h.le
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have g := h.gpr
  have hx0 : s.gpr .x0 = S := g _ wideRegs_x0
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  have dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  have hW₁ : ∀ j < 8, InRegions s₁.wr (s₁.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj =>
    ⟨_, dataR, by rw [x4₁, wAt, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have P₁ : CPre s₁ k := cpre_of E.x9 E.sched E.key (consts_of E.consts h.v)
    ((g₁ _ (by decide)).trans hx0) ((g₁ _ (by decide)).trans (g _ wideRegs_x9)) h.syms h.rd h.wr h.frame
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega_arith))
  have h16₁ : s₁.gpr .x16 = BitVec.ofNat 64 N := by rw [g₁ _ (by decide), g _ wideRegs_x16]; exact E.x16
  apply WP.seq
  apply WP.mono (batch_ok up P₁ E.rounds h16₁ hW₁)
  intro s₂ q
  have g₂ : ∀ r, r ∉ batchG → s₂.gpr r = s.gpr r :=
    fun r hr => (q.gpr r hr).trans (g₁ r fun e => hr (by rw [e]; decide))
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 128)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x8 (s₄.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil]
    rfl, ?_⟩
  have x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 16) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide), h.x2,
      show (BitVec.ofNat 64 16) = BitVec.ofNat 64 16 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have x1₅ : s₅.gpr .x1 = wAt D (n - (m - 16)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega_arith)
  have x8₅ : s₅.gpr .x8 = BitVec.ofNat 64 ((m - 16) / 16) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, lsr4 _ (by omega_arith)]
  have g₅ : ∀ r, WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a₁, a₂, a₃⟩
    have a₈ : r ≠ .x8 := fun e => a₃ (by rw [e]; decide)
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, a₈, a₂, a₁, ite_false]
    rw [g₂ r a₃, g r ⟨a₁, a₂, a₃⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  have frame' : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s₅.mem := by
    have f₁ : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    have f₂ : Frame [⟨D, 8 * (n - (m - 16))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by
        show Region.Sub ⟨s₁.gpr .x4, 128⟩ _
        rw [x4₁]; exact Offset.sub_base _ (by omega_arith)⟩
    rw [mem₅]; exact f₁.trans f₂
  have done' : ∀ b < n - (m - 16), blockAt s₅.mem (wAt D b) =
      blockOut k N up (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    rw [mem₅]
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨s₁.gpr .x4, 128⟩
      rw [x4₁]
      exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      have e := q.out j (by omega_arith)
      rw [x4₁] at e
      have hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [show wAt D (n - m + j) = wAt D (n - m) + BitVec.ofNat 64 (8 * j) by rw [← wAt_wAt], e]
      show blockOut k N up (blockAt s.mem _) = _
      rw [show wAt D (n - m) + BitVec.ofNat 64 (8 * j) = wAt D (n - m + j) by rw [← wAt_wAt], hB]
  have wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  have rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  have sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  have sy₅ : s₅.syms = s₀.syms := q.syms.trans h.syms
  have v₅ : ∀ r, r ∉ roundV → s₅.v r = s₀.v r := fun r hr => (q.v r hr).trans (h.v r hr)
  have flag := eval_nonzero s₅ .x8 x8₅ (by omega_arith)
  by_cases hend : m - 16 < 16
  · left
    have e : m - 16 = n % 16 := by have := h.mod; omega_arith
    refine ⟨by rw [flag]; simp; omega_arith, by rw [x2₅, e], by rw [x1₅, e], g₅, rd₅, wr₅, sp₅, sy₅, v₅,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by rw [flag]; simp; omega_arith, m - 16, by omega_arith,
      ⟨by omega_arith, by omega_arith, by have := h.mod; omega_arith, x2₅, x1₅, g₅, rd₅, wr₅, sp₅, sy₅, v₅, done',
        frame'⟩⟩

theorem wide_ok (up : Bool) {k : Schedule} {N : Nat} {s : State} (E : Env s k N) :
    WP isa (wide up) s (WidePost up k N s (s.gpr .x2).toNat) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := s.write .x .x8 (s.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some, runBlock_nil]
    rfl, ?_⟩
  have x8₁ : s₁.gpr .x8 = BitVec.ofNat 64 (n / 16) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], lsr4 _ hl]
  have g₁ : ∀ r, r ≠ .x8 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have g₁' : ∀ r, WideRegs r → s₁.gpr r = s.gpr r := fun r hr => g₁ r fun e => hr.2.2 (by rw [e]; decide)
  apply WP.ite _ (eval_zero s₁ .x8 x8₁ (by omega_arith))
  · intro hz
    have hz' : n < 16 := by simp at hz; omega_arith
    apply WP.block_nil
    have e : n % 16 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, g₁', rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    have hge : 16 ≤ n := by simp at hnz; omega_arith
    have E₁ : Env s₁ k N := by
      have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      have h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit, E.consts,
        by rw [g₁ .x9 (by decide)]; exact E.x9, by rw [h0]; exact E.key, E.rounds,
        by rw [g₁ .x16 (by decide)]; exact E.x16⟩
    have hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    have I : WideInv up k N s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok up E₁ hn₁ n s₁ I)
    intro s₂ p
    have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁' r hr), p.rd, p.wr,
      p.sp, p.syms, p.v, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb]; rfl

end VG.Proof.Cast5.AArch64.Tbl
