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
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
meta import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Proof.Blowfish.AArch64.ConstantTime
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-!
# CAST5 ECB on AArch64, by batches of sixteen blocks

The ECB functions of `Impl/Cast5/AArch64/Tbl.lean`: their correctness, and
their verification against the shared contracts.
-/

@[expose] public section

/-!
## CAST5 on AArch64: ECB by batches of sixteen blocks

As Blowfish's (`Proof/Blowfish/AArch64/Ecb.lean`, `EcbMain.lean`), whose
registers the code uses after its entry: `wide_ok`, the batches of sixteen
blocks in place while there are that many; `tail_ok`, the blocks left,
through the working space; `ecb_correct`, the function, which saves
`q8`–`q15` in the second half of the working space and restores them.
-/

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
  obtain hx0 : s.gpr .x0 = S := g _ wideRegs_x0
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  obtain g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  obtain x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  obtain dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  obtain hW₁ : ∀ j < 8, InRegions s₁.wr (s₁.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj =>
    ⟨_, dataR, by rw [x4₁, wAt, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain P₁ : CPre s₁ k := cpre_of E.x9 E.sched E.key (consts_of E.consts h.v)
    ((g₁ _ (by decide)).trans hx0) ((g₁ _ (by decide)).trans (g _ wideRegs_x9)) h.syms h.rd h.wr h.frame
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega_arith))
  obtain h16₁ : s₁.gpr .x16 = BitVec.ofNat 64 N := by rw [g₁ _ (by decide), g _ wideRegs_x16]; exact E.x16
  apply WP.seq
  apply WP.mono (batch_ok up P₁ E.rounds h16₁ hW₁)
  intro s₂ q
  obtain g₂ : ∀ r, r ∉ batchG → s₂.gpr r = s.gpr r :=
    fun r hr => (q.gpr r hr).trans (g₁ r fun e => hr (by rw [e]; decide))
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 128)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x8 (s₄.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil]
    rfl, ?_⟩
  obtain x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 16) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide), h.x2,
      show (BitVec.ofNat 64 16) = BitVec.ofNat 64 16 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  obtain x1₅ : s₅.gpr .x1 = wAt D (n - (m - 16)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega_arith)
  obtain x8₅ : s₅.gpr .x8 = BitVec.ofNat 64 ((m - 16) / 16) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, lsr4 _ (by omega_arith)]
  obtain g₅ : ∀ r, WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a₁, a₂, a₃⟩
    obtain a₈ : r ≠ .x8 := fun e => a₃ (by rw [e]; decide)
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, a₈, a₂, a₁, ite_false]
    rw [g₂ r a₃, g r ⟨a₁, a₂, a₃⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  obtain frame' : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s₅.mem := by
    obtain f₁ : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    obtain f₂ : Frame [⟨D, 8 * (n - (m - 16))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by
        show Region.Sub ⟨s₁.gpr .x4, 128⟩ _
        rw [x4₁]; exact Offset.sub_base _ (by omega_arith)⟩
    rw [mem₅]; exact f₁.trans f₂
  obtain done' : ∀ b < n - (m - 16), blockAt s₅.mem (wAt D b) =
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
      obtain e := q.out j (by omega_arith)
      rw [x4₁] at e
      obtain hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [show wAt D (n - m + j) = wAt D (n - m) + BitVec.ofNat 64 (8 * j) by rw [← wAt_wAt], e]
      show blockOut k N up (blockAt s.mem _) = _
      rw [show wAt D (n - m) + BitVec.ofNat 64 (8 * j) = wAt D (n - m + j) by rw [← wAt_wAt], hB]
  obtain wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  obtain rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  obtain sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  obtain sy₅ : s₅.syms = s₀.syms := q.syms.trans h.syms
  obtain v₅ : ∀ r, r ∉ roundV → s₅.v r = s₀.v r := fun r hr => (q.v r hr).trans (h.v r hr)
  obtain flag := eval_nonzero s₅ .x8 x8₅ (by omega_arith)
  by_cases hend : m - 16 < 16
  · left
    obtain e : m - 16 = n % 16 := by have := h.mod; omega_arith
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
  obtain x8₁ : s₁.gpr .x8 = BitVec.ofNat 64 (n / 16) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], lsr4 _ hl]
  obtain g₁ : ∀ r, r ≠ .x8 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  obtain g₁' : ∀ r, WideRegs r → s₁.gpr r = s.gpr r := fun r hr => g₁ r fun e => hr.2.2 (by rw [e]; decide)
  apply WP.ite _ (eval_zero s₁ .x8 x8₁ (by omega_arith))
  · intro hz
    obtain hz' : n < 16 := by simp at hz; omega_arith
    apply WP.block_nil
    obtain e : n % 16 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, g₁', rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    obtain hge : 16 ≤ n := by simp at hnz; omega_arith
    obtain E₁ : Env s₁ k N := by
      obtain h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      obtain h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit, E.consts,
        by rw [g₁ .x9 (by decide)]; exact E.x9, by rw [h0]; exact E.key, E.rounds,
        by rw [g₁ .x16 (by decide)]; exact E.x16⟩
    obtain hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    obtain I : WideInv up k N s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega_arith,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok up E₁ hn₁ n s₁ I)
    intro s₂ p
    obtain h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁' r hr), p.rd, p.wr,
      p.sp, p.syms, p.v, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb]; rfl

/-! ## The blocks left -/

/-- What the blocks left need: the `c < 16` blocks at `x1` writable, the
working space at `x3` writable, apart from each other and from the subkeys,
and what the rounds read. -/
structure TailEnv (s : State) (k : Schedule) (N : Nat) (c : Nat) : Prop where
  lt : c < 16
  x2 : s.gpr .x2 = BitVec.ofNat 64 c
  dataW : ∀ i < c, InRegions s.wr (wAt (s.gpr .x1) i) 8
  scratch : (⟨s.gpr .x3, 256⟩ : Region) ∈ s.wr
  cpre : CPre s k
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * c⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  rounds : N = 12 ∨ N = 16
  x16 : s.gpr .x16 = BitVec.ofNat 64 N

/-- The registers the blocks left keep. -/
def TailRegs (r : Reg) : Prop := r ∉ batchG ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

theorem tailRegs_x0 : TailRegs .x0 := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem tailRegs_x1 : TailRegs .x1 := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem tailRegs_x2 : TailRegs .x2 := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem tailRegs_x3 : TailRegs .x3 := ⟨by decide, by decide, by decide, by decide, by decide⟩

structure TailPost (up : Bool) (k : Schedule) (N : Nat) (c : Nat) (s s' : State) : Prop where
  out : ∀ b < c, blockAt s'.mem (wAt (s.gpr .x1) b) = blockOut k N up (blockAt s.mem (wAt (s.gpr .x1) b))
  gpr : ∀ r, TailRegs r → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  v : ∀ r, r ∉ roundV → s'.v r = s.v r
  frame : Frame [⟨s.gpr .x1, 8 * c⟩, ⟨s.gpr .x3, 128⟩] s.mem s'.mem

theorem tail_ok (up : Bool) {k : Schedule} {N c : Nat} {s : State} (E : TailEnv s k N c) :
    WP isa (tail up) s (TailPost up k N c s) := by
  let D := s.gpr .x1
  let B := s.gpr .x3
  have hk := E.lt
  obtain scrIn : ∀ i < 16, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, E.scratch, scratch_word hi⟩
  rw [tail]
  apply WP.ite _ (eval_zero s .x2 E.x2 (by omega_using [hk]))
  · intro hz
    obtain hk0 : c = 0 := by simpa using hz
    subst hk0
    apply WP.block_nil
    exact ⟨fun b hb => by omega, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  · intro hnz
    obtain hk0 : c ≠ 0 := by simpa using hnz
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₁ := ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s.write .x .x11 (s.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₁' := s₁.write .x .x13 (s₁.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₁', ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil]; rfl
    obtain g₁ : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁'.gpr r = s.gpr r := by
      intro r a b c; simp [s₁', s₁, State.write, a, b, c]
    obtain pre₁ : CopyPre D B c s₁' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega_using [hk]⟩
      · obtain ⟨r, hr, hc⟩ := E.dataW i hi
        exact ⟨r, List.mem_append_right _ hr, hc⟩
      · exact scrIn i (by omega_using [hk, hi])
      · exact E.dataBuf.sub_right (Region.sub_prefix (by omega_using [hk]))
    obtain inv₁ : CopyInv D B c s₁' 0 s₁' := by
      refine ⟨by omega_using [hk0], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, D]
      · rw [wAt_zero]; simp [s₁', s₁, State.write, State.read, B]
      · simp [s₁', s₁, State.write, State.read, E.x2]
    apply WP.seq
    apply WP.mono_syms (copy_ok pre₁ s₁' 0 inv₁)
    intro s₂ c₂ sy₂
    obtain g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s.gpr r :=
      fun r a b c e => (c₂.regs r ⟨a, b, c, e⟩).trans (g₁ r b c e)
    apply WP.seq
    -- x4 := x3
    let s₃ := s₂.write .x .x4 (s₂.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₃, ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
    obtain g₃ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₃, State.write, a, ite_false]; exact g₂ r b c e f
    obtain x4₃ : s₃.gpr .x4 = B := by
      simp [s₃, State.write, State.read]; exact g₂ _ (by decide) (by decide) (by decide) (by decide)
    have wr₃ : s₃.wr = s.wr := c₂.wr
    obtain hW₃ : ∀ j < 8, InRegions s₃.wr (s₃.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj =>
      ⟨_, by rw [wr₃]; exact E.scratch, by rw [x4₃]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
    obtain hc₃ : Consts s₃ := by
      have : s₃.v = s.v := by rw [show s₃.v = s₂.v from rfl, c₂.v]; rfl
      rw [Consts, this]; exact E.cpre.consts
    obtain P₃ : CPre s₃ k := cpre_of E.cpre.x9 E.cpre.sched E.cpre.key hc₃
      (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)) sy₂ c₂.rd c₂.wr
      (show Frame [⟨B, 8 * c⟩] s.mem s₃.mem from c₂.frame) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyBuf.sub_right (Region.sub_prefix (by omega_using [hk]))
    obtain h16₃ : s₃.gpr .x16 = BitVec.ofNat 64 N := by
      rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact E.x16
    apply WP.seq
    apply WP.mono (batch_ok up P₃ E.rounds h16₃ hW₃)
    intro s₄ q₄
    obtain g₄ : ∀ r, TailRegs r → s₄.gpr r = s.gpr r := by
      intro r ⟨a, f', i, j, l⟩
      rw [q₄.gpr r a, g₃ r (fun e => a (by rw [e]; decide)) f' i j l]
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₅ := ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₄.write .x .x11 (s₄.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₅' := s₅.write .x .x13 (s₅.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₅', ?_, ?_⟩
    · rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil]; rfl
    obtain g₅ : ∀ r, TailRegs r → s₅'.gpr r = s.gpr r := by
      intro r hr
      have ⟨_, _, i, j, l⟩ := hr
      simp only [s₅', s₅, State.write, i, j, l, ite_false]; exact g₄ r hr
    obtain wr₅ : s₅'.wr = s.wr := q₄.wr.trans wr₃
    obtain rd₅ : s₅'.rd = s.rd := q₄.rd.trans c₂.rd
    obtain pre₂ : CopyPre B D c s₅' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, by omega_using [hk]⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega_using [hk, hi])
        rw [wr₅]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₅]; exact E.dataW i hi
      · exact (E.dataBuf.sub_right (Region.sub_prefix (by omega_using [hk]))).symm
    obtain inv₂ : CopyInv B D c s₅' 0 s₅' := by
      refine ⟨by omega_using [hk0], ?_, ?_, ?_, fun j hj => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ tailRegs_x3
      · rw [wAt_zero]; simp [s₅', s₅, State.write, State.read]
        exact g₄ _ tailRegs_x1
      · simp [s₅', s₅, State.write, State.read]
        rw [g₄ _ tailRegs_x2, E.x2]
    apply WP.mono (copy_ok pre₂ s₅' 0 inv₂)
    intro s₆ c₆
    -- memory
    have m₃ : s₃.mem = s₂.mem := rfl
    have m₅ : s₅'.mem = s₄.mem := rfl
    refine ⟨fun b hb => ?_, fun r hr => (c₆.regs r ⟨hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩).trans (g₅ r hr),
      c₆.rd.trans rd₅, c₆.wr.trans wr₅, c₆.sp.trans (q₄.sp.trans c₂.sp), fun r hr => ?_, ?_⟩
    · -- the block in the data, from the scratch buffer after the batch
      obtain e₆ : blockAt s₆.mem (wAt D b) = blockAt s₄.mem (wAt B b) := by
        rw [← m₅]; exact blockAt_eq_of_readW (c₆.copied b hb)
      -- the block in the scratch buffer before the batch, from the data
      obtain e₂ : blockAt s₂.mem (wAt B b) = blockAt s.mem (wAt D b) := by
        refine blockAt_eq_of_readW ((c₂.copied b hb).trans ?_)
        rfl
      rw [e₆]
      obtain o := q₄.out b (by omega_using [hk, hb])
      rw [x4₃, m₃, e₂] at o
      exact o
    · rw [c₆.v, show s₅'.v = s₄.v from rfl, q₄.v r hr, show s₃.v = s₂.v from rfl, c₂.v]; rfl
    · have a : Frame [⟨D, 8 * c⟩, ⟨B, 128⟩] s.mem s₂.mem := c₂.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_using [hk])⟩
      obtain b : Frame [⟨D, 8 * c⟩, ⟨B, 128⟩] s₂.mem s₄.mem := q₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [x4₃]; exact fun _ h => h⟩
      obtain c' : Frame [⟨D, 8 * c⟩, ⟨B, 128⟩] s₅'.mem s₆.mem := c₆.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      rw [m₅] at c'
      exact (a.trans b).trans c'

/-! ## The function -/

/-- What the function's code after its entry may assume: the subkeys
readable at `x0`, 12 or 16 rounds in `x16`, the `n` blocks at `x1` and the
working space at `x3` writable, apart from each other. -/
structure MPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  rounds : (s.gpr .x16).toNat = 12 ∨ (s.gpr .x16).toNat = 16

/-- The code after the entry. -/
def main (up : Bool) : Prog isa :=
  .seq (.block (saveRegs ++ setup)) (.seq (wide up) (.seq (tail up) (.block restoreRegs)))

theorem setup_eq : saveRegs ++ setup = saveRegs ++ (constants ++ ([.adrSym .x9 planesSym] : List Instr)) := rfl

/-- Every block becomes its encryption or decryption, and `q8`–`q15` are
restored. -/
theorem main_ok (up : Bool) {s : State} (P : MPre s) :
    WP isa (main up) s (fun s' => (∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x16).toNat up (blockAt s.mem (wAt (s.gpr .x1) b))) ∧
      ∀ r ∈ savedRegs, s'.v r = s.v r) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  let c := n % 16
  let k := Spec.Cast5.scheduleAt s.mem S
  let N := (s.gpr .x16).toNat
  obtain bufW : (⟨s.gpr .x3, 256⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the prologue
  obtain ⟨s₁, r₁, v₁, f₁, e₁⟩ := strqs_run saveOff (by decide) 8 (by decide) s fun j hj => ⟨_, bufW, save_off s hj⟩
  obtain ⟨s₂, r₂, c₂, g₂, m₂, rd₂, wr₂, sp₂, o₂⟩ := constants_run s₁
  let s₂' := s₂.write .x .x9 (s₂.syms planesSym)
  obtain r₂' : runBlock isa ([.adrSym .x9 planesSym] : List Instr) s₂ = some s₂' := by
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_nil]
  obtain g₁ : s₁.gpr = s.gpr := by rw [e₁]
  obtain sy₂ : s₂.syms = s.syms := by rw [o₂.1, e₁]
  obtain hg₂ : ∀ r, r ≠ .x6 → r ≠ .x9 → s₂'.gpr r = s.gpr r := fun r hr h9 => by
    show (s₂.write .x .x9 _).gpr r = _
    rw [gpr_write_of_ne _ _ _ h9, g₂ r hr, g₁]
  obtain hrd₂ : s₂'.rd = s.rd := by show s₂.rd = _; rw [rd₂, e₁]
  obtain hwr₂ : s₂'.wr = s.wr := by show s₂.wr = _; rw [wr₂, e₁]
  have m₂' : s₂'.mem = s₁.mem := m₂
  obtain pro : Frame [saveR s] s.mem s₂'.mem := by rw [m₂']; exact f₁
  obtain E : Env s₂' k N := by
    obtain h0 := hg₂ .x0 (by decide) (by decide); have h1 := hg₂ .x1 (by decide) (by decide)
    obtain h2 := hg₂ .x2 (by decide) (by decide); have h3 := hg₂ .x3 (by decide) (by decide)
    refine ⟨by rw [hrd₂, h0]; exact P.rd, by rw [hwr₂, h1, h2, h3]; exact P.wr,
      by rw [h0, h1, h2]; exact P.keyData, by rw [h0, h3]; exact P.keyBuf,
      by rw [h1, h2, h3]; exact P.dataBuf, by rw [h1, h2]; exact P.fit, c₂, ?_, fun j hj => ?_, P.rounds, ?_⟩
    · show (s₂.write .x .x9 _).gpr .x9 = s₂.syms planesSym
      rw [gpr_write_self]; exact BitVec.setWidth_eq _
    · rw [h0, pro.readW (r := ⟨S, 128⟩) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact P.keyBuf.sub_right (Offset.sub_base _ (by omega_using []))) (by decide)]
      exact (Proof.Cast5.scheduleAt_getD _ _ hj).symm
    · rw [hg₂ .x16 (by decide) (by decide)]
      show s.gpr .x16 = BitVec.ofNat 64 (s.gpr .x16).toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain saveSep : (saveR s).Disjoint ⟨s.gpr .x1, 8 * n⟩ :=
    (P.dataBuf.sub_right (Offset.sub_base _ (by omega_using []))).symm
  obtain hn₂ : (s₂'.gpr .x2).toNat = n := by rw [hg₂ _ (by decide) (by decide)]
  rw [main, setup_eq]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂', by rw [saveRegs_eq]; exact cat_run r₁ (cat_run r₂ r₂'), ?_⟩
  apply WP.seq
  apply WP.mono (wide_ok up E)
  intro s₃ w
  rw [hn₂] at w
  have g := w.gpr
  obtain h0 : s₃.gpr .x0 = S := (g _ wideRegs_x0).trans (hg₂ _ (by decide) (by decide))
  obtain h3 : s₃.gpr .x3 = s.gpr .x3 := (g _ wideRegs_x3).trans (hg₂ _ (by decide) (by decide))
  obtain h1' : s₂'.gpr .x1 = D := hg₂ _ (by decide) (by decide)
  obtain h1 : s₃.gpr .x1 = wAt D (n - c) := by rw [w.x1, h1']
  obtain hl : 8 * n < 2 ^ 64 := by have := E.len; rw [hn₂] at this; exact this
  have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := P.fit
  obtain sub₁ : Region.Sub ⟨s₃.gpr .x1, 8 * c⟩ ⟨D, 8 * n⟩ := by
    rw [h1]; exact Offset.sub_base _ (by omega_using [])
  obtain T : TailEnv s₃ k N c := by
    refine ⟨Nat.mod_lt _ (by decide), w.x2, fun i hi => ?_, ?_, ?_, ?_, ?_, P.rounds, ?_⟩
    · rw [w.wr, hwr₂, P.wr, h1, wAt_wAt]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])⟩
    · rw [w.wr, hwr₂, P.wr, h3]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · refine cpre_of E.x9 E.sched E.key (consts_of E.consts w.v) (g _ wideRegs_x0) (g _ wideRegs_x9) w.syms
        w.rd w.wr w.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [h1', hg₂ .x0 (by decide) (by decide)]
      exact P.keyData.sub_right (Region.sub_prefix (by omega_using []))
    · rw [h0, h3]; exact P.keyBuf
    · rw [h3]; exact P.dataBuf.sub_left sub₁
    · rw [g _ wideRegs_x16]; exact E.x16
  apply WP.seq
  apply WP.mono (tail_ok up T)
  intro s₄ t
  -- the epilogue
  obtain hR₄ : ∀ j < 8, InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 := by
    intro j hj
    rw [t.rd, t.wr, t.gpr _ tailRegs_x3, w.rd, w.wr, h3, hrd₂, hwr₂]
    exact ⟨_, List.mem_append_right _ bufW, save_off s hj⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := ldrqs_run saveOff (by decide) 8 (by decide) s₄ hR₄
  have hm₅ : s₅.mem = s₄.mem := o₅.mem
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩ := P.dataBuf
  obtain hB₂ : ∀ b < n, blockAt s₂'.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame pro fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (saveSep.sub_right (Offset.sub_base _ (by omega_using [hb]))).symm
  refine WP.of_runBlock ⟨s₅, by rw [restoreRegs_eq]; exact r₅, ?_, ?_⟩
  · intro b hb
    rw [hm₅]
    by_cases hbk : b < n - c
    · have e := w.done b hbk
      rw [h1', hB₂ b hb] at e
      rw [← e]
      refine blockAt_frame t.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h1]; exact Offset.disjoint D (Or.inl (by omega_using [hbk])) (by omega_using [hl, hb]) (by omega_using [hl])
      · rw [h3]; exact dataB.sub_left (Offset.sub_base _ (by omega_using [hb])) |>.sub_right (Region.sub_prefix (by omega_using []))
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - c + j := ⟨b - (n - c), by omega_using [hbk]⟩
      obtain e := t.out j (by omega_using [hb])
      rw [h1, wAt_wAt] at e
      rw [e]
      obtain hB : blockAt s₃.mem (wAt D (n - c + j)) = blockAt s₂'.mem (wAt D (n - c + j)) :=
        blockAt_frame w.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact Offset.disjoint_base D (by omega_using []) (by omega_using [hl, hb])
      rw [hB, hB₂ _ hb]
  · -- the saved registers, from the save area, which nothing else wrote
    obtain ss : ∀ j < 8, s₅.v (savedReg j) = s.v (savedReg j) := by
      intro j hj
      obtain hc : (saveR s).Contains (s.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 :=
        Offset.contains _ (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hj]) (by omega_using [])
      rw [v₅ j hj, t.gpr _ tailRegs_x3, h3,
        t.frame.read hc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact saveSep.sub_right sub₁
          · rw [h3]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])) (by decide),
        w.frame.read hc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact saveSep.sub_right (Region.sub_prefix (by omega_using []))) (by decide),
        m₂', v₁ j hj]
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ss 0 (by decide)
    · exact ss 1 (by decide)
    · exact ss 2 (by decide)
    · exact ss 3 (by decide)
    · exact ss 4 (by decide)
    · exact ss 5 (by decide)
    · exact ss 6 (by decide)
    · exact ss 7 (by decide)

/-- What the function may assume: the subkeys readable at `x0`, 12 or 16
rounds in `x1`, the `n` (in `x3`) blocks at `x2` and the working space at
`x4` writable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩]
  wr : s.wr = [⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, 256⟩]
  keyData : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x4, 256⟩
  dataBuf : (⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, 256⟩
  fit : (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64
  rounds : (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16

theorem ecb_eq (up : Bool) : ecb up = .seq (.block (entry ++ (saveRegs ++ setup)))
    (.seq (wide up) (.seq (tail up) (.block restoreRegs))) := by
  simp only [ecb, List.append_assoc]

/-- Every block becomes its encryption or decryption, and `q8`–`q15` are
restored. -/
theorem ecb_correct (up : Bool) {s : State} (P : EcbPre s) :
    WP isa (ecb up) s (fun s' => (∀ b < (s.gpr .x3).toNat, blockAt s'.mem (wAt (s.gpr .x2) b) =
      blockOut (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat up (blockAt s.mem (wAt (s.gpr .x2) b))) ∧
      ∀ r ∈ savedRegs, s'.v r = s.v r) := by
  let s₁ := s.write .x .x16 (s.read .x .x1 + BitVec.ofNat _ 0)
  let s₂ := s₁.write .x .x1 (s₁.read .x .x2 + BitVec.ofNat _ 0)
  let s₃ := s₂.write .x .x2 (s₂.read .x .x3 + BitVec.ofNat _ 0)
  let s₄ := s₃.write .x .x3 (s₃.read .x .x4 + BitVec.ofNat _ 0)
  obtain rE : runBlock isa entry s = some s₄ := by
    rw [entry, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]
  obtain x0 : s₄.gpr .x0 = s.gpr .x0 := by simp [s₄, s₃, s₂, s₁, State.write]
  obtain x1 : s₄.gpr .x1 = s.gpr .x2 := by simp [s₄, s₃, s₂, s₁, State.write, State.read]
  obtain x2 : s₄.gpr .x2 = s.gpr .x3 := by simp [s₄, s₃, s₂, s₁, State.write, State.read]
  obtain x3 : s₄.gpr .x3 = s.gpr .x4 := by simp [s₄, s₃, s₂, s₁, State.write, State.read]
  obtain x16 : s₄.gpr .x16 = s.gpr .x1 := by simp [s₄, s₃, s₂, s₁, State.write, State.read]
  obtain M : MPre s₄ :=
    ⟨by rw [x0]; exact P.rd, by rw [x1, x2, x3]; exact P.wr, by rw [x0, x1, x2]; exact P.keyData,
      by rw [x0, x3]; exact P.keyBuf, by rw [x1, x2, x3]; exact P.dataBuf, by rw [x1, x2]; exact P.fit,
      by rw [x16]; exact P.rounds⟩
  rw [ecb_eq, WP.seq_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, rE, ?_⟩
  rw [← WP.seq_iff]
  refine WP.mono (main_ok up M) fun s' ⟨hb, hv⟩ => ?_
  rw [x0, x1, x2, x16] at hb
  exact ⟨hb, hv⟩

end VG.Proof.Cast5.AArch64.Tbl

/-!
## CAST5 ECB on AArch64, by batches of sixteen blocks: verified against the shared contracts

The pointers, the number of rounds and the count of blocks are public, and
so is everything the code computes from them (the batches, the round
counts, the addresses of the subkeys and of the table's planes): every
address and branch. The rotation amounts are multiplied in (`umull`), and
the S-box indices are only ever `tbl`/`tbx` operands.
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.Impl.Cast5.AArch64.Tbl
open VG.Proof.Blowfish.AArch64 (PublicRegs wAt savedRegs)

def dir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat (dir up)
        (Spec.Cast5.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

theorem ecb_blocks (K : Spec.Cast5.Schedule) (N : Nat) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.Cast5.blockAt m' (wAt D b) = blockOut K N up (Spec.Cast5.blockAt m (wAt D b))) :
    Spec.Cast5.blocksAt m' D n = Spec.Cast5.ecb K N (dir up) (Spec.Cast5.blocksAt m D n) := by
  simp only [Spec.Cast5.blocksAt, Spec.Cast5.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

theorem ecbEncrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) ecbEncrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem ecbDecrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3, .x4]) ecbDecrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 256⟩]

theorem publicRegs_five (s₁ s₂ : State) :
    PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem ecb_ok (up : Bool) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit, rounds⟩ := hs
  obtain ⟨t, s', he, ⟨hb, hv⟩, hg⟩ := WP.gprs (c := ecb up) (ecb_correct up ⟨hrd, hwr, keyData, keyBuf,
    dataBuf, fit, rounds⟩) (rs := preserved) (by cases up <;> lit_decide) (by cases up <;> rfl)
  refine ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, fun r hr => by rw [hv r hr]⟩,
    ecb_blocks _ _ _ _ _ _ _ hb⟩

theorem ecbEncrypt_verified :
    Verified AArch64.target ecbEncrypt (Proof.Cast5.ecbEncryptRoundsContract AArch64.abi) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true) (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.Cast5.ecbEncryptRoundsContract, Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig,
    Spec.Cast5.ecbPre, Proof.Cast5.ecbRoundsPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

theorem ecbDecrypt_verified :
    Verified AArch64.target ecbDecrypt (Proof.Cast5.ecbDecryptRoundsContract AArch64.abi) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false) (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.Cast5.ecbDecryptRoundsContract, Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig,
    Spec.Cast5.ecbPre, Proof.Cast5.ecbRoundsPost, abi, argRegs, ecbC, dir, publicRegs_five]
    [satState] using satState

end VG.Proof.Cast5.AArch64.Tbl
