module

public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Impl.Idea.RISCV64
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
public import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Idea.Inverse
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `Idea.RISCV64.Invert`, which this module and modules that import it used -/

section

/-!
# IDEA decryption subkeys on RISC-V

Each decryption subkey is a copy, the negation or the inverse of an
encryption subkey (`invertKey_getD`, `Impl.Idea.invOp`), computed into
`t1` (`invWord_ok`; the inverse by a loop of fifteen steps of
`t := (t ⊙ t) ⊙ a`, `invLoop_ok`), as on PPC64LE, and stored a byte at a
time (`storeKey_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Idea

/-- A byte written at offset `j` from `a`, read at offset `i`. -/
theorem write1_off (m : Mem) (a : Addr) (v : BitVec 8) {i j : Nat} (hi : i < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    (m.write (a + BitVec.ofNat 64 j) 1 v) (a + BitVec.ofNat 64 i) =
      if i = j then v else m (a + BitVec.ofNat 64 i) := by
  have hd : ((a + BitVec.ofNat 64 i) - (a + BitVec.ofNat 64 j)).toNat = (i + 2 ^ 64 - j) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    omega_using [hj]
  simp only [Mem.write, hd]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, show (i + 2 ^ 64 - i) % 2 ^ 64 = 0 by omega_using [], Nat.zero_lt_one,
      Nat.mul_zero]
    ext k hk
    simp
  · simp only [h, ↓reduceIte, ite_eq_right_iff]
    intro h'; omega

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.a2, .a3, .a4, .t0, .t1, .t3]

theorem invStep_ok (t : State) (h2 : t.gpr .t2 = 65535) :
    WP isa (.block invStep) t fun t' =>
      t'.gpr .a4 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .a4).setWidth 16) ((t.gpr .a4).setWidth 16))
        ((t.gpr .a3).setWidth 16)).setWidth 64 ∧
      t'.gpr .a2 = t.gpr .a2 - 1#64 ∧ t'.mem = t.mem ∧ Keep [.a2, .a4, .t0, .t1] t t' := by
  simp only [invStep, List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [mov .t0 .a4, mov .t1 .a4]) t fun u =>
      u.gpr .t0 = t.gpr .a4 ∧ u.gpr .t1 = t.gpr .a4 ∧ u.mem = t.mem ∧ Keep [.t0, .t1] t u := by
    refine WP.mono (WP.keep [.t0, .t1] (Q := fun u =>
      u.gpr .t0 = t.gpr .a4 ∧ u.gpr .t1 = t.gpr .a4 ∧ u.mem = t.mem) ?_ (by decide) rfl)
      fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    mrun
  refine WP.mono h1 fun u ⟨u0, u1, um, ue⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep u ((ue.gpr (by decide)).trans h2)) fun v ⟨v1, vm, ve⟩ => ?_
  rw [WP.block_append_iff]
  have h3 : WP isa (.block [mov .t0 .t1, mov .t1 .a3]) v fun w =>
      w.gpr .t0 = v.gpr .t1 ∧ w.gpr .t1 = v.gpr .a3 ∧ w.mem = v.mem ∧ Keep [.t0, .t1] v w := by
    refine WP.mono (WP.keep [.t0, .t1] (Q := fun w =>
      w.gpr .t0 = v.gpr .t1 ∧ w.gpr .t1 = v.gpr .a3 ∧ w.mem = v.mem) ?_ (by decide) rfl)
      fun w ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    mrun
  refine WP.mono h3 fun w ⟨w0, w1, wm, we⟩ => ?_
  have e₃ : Keep [.t0, .t1] t w := ((ue.trans ve).trans we).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep w ((e₃.gpr (by decide)).trans h2)) fun x ⟨x1, xm, xe⟩ => ?_
  have h5 : WP isa (.block [mov .a4 .t1, .addi .a2 .a2 (-1)]) x fun y =>
      y.gpr .a4 = x.gpr .t1 ∧ y.gpr .a2 = x.gpr .a2 - 1#64 ∧ y.mem = x.mem ∧ Keep [.a2, .a4] x y := by
    refine WP.mono (WP.keep [.a2, .a4] (Q := fun y =>
      y.gpr .a4 = x.gpr .t1 ∧ y.gpr .a2 = x.gpr .a2 - 1#64 ∧ y.mem = x.mem) ?_ (by decide) rfl)
      fun y ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    mrun
  refine WP.mono h5 fun y ⟨y4, y2, ym, ye⟩ => ?_
  refine ⟨?_, ?_, by rw [ym, xm, wm, vm, um], ((e₃.trans xe).trans ye).mono (by decide)⟩
  · rw [y4, x1, w0, w1, v1, u0, u1, setWidth_setWidth16, ve.gpr (by decide), ue.gpr (by decide)]
  · rw [y2, xe.gpr (by decide), e₃.gpr (by decide)]

/-- `c` steps remain: `a4` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  a2 : t.gpr .a2 = BitVec.ofNat 64 c
  a3 : (t.gpr .a3).setWidth 16 = a
  a4 : (t.gpr .a4).setWidth 16 = chain a (15 - c)
  mask : t.gpr .t2 = 65535
  mem : t.mem = t₀.mem
  keep : Keep [.a2, .a4, .t0, .t1] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) (.nonzero .a2)) t (fun t' =>
      t'.gpr .a4 = (Spec.Idea.inv a).setWidth 64 ∧ t'.mem = t₀.mem ∧
      Keep [.a2, .a4, .t0, .t1] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  refine WP.mono (invStep_ok t hi.mask) fun t' ⟨a4', a2', m', e'⟩ => ?_
  have hv : t'.gpr .a4 = (chain a (15 - c + 1)).setWidth 64 := by
    rw [a4', hi.a4, hi.a3]; rfl
  have hc : t.gpr .a2 - 1#64 = BitVec.ofNat 64 (c - 1) := by
    rw [hi.a2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  have keep' : Keep [.a2, .a4, .t0, .t1] t₀ t' := (hi.keep.trans e').mono (by decide)
  have := hi.pos; have := hi.le
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨?_, ?_, m'.trans hi.mem, keep'⟩
    · rw [Steps.eval_nonzero_ofNat _ _ (by omega_using []) (a2'.trans hc)]; rfl
    · rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    refine ⟨?_, c - 1, by omega_arith, by omega_arith, by omega_using [this], a2'.trans hc, ?_, ?_, ?_, m'.trans hi.mem, keep'⟩
    · rw [Steps.eval_nonzero_ofNat _ _ (by omega_using [this]) (a2'.trans hc)]
      simp only [Option.some.injEq, decide_eq_true_eq]
      omega_arith
    · rw [e'.gpr (by decide)]; exact hi.a3
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega_arith]
    · rw [e'.gpr (by decide)]; exact hi.mask

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .t1 = ((Spec.Idea.invertKey z).getD n 0).setWidth 64 ∧ t'.mem = t.mem ∧
      Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    exact WP.mono (loadKey_ok hz (r := .t1) (by decide) hk) fun t₁ ⟨v₁, m₁, e₁⟩ =>
      ⟨v₁, m₁, e₁.mono (by decide)⟩
  | neg =>
    rw [WP.block_append_iff]
    refine WP.mono (loadKey_ok hz (r := .a3) (by decide) hk) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
    have h2 : WP isa (.block [.li .t1 0, .sub .t1 .t1 .a3, .logic .and .t1 .t1 .t2]) t₁
        fun t₂ => t₂.gpr .t1 = (0 - t₁.gpr .a3) &&& 65535 ∧ t₂.mem = t₁.mem ∧ Keep [.t1] t₁ t₂ := by
      refine WP.mono (WP.keep [.t1] (Q := fun t₂ =>
        t₂.gpr .t1 = (0 - t₁.gpr .a3) &&& 65535 ∧ t₂.mem = t₁.mem) ?_ (by decide) rfl)
        fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      mrun [(e₁.gpr (by decide)).trans hz.mask]
      rfl
    refine WP.mono h2 fun t₂ ⟨v₂, m₂, e₂⟩ => ⟨?_, m₂.trans m₁, (e₁.trans e₂).mono (by decide)⟩
    rw [v₂, neg_mask, v₁, setWidth_setWidth16]; rfl
  | inv =>
    apply WP.seq
    rw [WP.block_append_iff]
    refine WP.mono (loadKey_ok hz (r := .a3) (by decide) hk) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
    have h2 : WP isa (.block [mov .a4 .a3, .li .a2 15]) t₁ fun t₂ =>
        t₂.gpr .a3 = t₁.gpr .a3 ∧ t₂.gpr .a4 = t₁.gpr .a3 ∧ t₂.gpr .a2 = 15 ∧ t₂.mem = t₁.mem ∧
        Keep [.a2, .a4] t₁ t₂ := by
      refine WP.mono (WP.keep [.a2, .a4] (Q := fun t₂ =>
        t₂.gpr .a3 = t₁.gpr .a3 ∧ t₂.gpr .a4 = t₁.gpr .a3 ∧ t₂.gpr .a2 = 15 ∧ t₂.mem = t₁.mem) ?_
        (by decide) rfl) fun u ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩
      unfold mov
      mrun
      rfl
    refine WP.mono h2 fun t₂ ⟨a3₂, a4₂, a2₂, m₂, e₂⟩ => ?_
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ 15 t₂ ⟨by decide, by decide, a2₂,
      by rw [a3₂, v₁, setWidth_setWidth16],
      by rw [a4₂, v₁, setWidth_setWidth16]; rfl,
      (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hz.mask),
      rfl, Keep.refl _ _⟩) fun t₃ ⟨a4₃, m₃, e₃⟩ => ?_
    have h4 : WP isa (.block [mov .t1 .a4]) t₃ fun t₄ => t₄.gpr .t1 = t₃.gpr .a4 ∧
        t₄.mem = t₃.mem ∧ Keep [.t1] t₃ t₄ := by
      refine WP.mono (WP.keep [.t1] (Q := fun t₄ => t₄.gpr .t1 = t₃.gpr .a4 ∧ t₄.mem = t₃.mem) ?_
        (by decide) rfl) fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      unfold mov
      mrun
    refine WP.mono h4 fun t₄ ⟨v₄, m₄, e₄⟩ => ⟨?_, by rw [m₄, m₃, m₂, m₁],
      (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
    rw [v₄, a4₃]; rfl

/-- A word's two bytes, as `storeKey` stores them, read back little-endian. -/
theorem join16 (x : BitVec 16) : (x.setWidth 64 >>> 8).setWidth 8 ++ (x.setWidth 64).setWidth 8 = x := by
  rw [hi8, lo8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp only [h, ↓reduceIte, BitVec.getLsbD_setWidth, decide_true, Bool.true_and]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show i - 8 < 8 by omega_using [hi], decide_true, Bool.true_and, show 8 + (i - 8) = i by omega_using [h]]

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- The low 16 bits of `r` to subkey `k` of the schedule at `a1`. -/
theorem storeKey_ok {r : Reg} (hr : r ≠ .a1) (k : Nat) (hk : k < 52) (s : State)
    (h0 : InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (2 * k + 1)) 1) :
    WP isa (.block (storeKey r k)) s fun t =>
      t.mem = (s.mem.write (s.gpr .a1 + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r).setWidth 8)).write
        (s.gpr .a1 + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      Keep [r] s t := by
  refine WP.mono (WP.keep (c := .block (storeKey r k)) [r] (Q := fun t =>
      t.mem = (s.mem.write (s.gpr .a1 + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r).setWidth 8)).write
        (s.gpr .a1 + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r >>> 8).setWidth 8)) ?_
      (by simp [writesOnly, Code.allInstrs_eq, instrs, storeKey, dstOf]) rfl)
    fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold storeKey
  mrun [h0, h1, hr, Ne.symm hr, show 2 * k < 2048 by omega_using [hk], show 2 * k + 1 < 2048 by omega_using [hk]]

/-- What `vg_idea_invert_key` needs of its state: the encryption subkeys (104
bytes at `a0`) readable, the decryption subkeys (104 bytes at `a1`) writable,
apart. -/
structure InvPre (s : State) : Prop where
  sched : ⟨s.gpr .a0, 104⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .a1, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .a0, 104⟩ : Region).Disjoint ⟨s.gpr .a1, 104⟩

/-- After `n` decryption subkeys, from the state `s₀` after the mask is set. -/
structure SInv (s₀ : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 52
  keep : Keep invWrites s₀ t
  frame : Frame [⟨s₀.gpr .a1, 104⟩] s₀.mem t.mem
  words : ∀ i < n, t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * i + 1)) ++
    t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * i)) = dk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .a0)) i

theorem SInv.keyOk {s₀ t : State} {n : Nat} (hp : InvPre s₀) (h2 : s₀.gpr .t2 = 65535)
    (hi : SInv s₀ n t) : KeyOk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .a0)) t := by
  have h0 : t.gpr .a0 = s₀.gpr .a0 := hi.keep.gpr (by decide)
  have h := keyOk_of t (by rw [h0, hi.keep.2.1, hi.keep.2.2]; exact hp.sched)
    ((hi.keep.gpr (by decide)).trans h2)
  rwa [h0, scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep) (by decide))] at h

theorem subkey_ok (s₀ : State) (hp : InvPre s₀) (h2 : s₀.gpr .t2 = 65535) (n : Nat) (hn : n < 52)
    (t : State) (hi : SInv s₀ n t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', SInv s₀ (n + 1) t' → WP isa rest t' Q) :
    WP isa (.seq (invWord n) (.seq (.block (storeKey .t1 n)) rest)) t Q := by
  have hz := hi.keyOk hp h2
  apply WP.seq
  refine WP.mono (invWord_ok _ hn t hz) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
  apply WP.seq
  have e : Keep invWrites s₀ t₁ := (hi.keep.trans e₁).mono (by decide)
  have ha : t₁.gpr .a1 = s₀.gpr .a1 := e.gpr (by decide)
  have hw (o : Nat) (ho : o < 104) : InRegions t₁.wr (t₁.gpr .a1 + BitVec.ofNat 64 o) 1 := by
    rw [ha, e.2.2]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
  refine WP.mono (storeKey_ok (r := .t1) (by decide) n hn t₁ (hw _ (by omega_using [hn])) (hw _ (by omega_using [hn])))
    fun t₂ ⟨m₂, e₂⟩ => hrest t₂ ?_
  rw [ha, v₁] at m₂
  refine ⟨by omega_using [hn], (e.trans e₂).mono (by decide), ?_, fun i hin => ?_⟩
  · rw [m₂, m₁]
    have hc (o : Nat) (ho : o < 104) : (⟨s₀.gpr .a1, 104⟩ : Region).Contains
        (s₀.gpr .a1 + BitVec.ofNat 64 o) 1 := Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])
    exact (hi.frame.write (List.mem_singleton_self _) _ (hc _ (by omega_using [hn]))).write
      (List.mem_singleton_self _) _ (hc _ (by omega_using [hn]))
  · rw [m₂, write1_off _ _ _ (by omega_using [hn, hin]) (by omega_using [hn]), write1_off _ _ _ (by omega_using [hn, hin]) (by omega_using [hn]),
      write1_off _ _ _ (by omega_using [hn, hin]) (by omega_using [hn]), write1_off _ _ _ (by omega_using [hn, hin]) (by omega_using [hn]), m₁]
    by_cases he : i = n
    · subst he
      simp only [↓reduceIte, show ¬ (2 * i = 2 * i + 1) by omega_using []]
      exact join16 _
    · simp only [show ¬ (2 * i + 1 = 2 * n + 1) by omega_using [he], show ¬ (2 * i + 1 = 2 * n) by omega_using [],
        show ¬ (2 * i = 2 * n + 1) by omega_using [], show ¬ (2 * i = 2 * n) by omega_using [he], ↓reduceIte]
      exact hi.words i (by omega_using [hin, he])

/-- Decryption subkeys `n … n + k - 1`. -/
def subs (n k : Nat) : Prog isa :=
  (List.range' n k).foldr (fun n rest => .seq (invWord n) (.seq (.block (storeKey .t1 n)) rest))
    (.block [])

theorem subs_ok (s₀ : State) (hp : InvPre s₀) (h2 : s₀.gpr .t2 = 65535) :
    ∀ k n, n + k = 52 → ∀ t, SInv s₀ n t → WP isa (subs n k) t (SInv s₀ 52)
  | 0, n, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | k + 1, n, h, t, hi => by
    simp only [subs, List.range'_succ, List.foldr_cons]
    exact subkey_ok s₀ hp h2 n (by omega_using [h]) t hi fun t₁ h₁ => subs_ok s₀ hp h2 k (n + 1) (by omega_using [h]) t₁ h₁

theorem invertKey_eq : invertKey = .seq (.block setMask) (subs 0 52) := rfl

/-- `vg_idea_invert_key` on RISC-V. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 104⟩
    let out : Region := ⟨s.gpr .a1, 104⟩
    s.rd = [sched] ∧ s.wr = [out] ∧ sched.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .a1) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

/-- The registers `invertKey` writes: temporaries and argument registers. -/
abbrev invertWrites : List Reg := [.t2, .a2, .a3, .a4, .t0, .t1, .t3]

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (invertContract.post s) := by
  obtain ⟨hrd, hwr, hsep⟩ := hs
  rw [invertKey_eq]
  apply WP.seq
  have h1 : WP isa (.block setMask) s fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem ∧
      Keep [.t2] s t := by
    refine WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    exact WP.mono (setMask_ok s) fun t ⟨a, b⟩ => ⟨a, b⟩
  refine WP.mono h1 fun s₁ ⟨h2₁, m₁, e₁⟩ => ?_
  have hp : InvPre s₁ := ⟨by rw [e₁.gpr (by decide), e₁.2.1, e₁.2.2, hrd]; simp,
    by rw [e₁.gpr (by decide), e₁.2.2, hwr]; simp,
    by rw [e₁.gpr (by decide), e₁.gpr (by decide)]; exact hsep⟩
  refine WP.mono (subs_ok s₁ hp h2₁ 52 0 rfl s₁ ⟨by decide, Keep.refl _ _, Frame.refl _ _,
    fun i hi => absurd hi (by omega_using [])⟩) fun s' hi => ?_
  show Spec.Idea.scheduleAt s'.mem (s.gpr .a1) = _
  rw [← e₁.gpr (show Reg.a1 ∉ [Reg.t2] by decide), ← e₁.gpr (show Reg.a0 ∉ [Reg.t2] by decide),
    ← m₁]
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn, scheduleAt_getD _ _ hn]
  exact hi.words n hn

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ :=
    WP.keep invertWrites (invert_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem invert_ct : ConstantTime isa invertContract.pre invertContract.pub invertKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

def invertSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩]

theorem invertKey_verified : Verified RISCV64.target invertKey
    (Spec.Idea.invertKeyContract RISCV64.abi) :=
  Verified.of_correct invert_correct invert_ct (by
    sig_implies [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost,
      RISCV64.abi, RISCV64.argRegs, invertContract] [invertSat] using invertSat)

end VG.Proof.Idea.RISCV64

end

end

/-!
# IDEA key expansion on RISC-V

`expandKey_verified`: `Impl.Idea.RISCV64.expandKey` meets the shared
contract. The key, as a 128-bit number, is loaded into `a2` (its high half)
and `a3` (`keyLoad_ok`); after `j` rotations by 25 bits (`rotate_ok`) bit `i`
of the pair is bit `i - 25 j` (modulo 128) of the key (`KInv`), which is
where `Impl.Idea.keyBit` puts the bits of subkeys `8j … 8j + 7`
(`expandKey_getLsbD`), and each is stored a byte at a time
(`expandSub_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Idea VG.RISCV64.ByteLoad

/-! ## Bits -/

/-- Bit `8k + b` of eight bytes, the first most significant. -/
theorem append8_getLsbD (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) {k b : Nat} (hk : k < 8) (hb : b < 8) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7).getLsbD (8 * k + b) =
      ([b7, b6, b5, b4, b3, b2, b1, b0].getD k 0).getLsbD b := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_using [hk]
  all_goals
    simp (disch := omega) only [BitVec.getLsbD_append, ite_eq_left, ite_eq_right, List.getD_cons_zero,
      List.getD_cons_succ]
    congr 1
    omega_using []

theorem be64_getLsbD (m : Mem) (p : Addr) (off : Nat) {k b : Nat} (hk : k < 8) (hb : b < 8) :
    (be64 m p off).getLsbD (8 * k + b) = (m (p + BitVec.ofNat 64 (off + (7 - k)))).getLsbD b := by
  unfold be64
  rw [append8_getLsbD _ _ _ _ _ _ _ _ hk hb]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_using [hk]
  all_goals rfl

/-- Bit `i` of the key at `p` as a 128-bit number. -/
theorem keyAt_getLsbD (m : Mem) (p : Addr) {i : Nat} (hi : i < 128) :
    (Spec.Idea.keyValue (Spec.Idea.keyAt m p)).getLsbD i =
      (m (p + BitVec.ofNat 64 (15 - i / 8))).getLsbD (i % 8) := by
  rw [keyValue_getLsbD _ hi, keyAt_getD _ _ (by omega_using [])]

/-- The bit of the key that is at bit `i` of the pair after `j` rotations. -/
def src (j i : Nat) : Nat := (i + 128 - 25 * j % 128) % 128

/-! ## The invariant -/

/-- After `j` rotations and `n` subkeys, from `s₀`: the pair holds the key
rotated, and the first `n` subkeys are stored. -/
structure KInv (s₀ : State) (j n : Nat) (t : State) : Prop where
  le : n ≤ 52
  keep : Keep [.a2, .a3, .t0, .t1] s₀ t
  hi : ∀ i < 64, (t.gpr .a2).getLsbD i =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getLsbD (src j (64 + i))
  lo : ∀ i < 64, (t.gpr .a3).getLsbD i =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getLsbD (src j i)
  frame : Frame [⟨s₀.gpr .a1, 104⟩] s₀.mem t.mem
  words : ∀ k < n, t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * k + 1)) ++
    t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * k)) =
      (Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getD k 0

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `a0`)
readable and the schedule (104 bytes at `a1`) writable. -/
structure KeyPre (s : State) : Prop where
  key : ⟨s.gpr .a0, 16⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .a1, 104⟩ ∈ s.wr

/-! ## The pieces -/

theorem keyLoad_ok (s : State) (hp : KeyPre s) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 .a2 .t0 .a0 0 ++
      Impl.Words.RISCV64.loadBE64 .a3 .t0 .a0 8)) s (KInv s 0 0) := by
  rw [WP.block_append_iff]
  have h0 : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 0) 8 :=
    ⟨_, hp.key, Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  refine WP.mono (loadBE64_ok (by decide) (by decide) (by decide) (by decide) h0) fun s₁ h₁ => ?_
  have e₁ : s₁.gpr .a0 = s.gpr .a0 ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rw [h₁]; exact ⟨by simp [State.write], rfl, rfl⟩
  have h8 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .a0 + BitVec.ofNat 64 8) 8 := by
    rw [e₁.1, e₁.2.1, e₁.2.2]
    exact ⟨_, hp.key, Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  refine WP.mono (loadBE64_ok (by decide) (by decide) (by decide) (by decide) h8) fun s₂ h₂ => ?_
  subst h₂
  subst h₁
  have hk (i : Nat) (hi : i < 128) := keyAt_getLsbD s.mem (s.gpr .a0) hi
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl⟩, fun i hi => ?_, fun i hi => ?_, Frame.refl _ _,
    fun k hk => absurd hk (by omega_using [])⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.write, hr.1, hr.2.1, hr.2.2.1]
  · simp only [State.write, ite_eq_right (show Reg.a2 ≠ Reg.a3 by decide),
      ite_eq_right (show Reg.a2 ≠ Reg.t0 by decide), ite_true]
    have := be64_getLsbD s.mem (s.gpr .a0) 0 (k := i / 8) (b := i % 8) (by omega_using [hi]) (by omega_using [])
    rw [show 8 * (i / 8) + i % 8 = i by omega_using []] at this
    rw [this, show src 0 (64 + i) = 64 + i by simp only [src]; omega_using [hi], hk _ (by omega_using [hi]),
      show (64 + i) % 8 = i % 8 by omega_using [], show 15 - (64 + i) / 8 = 0 + (7 - i / 8) by omega_using []]
  · simp only [State.write, reduceCtorEq, ↓reduceIte]
    have := be64_getLsbD s.mem (s.gpr .a0) 8 (k := i / 8) (b := i % 8) (by omega_using [hi]) (by omega_using [])
    rw [show 8 * (i / 8) + i % 8 = i by omega_using []] at this
    rw [this, show src 0 i = i by simp only [src]; omega_using [hi], hk _ (by omega_using [hi]),
      show 15 - i / 8 = 8 + (7 - i / 8) by omega_using [hi]]

theorem rotate_ok (s₀ : State) (j n : Nat) (t : State) (hi : KInv s₀ j n t) :
    WP isa (.block rotate) t (KInv s₀ (j + 1) n) := by
  have h : WP isa (.block rotate) t fun u =>
      u.gpr .a2 = t.gpr .a2 <<< 25 ||| t.gpr .a3 >>> 39 ∧
      u.gpr .a3 = t.gpr .a3 <<< 25 ||| t.gpr .a2 >>> 39 ∧ u.mem = t.mem ∧
      Keep [.a2, .a3, .t0, .t1] t u := by
    refine WP.mono (WP.keep [.a2, .a3, .t0, .t1] (Q := fun u =>
      u.gpr .a2 = t.gpr .a2 <<< 25 ||| t.gpr .a3 >>> 39 ∧
      u.gpr .a3 = t.gpr .a3 <<< 25 ||| t.gpr .a2 >>> 39 ∧ u.mem = t.mem) ?_ (by decide) rfl)
      fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold rotate
    mrun
  refine WP.mono h fun u ⟨u2, u3, um, ue⟩ =>
    ⟨hi.le, (hi.keep.trans ue).mono (by decide), fun i hi' => ?_, fun i hi' => ?_,
      um ▸ hi.frame, fun k hk => um ▸ hi.words k hk⟩
  · rw [u2, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h25 : i < 25
    · simp only [h25, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or,
        show i < 64 from hi']
      rw [hi.lo _ (by omega_using [h25])]
      congr 1; simp only [src]; omega_using []
    · rw [BitVec.getLsbD_of_ge (t.gpr .a3) (39 + i) (by omega_using [h25])]
      simp only [h25, decide_false, Bool.not_false, Bool.and_true, Bool.or_false,
        show i < 64 from hi', decide_true, Bool.true_and]
      rw [hi.hi _ (by omega_using [hi'])]
      congr 1; simp only [src]; omega_using [h25]
  · rw [u3, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h25 : i < 25
    · simp only [h25, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or,
        show i < 64 from hi']
      rw [hi.hi _ (by omega_using [h25])]
      congr 1; simp only [src]; omega_using []
    · rw [BitVec.getLsbD_of_ge (t.gpr .a2) (39 + i) (by omega_using [h25])]
      simp only [h25, decide_false, Bool.not_false, Bool.and_true, Bool.or_false,
        show i < 64 from hi', decide_true, Bool.true_and]
      rw [hi.lo _ (by omega_using [hi'])]
      congr 1; simp only [src]; omega_using [h25]

/-- A 16-bit window, as `storeKey` stores it, read back little-endian. -/
theorem window_getLsbD (x : BitVec 64) {b : Nat} (hb : b < 16) :
    ((x >>> 8).setWidth 8 ++ x.setWidth 8).getLsbD b = x.getLsbD b := by
  rw [BitVec.getLsbD_append]
  by_cases h : b < 8
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show b - 8 < 8 by omega_using [hb], decide_true, Bool.true_and]
    congr 1; omega_using [h]

theorem expandSub_ok (s₀ : State) (hp : KeyPre s₀) (j i : Nat) (hi8 : i < 8) (hn : 8 * j + i < 52)
    (t : State) (hi : KInv s₀ j (8 * j + i) t) :
    WP isa (.block (expandSub j i)) t (KInv s₀ j (8 * j + i + 1)) := by
  have ha : t.gpr .a1 = s₀.gpr .a1 := hi.keep.gpr (by decide)
  have hw (o : Nat) (ho : o < 104) : InRegions t.wr (t.gpr .a1 + BitVec.ofNat 64 o) 1 := by
    rw [ha, hi.keep.2.2]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])⟩
  unfold expandSub
  rw [show ∀ (x : Instr) (l : List Instr), x :: l = [x] ++ l from fun _ _ => rfl,
    WP.block_append_iff]
  have hs : WP isa (.block [.shift .srl .d .t0 (half i) (16 * (3 - i % 4))]) t fun u =>
      u.gpr .t0 = t.gpr (half i) >>> (16 * (3 - i % 4)) ∧ u.mem = t.mem ∧ Keep [.t0] t u := by
    refine WP.mono (WP.keep (c := .block [.shift .srl .d .t0 (half i) (16 * (3 - i % 4))]) [.t0]
      (Q := fun u => u.gpr .t0 = t.gpr (half i) >>> (16 * (3 - i % 4)) ∧ u.mem = t.mem) ?_
      (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    mrun [show 16 * (3 - i % 4) < 64 by omega_using []]
  refine WP.mono hs fun u ⟨u0, um, ue⟩ => ?_
  have ua : u.gpr .a1 = t.gpr .a1 := ue.gpr (by decide)
  refine WP.mono (storeKey_ok (r := .t0) (by decide) (8 * j + i) hn u
    (by rw [ua, ue.2.2]; exact hw _ (by omega_using [hn])) (by rw [ua, ue.2.2]; exact hw _ (by omega_using [hn])))
    fun v ⟨vm, ve⟩ => ?_
  rw [ua, ha, u0, um] at vm
  refine ⟨by omega_using [hn], ((hi.keep.trans ue).trans ve).mono (by decide), fun b hb => ?_, fun b hb => ?_,
    ?_, fun k hk => ?_⟩
  · rw [ve.gpr (by decide), ue.gpr (by decide)]; exact hi.hi b hb
  · rw [ve.gpr (by decide), ue.gpr (by decide)]; exact hi.lo b hb
  · rw [vm]
    have hc (o : Nat) (ho : o < 104) : (⟨s₀.gpr .a1, 104⟩ : Region).Contains
        (s₀.gpr .a1 + BitVec.ofNat 64 o) 1 := Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])
    exact (hi.frame.write (List.mem_singleton_self _) _ (hc _ (by omega_using [hn]))).write
      (List.mem_singleton_self _) _ (hc _ (by omega_using [hn]))
  · rw [vm, write1_off _ _ _ (by omega_using [hn, hk]) (by omega_using [hn]), write1_off _ _ _ (by omega_using [hn, hk]) (by omega_using [hn]),
      write1_off _ _ _ (by omega_using [hn, hk]) (by omega_using [hn]), write1_off _ _ _ (by omega_using [hn, hk]) (by omega_using [hn])]
    by_cases he : k = 8 * j + i
    · subst he
      simp only [↓reduceIte, show ¬ (2 * (8 * j + i) = 2 * (8 * j + i) + 1) by omega_using []]
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      rw [window_getLsbD _ hb, BitVec.getLsbD_ushiftRight, expandKey_getLsbD _ (by omega_using [hn]) hb]
      unfold half
      by_cases h4 : i < 4
      · rw [ite_eq_left h4, hi.hi _ (by omega_using [hb]), show i % 4 = i by omega_using [h4]]
        congr 1; simp only [src, keyBit, show (8 * j + i) / 8 = j by omega_using [hi8],
          show (8 * j + i) % 8 = i by omega_using [hi8]]; omega_using [h4]
      · rw [ite_eq_right h4, hi.lo _ (by omega_using [hb]), show i % 4 = i - 4 by omega_using [hi8, h4]]
        congr 1; simp only [src, keyBit, show (8 * j + i) / 8 = j by omega_using [hi8],
          show (8 * j + i) % 8 = i by omega_using [hi8]]; omega_using [h4]
    · simp only [show ¬ (2 * k + 1 = 2 * (8 * j + i) + 1) by omega_using [he],
        show ¬ (2 * k + 1 = 2 * (8 * j + i)) by omega_using [], show ¬ (2 * k = 2 * (8 * j + i) + 1) by omega_using [],
        show ¬ (2 * k = 2 * (8 * j + i)) by omega_using [he], ↓reduceIte]
      exact hi.words k (by omega_using [hk, he])

/-- The subkeys `8j … 8j + c - 1`. -/
theorem expandSubs_ok (s₀ : State) (hp : KeyPre s₀) (j : Nat) :
    ∀ c ≤ 8, 8 * j + c ≤ 52 → ∀ t, KInv s₀ j (8 * j) t →
      WP isa (.block ((List.range c).flatMap (expandSub j))) t (KInv s₀ j (8 * j + c))
  | 0, _, _, t, hi => WP.block_nil hi
  | c + 1, hc, hj, t, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (expandSubs_ok s₀ hp j c (by omega_using [hc]) (by omega_using [hj]) t hi) fun u hu =>
      expandSub_ok s₀ hp j c (by omega_using [hc]) (by omega_using [hj]) u hu

theorem expandGroup_ok (s₀ : State) (hp : KeyPre s₀) (j : Nat) (hj : j ≤ 6) (t : State)
    (hi : KInv s₀ j (8 * j) t) :
    WP isa (.block (expandGroup j)) t (KInv s₀ j (min (8 * j + 8) 52)) := by
  unfold expandGroup
  by_cases h6 : j < 6
  · rw [ite_eq_left h6, show min (8 * j + 8) 52 = 8 * j + 8 by omega_using [h6]]
    exact expandSubs_ok s₀ hp j 8 (by decide) (by omega_using [h6]) t hi
  · rw [ite_eq_right h6, show min (8 * j + 8) 52 = 8 * j + 4 by omega_using [hj, h6]]
    exact expandSubs_ok s₀ hp j 4 (by decide) (by omega_using [hj]) t hi

theorem groups_ok (s₀ : State) (hp : KeyPre s₀) :
    ∀ c ≤ 6, ∀ t, KInv s₀ 0 8 t →
      WP isa (.block ((List.range c).flatMap fun j => rotate ++ expandGroup (j + 1))) t
        (KInv s₀ c (min (8 * c + 8) 52))
  | 0, _, t, hi => WP.block_nil hi
  | c + 1, hc, t, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (groups_ok s₀ hp c (by omega_using [hc]) t hi) fun u hu => ?_
    rw [WP.block_append_iff]
    refine WP.mono (rotate_ok s₀ c _ u hu) fun v hv => ?_
    rw [show min (8 * c + 8) 52 = 8 * (c + 1) by omega_using [hc]] at hv
    exact expandGroup_ok s₀ hp (c + 1) (by omega_using [hc]) v hv

/-! ## The function -/

/-- `vg_idea_expand_key` on RISC-V. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 16⟩
    let out : Region := ⟨s.gpr .a1, 104⟩
    s.rd = [key] ∧ s.wr = [out] ∧ key.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .a1) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

theorem expandKey_eq : expandKey = .block ((Impl.Words.RISCV64.loadBE64 .a2 .t0 .a0 0 ++
    Impl.Words.RISCV64.loadBE64 .a3 .t0 .a0 8) ++ (expandGroup 0 ++
    (List.range 6).flatMap fun j => rotate ++ expandGroup (j + 1))) := by
  simp only [expandKey, List.append_assoc]

theorem expand_wp (s : State) (hs : expandContract.pre s) :
    WP isa expandKey s (expandContract.post s) := by
  obtain ⟨hrd, hwr, _⟩ := hs
  have hp : KeyPre s := ⟨by rw [hrd, hwr]; simp, by rw [hwr]; simp⟩
  rw [expandKey_eq, WP.block_append_iff]
  refine WP.mono (keyLoad_ok s hp) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (expandGroup_ok s hp 0 (by decide) s₁ h₁) fun s₂ h₂ => ?_
  refine WP.mono (groups_ok s hp 6 (by decide) s₂ h₂) fun s' hi => ?_
  show Spec.Idea.scheduleAt s'.mem (s.gpr .a1) = _
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn, scheduleAt_getD _ _ hn]
  exact hi.words n (by omega_using [hn])

/-- The registers `expandKey` writes. -/
abbrev expandWrites : List Reg := [.a2, .a3, .t0, .t1]

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ :=
    WP.keep expandWrites (expand_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem expand_ct : ConstantTime isa expandContract.pre expandContract.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

def expandSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem expandKey_verified : Verified RISCV64.target expandKey
    (Spec.Idea.expandKeyContract RISCV64.abi) :=
  Verified.of_correct expand_correct expand_ct (by
    sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost,
      RISCV64.abi, RISCV64.argRegs, expandContract] [expandSat] using expandSat)

end VG.Proof.Idea.RISCV64
