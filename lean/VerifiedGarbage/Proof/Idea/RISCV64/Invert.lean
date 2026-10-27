module

public import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
public import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Idea.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Idea.Inverse
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Idea.RISCV64.Mul
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

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
    omega
  simp only [Mem.write, hd]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte, show (i + 2 ^ 64 - i) % 2 ^ 64 = 0 by omega, Nat.zero_lt_one,
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
    omega
  have keep' : Keep [.a2, .a4, .t0, .t1] t₀ t' := (hi.keep.trans e').mono (by decide)
  have := hi.pos; have := hi.le
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨?_, ?_, m'.trans hi.mem, keep'⟩
    · rw [Steps.eval_nonzero_ofNat _ _ (by omega) (a2'.trans hc)]; rfl
    · rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    refine ⟨?_, c - 1, by omega, by omega, by omega, a2'.trans hc, ?_, ?_, ?_, m'.trans hi.mem, keep'⟩
    · rw [Steps.eval_nonzero_ofNat _ _ (by omega) (a2'.trans hc)]
      simp only [Option.some.injEq, decide_eq_true_eq]
      omega
    · rw [e'.gpr (by decide)]; exact hi.a3
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega]
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
      show i - 8 < 8 by omega, decide_true, Bool.true_and, show 8 + (i - 8) = i by omega]

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
  mrun [h0, h1, hr, Ne.symm hr, show 2 * k < 2048 by omega, show 2 * k + 1 < 2048 by omega]

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
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (storeKey_ok (r := .t1) (by decide) n hn t₁ (hw _ (by omega)) (hw _ (by omega)))
    fun t₂ ⟨m₂, e₂⟩ => hrest t₂ ?_
  rw [ha, v₁] at m₂
  refine ⟨by omega, (e.trans e₂).mono (by decide), ?_, fun i hin => ?_⟩
  · rw [m₂, m₁]
    have hc (o : Nat) (ho : o < 104) : (⟨s₀.gpr .a1, 104⟩ : Region).Contains
        (s₀.gpr .a1 + BitVec.ofNat 64 o) 1 := Offset.contains_base _ (by omega) (by omega)
    exact (hi.frame.write (List.mem_singleton_self _) _ (hc _ (by omega))).write
      (List.mem_singleton_self _) _ (hc _ (by omega))
  · rw [m₂, write1_off _ _ _ (by omega) (by omega), write1_off _ _ _ (by omega) (by omega),
      write1_off _ _ _ (by omega) (by omega), write1_off _ _ _ (by omega) (by omega), m₁]
    by_cases he : i = n
    · subst he
      simp only [↓reduceIte, show ¬ (2 * i = 2 * i + 1) by omega]
      exact join16 _
    · simp only [show ¬ (2 * i + 1 = 2 * n + 1) by omega, show ¬ (2 * i + 1 = 2 * n) by omega,
        show ¬ (2 * i = 2 * n + 1) by omega, show ¬ (2 * i = 2 * n) by omega, ↓reduceIte]
      exact hi.words i (by omega)

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
    exact subkey_ok s₀ hp h2 n (by omega) t hi fun t₁ h₁ => subs_ok s₀ hp h2 k (n + 1) (by omega) t₁ h₁

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
    fun i hi => absurd hi (by omega)⟩) fun s' hi => ?_
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
