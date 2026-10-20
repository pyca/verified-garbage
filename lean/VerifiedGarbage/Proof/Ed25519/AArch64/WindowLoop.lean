module

public import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Merged from `Proof.Ed25519.AArch64.WindowByte`. -/

@[expose] public section

section
/-!
# Verification's nibbles: one window per nibble of the scalars

Nibble `i` of `k` (and of `S`) is a digit, read from the nibbles' buffers; after it, the
accumulator represents `[k / 16^i]A - [S / 16^i]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a nibble of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 56 712 s.mem t.mem

theorem ByteKeep.refl (base : Addr) (s : State) : ByteKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.of_counter {base : Addr} {s t : State}
    (ag : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r) (ar : t.rd = s.rd) (aw : t.wr = s.wr) (asp : t.sp = s.sp)
    (am : Outside base 56 8 s.mem t.mem) : ByteKeep base s t :=
  ⟨fun r _ hb _ => ag r hb, ar, aw, asp, am.mono (by decide) (by decide)⟩

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base : Addr} {K S : Nat} {A : EPoint dZ} {s t : State}
    (h : WinCtx base K S A s) (k : ByteKeep base s t) : WinCtx base K S A t :=
  h.of_mem (k.scratch h.scratch) k.mem

/-! ## Digits from the nibbles -/

theorem digitK {base : Addr} {K S : Nat} {A : EPoint dZ} {s : State} (h : WinCtx base K S A s)
    {i : Nat} (hi : i < 128) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitAt 768) (K / 16 ^ i % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitAt_ok ht.scratch (by decide) (by omega) (kt.counter.trans hc))
    fun u ⟨uv, ku⟩ => ?_
  rw [ht.kNib i hi] at uv
  exact ⟨uv, ku.mono (by decide)⟩

theorem digitS {base : Addr} {K S : Nat} {A : EPoint dZ} {s : State} (h : WinCtx base K S A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitAt 896) (S / 16 ^ i % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitAt_ok ht.scratch (by decide) (by omega) (kt.counter.trans hc))
    fun u ⟨uv, ku⟩ => ?_
  rw [ht.sNib i hi] at uv
  exact ⟨uv, ku.mono (by decide)⟩

/-! ## A nibble -/

private theorem above_cmp : ∀ i < 129,
    (BitVec.ofNat 64 i - BitVec.ofNat 64 64 != 0) = decide (i ≠ 64) := by decide

theorem aboveLow_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i ≤ 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block aboveLow) s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 64)) ∧
      Keeps [.x19] s t := by
  rw [aboveLow, show ([ld .x19 56, .subImm .x .x19 .x19 64] : List Instr) =
    [ld .x19 56] ++ [.subImm .x .x19 .x19 64] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (64 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write, ka.mem],
    by simp only [RegUpd.rd_write, ka.rd], by simp only [RegUpd.wr_write, ka.wr],
    by simp only [RegUpd.sp_write, ka.sp]⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, av, hc, above_cmp i (by omega)]
  · have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
    rw [RegUpd.gpr_write_of_ne _ _ _ h, ka.gpr r hr]

theorem nibStepA_ok {s : State} {base : Addr} {K S : Nat} {A : EPoint dZ} (h : WinCtx base K S A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi64 : 64 ≤ i) (hi : i < 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) (hS : S < 256 ^ 32)
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))) :
    WP isa nibStepA s fun t => eval (.nonzero .x .x19) t = some (decide (i ≠ 64)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3) ((K / 16 ^ i) • A + (S / 16 ^ i) • (-baseAff)) ∧
      ByteKeep base s t := by
  rw [nibStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  refine WP.seq (WP.mono (windowA_ok (a := (K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.mod_lt _ (by decide)) (digitK ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.mono (aboveLow_ok hb'.scratch i (by omega) (kb.counter.trans av)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact bd, ?_, (ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kb.counter.trans av
  · rw [kt.mem]
    convert br using 1
    rw [← nibble_step A (-baseAff) K S i, nibble_high_zero hS hi64, Nat.zero_mod, zero_smul, add_zero]

theorem nibStepAB_ok {s : State} {base : Addr} {K S : Nat} {A : EPoint dZ} (h : WinCtx base K S A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : RepP (point (env s.mem base) 0 1 2 3)
      ((K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))) :
    WP isa nibStepAB s fun t => t.gpr .x19 = BitVec.ofNat 64 i ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      RepP (point (env t.mem base) 0 1 2 3) ((K / 16 ^ i) • A + (S / 16 ^ i) • (-baseAff)) ∧
      ByteKeep base s t := by
  rw [nibStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_)
  have ka : ByteKeep base s a := ByteKeep.of_counter ag ar aw asp am
  have ae := header_env am
  have ha' := h.of_byte ka
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 16 ^ (i + 1)) • A + (S / 16 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (digitK ha' (by omega) av) (digitS ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.mono (batchTest_ok hb'.scratch i (kb.counter.trans av)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.mem]; exact bd, ?_, (ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.mem]; exact kb.counter.trans av
  · rw [kt.mem, ← nibble_step A (-baseAff) K S i]
    exact br

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's loops over the nibbles of the scalars

The leading zero nibbles of `k` above its low 64 are skipped, as the sum before
them is zero; nibbles 127 down to 64 are digits of `k` alone, nibbles 63 down to 0
of both scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- The loops' invariant, with `c` nibbles left. -/
structure WinLoop (s₀ : State) (base : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base K S A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kLt : K < 256 ^ 64
  sLt : S < 256 ^ 32
  value : RepP (point (env s.mem base) 0 1 2 3) ((K / 16 ^ c) • A + (S / 16 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

theorem WinLoop.of_keeps {s₀ s t : State} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    {rs : List Reg} (h : WinLoop s₀ base A K S c s) (k : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinLoop s₀ base A K S c t := by
  have kb : ByteKeep base s t := ByteKeep.of_keeps k hrs
  exact ⟨h.ctx.of_byte kb, by rw [k.mem]; exact h.d, by rw [k.mem]; exact h.counter, h.kLt, h.sLt,
    by rw [k.mem]; exact h.value, h.keep.trans kb⟩

/-- A nibble of `k` alone, from `64 + j + 1` nibbles left to `64 + j`. -/
theorem stepA_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 64)
    (ht : WinLoop s₀ base A K S (64 + (j + 1)) t) :
    WP isa nibStepA t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base A K S (64 + j) u := by
  refine WP.mono (nibStepA_ok (i := 64 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) ht.sLt ht.value) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, ht.kLt, ht.sLt, uv, ht.keep.trans uk⟩

/-- A nibble of both scalars, from `j + 1` nibbles left to `j`. -/
theorem stepB_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 64)
    (ht : WinLoop s₀ base A K S (j + 1) t) :
    WP isa nibStepAB t fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
      WinLoop s₀ base A K S j u := by
  refine WP.mono (nibStepAB_ok (i := j) ht.ctx ht.d hj ht.counter ht.value)
    fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨by simp only [eval, read_x, uz, counter_nonzero (by omega : j < 2 ^ 64)], ht.ctx.of_byte uk,
    ud, uc, ht.kLt, ht.sLt, uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 64) (h : WinLoop s₀ base A K S (64 + n) s) :
    WP isa (.loop nibStepA (.nonzero .x .x19)) s (WinLoop s₀ base A K S 64) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base A K S (64 + n) t ∧ 0 < n ∧ n ≤ 64)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, hn0, hn⟩

theorem windowsA_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc64 : 64 ≤ c) (hc128 : c ≤ 128) (h : WinLoop s₀ base A K S c s) :
    WP isa windowsA s (WinLoop s₀ base A K S 64) := by
  rw [windowsA]
  refine WP.seq (WP.mono (aboveLow_ok h.ctx.scratch c (by omega) h.counter) fun a ⟨az, ka⟩ => ?_)
  have ha := h.of_keeps ka (by decide)
  refine WP.ite (decide (c ≠ 64)) az (fun hy => ?_) (fun hn => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 64 + n := ⟨c - 64, by omega⟩
    exact loopA_ok n (by have := of_decide_eq_true hy; omega) (by omega) ha
  · have : c = 64 := by simpa using hn
    subst this
    exact WP.block_nil ha

theorem loopB_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base A K S 64 s) :
    WP isa (.loop nibStepAB (.nonzero .x .x19)) s (WinLoop s₀ base A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base A K S n t ∧ 0 < n ∧ n ≤ 64)
    (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨uz.trans rfl, hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true hj]), j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

/-! ## Skipping the leading zero nibbles of `k` -/

theorem subOne_ok (s : State) (r : Reg) (n : Nat) (hc : s.gpr r = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x r r 1]) s fun t => t.gpr r = BitVec.ofNat 64 n ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

theorem skipLoad_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 128)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipLoad) s fun t => t.gpr .x8 = BitVec.ofNat 64 j ∧
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off base (768 + j))).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [skipLoad, show ([ld .x8 56, .subImm .x .x8 .x8 1, .add .x .x2 .x0 .x8, .ldrb .x19 .x2 768] :
      List Instr) = [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++ [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768])
      from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  have hm : b.mem = s.mem := kb.mem.trans ka.mem
  have b0 : b.gpr .x0 = base := (kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hs.x0)
  have hea : base + BitVec.ofNat 64 j + BitVec.ofNat 64 768 = off base (768 + j) := by
    rw [Offset.add_add, Nat.add_comm]
  have hr : InRegions (b.rd ++ b.wr) (off base (768 + j)) 1 :=
    ⟨_, List.mem_append_right _ (by rw [kb.wr, ka.wr]; exact hs.wr), contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    b0, bv, hea, hr, hm, read_byte, byte_ext,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kb.wr, ka.wr],
    by simp only [RegUpd.sp_write, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
  rw [kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.2.1])]

theorem skipStore_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 (64 + n)) :
    WP isa (.block [st .x8 56, .subImm .x .x19 .x8 64]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (64 + n) ∧
      (∀ r, r ≠ .x19 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  have he : BitVec.ofNat 64 (64 + n) - BitVec.ofNat 64 64 = BitVec.ofNat 64 n := by
    rw [Nat.add_comm, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc hs (by decide) (by decide), runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (64 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, h8, he]
  refine ⟨trivial, ?_, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, ?_⟩
  · rw [RegUpd.mem_write, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write]; exact writeW_outside _ _ _ (by decide)

private theorem byte_nonzero : ∀ b : BitVec 8,
    (BitVec.ofNat 64 b.toNat != 0) = decide (b.toNat ≠ 0) := by decide

theorem movzZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => eval (.nonzero .x .x19) t = some false ∧
      Keeps [.x19] s t :=
  WP.mono (movzW_ok s .x19 0) fun t ⟨tv, kt⟩ => ⟨by simp only [eval, read_x, tv]; rfl, kt⟩

/-- Skipping: `c = 64 + n` nibbles are left, and the nibbles of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  WinLoop s₀ base A K S (64 + n) s ∧ K / 16 ^ (64 + n) = 0 ∧ 0 < n ∧ n ≤ 64

/-- Whether the skipping goes on below `64 + j + 1` nibbles left: nibble `64 + j` of `k` is zero,
and more than 64 nibbles are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 16 ^ (64 + j) % 16 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `64 + j + 1` nibbles left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 16 ^ (64 + j) % 16 = 0 then 64 else 64 + (j + 1)

theorem skipBody_ok {s₀ t : State} {base : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base A K S (j + 1) t) :
    WP isa skipBody t fun u => eval (.nonzero .x .x19) u = some (skipOn K j) ∧
      (skipOn K j = false → WinLoop s₀ base A K S (skipEnd K j) u) ∧
      (skipOn K j = true → SkipInv s₀ base A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx.scratch (64 + j) (by omega)
    (by rw [hl.counter]; rfl)) fun a ⟨a8, av, ka⟩ => ?_)
  have ha := hl.of_keeps ka (by decide)
  have hb : (t.mem (off base (768 + (64 + j)))).toNat = K / 16 ^ (64 + j) % 16 :=
    hl.ctx.kNib _ (by omega)
  refine WP.ite (decide ((t.mem (off base (768 + (64 + j)))).toNat ≠ 0))
    (by simp only [eval, read_x, av, byte_nonzero]) (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 16 ^ (64 + j) % 16 ≠ 0 := by rw [← hb]; simpa using hy
    have hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (movzZero_ok a) fun u ⟨uz, ku⟩ => ⟨by rw [uz, hoff], fun _ => ?_,
      fun ht => absurd ht (by rw [hoff]; decide)⟩
    have e : skipEnd K j = 64 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ha.of_keeps ku (by decide)
  · have h0 : K / 16 ^ (64 + j) % 16 = 0 := by rw [← hb]; simpa using hy
    refine WP.mono (skipStore_ok ha.ctx.scratch j a8) fun u ⟨uv, uc, ug, ur, uw, usp, um⟩ => ?_
    have ku : ByteKeep base a u := ByteKeep.of_counter ug ur uw usp um
    have hK : K / 16 ^ (64 + j) = 0 := by
      have := nibble_split K (64 + j)
      rw [show 64 + j + 1 = 64 + (j + 1) by omega, hz] at this
      omega
    have hw : WinLoop s₀ base A K S (64 + j) u := by
      refine ⟨ha.ctx.of_byte ku, by rw [header_env um]; exact ha.d, uc, ha.kLt, ha.sLt, ?_,
        ha.keep.trans ku⟩
      have v := ha.value
      rw [hz, nibble_high_zero ha.sLt (by omega)] at v
      rw [header_env um, hK, nibble_high_zero ha.sLt (by omega)]
      exact v
    have he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    have hj64 : j < 64 := by omega
    refine ⟨by simp only [eval, read_x, uv]; rw [counter_nonzero (by omega : j < 2 ^ 64), he], fun hf => ?_,
      fun ht => ⟨hw, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega, by omega⟩⟩
    have hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    have e : skipEnd K 0 = 64 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact hw

theorem skipEnd_range (K j : Nat) (hj : j < 64) : 64 ≤ skipEnd K j ∧ skipEnd K j ≤ 128 := by
  unfold skipEnd; split <;> omega

theorem skipZero_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base A K S 128 s) :
    WP isa skipZero s fun t => ∃ c, 64 ≤ c ∧ c ≤ 128 ∧ WinLoop s₀ base A K S c t := by
  have hK : K / 16 ^ 128 = 0 := Nat.div_eq_of_lt (by rw [show (16 : Nat) ^ 128 = 256 ^ 64 from rfl]; exact h.kLt)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base A K S) (n := 64)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega : n ≠ 0)
    have hj : j < 64 := by have := ht.2.2.2; omega
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨uz.trans (by rw [hs]), skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2,
        uf hs⟩
    · exact Or.inr ⟨uz.trans (by rw [hs]), j, by omega, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64
