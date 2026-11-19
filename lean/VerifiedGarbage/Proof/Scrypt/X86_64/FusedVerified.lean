module

public import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMixFused
public import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Tactic.DefEqTransformations
meta import Mathlib.Tactic.DefEqTransformations
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedLoop
import VerifiedGarbage.Proof.MdStream.X86_64.Common
meta import VerifiedGarbage.Proof.Scrypt.X86_64.FusedLoop
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.MdStream.X86_64.Common
public import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
public import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.X86_64.Common
meta import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `Scrypt.X86_64.FusedInit`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64

theorem access {rs : List Region} {p : Addr} {len off n : Nat}
    (h : InRegions rs p len) (ho : off + n ≤ len) (hn : off < 2 ^ 64 := by omega) :
    InRegions rs (bufAt p off) n :=
  Covers.one h _ _ ⟨_, by simp, contains_off ho hn⟩

theorem load_step {s₀ : State}
    (hi : InRegions (s₀.rd ++ s₀.wr) (bp s₀) 64)
    (hw : InRegions s₀.wr (sp s₀) 64)
    (hd : (bR (bp s₀)).Disjoint (scR (sp s₀)))
    {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ s₀ n s) :
    WP isa (.block (loadWord n)) s (LI s₀ s₀ (n + 1)) := by
  have hr : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact access hi (by omega_using [hn])), h.rdi]
    rw [h.frame.readW (r := bR (bp s₀)) (a := bufAt (bp s₀) (4 * n)) (w := 32) (contains_off (by omega_using [hn]) (by omega_using [hn])) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact hd.sub_right (Region.sub_prefix (by decide))) (by decide)]
    simp only [V_get _ hn]
  unfold loadWord
  split
  · rename_i hn12
    refine wp_cons (mov32_upd (d := wreg n) hr) fun s' u => WP.block_nil ?_
    have ne := wreg_ne n hn12
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, u.mem ▸ h.frame, u.rd.trans h.rd,
      u.wr.trans h.wr, (u.other _ ne.2.1.symm).trans h.rsi, (u.other _ ne.2.2.1.symm).trans h.rdi,
      (u.other _ ne.2.2.2.symm).trans h.rsp⟩
    · by_cases e : k = n
      · subst e; exact u.gpr
      · rw [u.other _ fun h' => e (wreg_inj k hk n hn12 h'), h.regs k hk (by omega_using [hkn, e])]
    · rw [u.mem]; exact h.slots k hk h12 (by omega_using [hn12, h12, hkn])
  · rename_i hn12
    refine wp_cons (mov32_upd (d := .rax) hr) fun s' u => ?_
    have hout : InRegions s'.wr (s'.ea (at_ .rsi (slotOff n))) 4 := by
      rw [ea_at, u.other _ (by decide), h.rsi, u.wr, h.wr]
      exact access hw (by simp only [slotOff]; omega_using [hn]) (by simp only [slotOff]; omega_using [hn])
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    rw [ea_at, u.other _ (by decide), h.rsi, u.gpr, u.mem]
    have e : ((V s₀)[n].setWidth 64).setWidth 32 = (V s₀)[n] := by simp
    rw [e]
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, ?_, u.rd.trans h.rd, u.wr.trans h.wr,
      (u.other _ (by decide)).trans h.rsi, (u.other _ (by decide)).trans h.rdi,
      (u.other _ (by decide)).trans h.rsp⟩
    · rw [u.other _ (wreg_ne k hk).1]; exact h.regs k hk (by omega_using [hn12, hk])
    · by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega_using []) (by simp only [slotOff]; omega_using [hk])
          (by simp only [slotOff]; omega_using [hn]) (by simp only [slotOff]; omega_using [hn12, h12, e])]
        exact h.slots k hk h12 (by omega_using [hkn, e])
    · exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega_using [hn]) (by simp only [slotOff]; omega_using [hn]))


theorem load_ok {s : State}
    (hi : InRegions (s.rd ++ s.wr) (bp s) 64) (hw : InRegions s.wr (sp s) 64)
    (hd : (bR (bp s)).Disjoint (scR (sp s))) :
    WP isa (.block load) s fun t => Words (sp s) (memWords s.mem (bp s)) t ∧
      Frame [slotR (sp s)] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .rdi = bp s ∧ t.gpr .rsp = s.gpr .rsp := by
  have ini : LI s s 0 s := ⟨fun _ _ h => by omega, fun _ _ _ h => by omega,
    Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  exact WP.mono (wp_range_flatMap (M := isa) (f := loadWord) (N := 16) (LI s s)
    (fun _ _ hn h => load_step hi hw hd hn h) 16 (Nat.le_refl _) s ini) fun t h =>
    ⟨⟨fun k hk => h.regs k hk (by omega_using [hk]), fun k hk h12 => h.slots k hk h12 hk, h.rsi⟩,
      h.frame, h.rd, h.wr, h.rdi, h.rsp⟩
end VG.Proof.Scrypt.X86_64.Retained

end

end

/-! ### `Scrypt.X86_64.BlockMixCT`, which this module and modules that import it used -/

section

/-!
# scryptBlockMix on x86-64: the loop's layout and invariants
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk salsa blockMix)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ blockMix_eq yAt_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_movm wp_store wp_add wp_addi wp_subi)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem bytesAt_length frame_bytesAt bytesAt_writeBytes_self blk_bytesAt xorBytes_length
  bytesAt_add bytesAt_blocks)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .rdi
abbrev rr : Nat := (s₀.gpr .rsi).toNat
abbrev yP : Addr := s₀.gpr .rdx
abbrev sc : Addr := s₀.gpr .r8
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (sc s₀) s₀.gpr bmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_y : (stkR s₀).Disjoint (yR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  rcx : s₀.gpr .rcx = s₀.gpr .rsi
  pos : 0 < rr s₀

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, by rw [h2, h14], ?_, h4.sub_right ?_, h5, ?_, h7, ?_, ?_, h10, h11, ?_, h13, h14, h15⟩
  · rw [h14] at h3; exact h3
  · rw [h14]; exact fun _ h => h
  · rw [h14] at h6; exact h6
  · exact h8
  · rw [h14] at h9; exact h9
  · rw [h14] at h12; exact h12

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
  simp only [Region.Contains]
  have := (sc s₀ - yP s₀).isLt
  omega_arith

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  (hp.b_y.symm.sub_left (Memory.sub_off (by omega_arith) (by omega_arith))).sub_right (Memory.sub_off (by omega_arith) (by omega_arith))

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  Memory.sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  Memory.sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off h (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  Memory.sub_off h (by omega_arith)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bB s₀ k
  rbp : s.gpr .rbp = yE s₀ k
  r12 : s.gpr .r12 = yO s₀ k
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k)
  r15 : s.gpr .r15 = xP s₀ k
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_arith)

/-! ## One pair -/

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
/-- The input is unchanged in any memory that differs from the initial one
only in `y`, `scratch` and the stack. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)
  · exact (hp.stk_b.symm.sub_left (b_sub hp ho))

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega_arith))

theorem slot_stk {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (stkR s₀) :=
  (hp.stk_y.sub_right (y_sub hp ho)).symm

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  have lt := r_lt hp
  intro p hp'
  rw [← h p hp']
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega_arith)
  refine hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa using this
  · exact (hp.stk_s.sub_right hsub).symm

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact y_disj hp hd ho' ho (by omega_arith) (by omega_arith)
  · exact slot_s hp ho'
  · exact slot_stk hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩, stkR s₀] m m') : Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨stkR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun _ h => h⟩

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩, stkR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩, stkR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_arith : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_arith, ← blk_B s₀ (by omega_arith), yAt_eq]
  have hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_arith)]
    exact b_frame hp F₂ (by omega_arith)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_arith) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_arith
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₁]
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₂]

end VG.Proof.Scrypt.X86_64.BlockMix

/-!
# scryptBlockMix on x86-64: the whole function

The prologue saves our caller's registers in `scratch` and sets up the loop's;
the loop runs the `r` pairs; the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_movm wp_store wp_add wp_subi)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem bytesAt_add frame_bytesAt
  bytesAt_blocks)

/-! ## The prologue -/

theorem saved_bound : ∀ p ∈ bmSaved, 64 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by decide

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_bound p hp; omega_arith) (by decide)

theorem prologue_eq : bmPrologue =
    ([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
     .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++
    ([.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
      .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++ rest))
      s₀ Q := by
  refine Spill.save_then .r8 bmSaved (fun p hp' => ?_) (k _ rfl rfl rfl rfl)
  have := saved_bound p hp'
  rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega_arith))

theorem dbl {a : Addr} {n : Nat} (h : a = BitVec.ofNat 64 n) : a + a = BitVec.ofNat 64 (2 * n) := by
  rw [h, ← BitVec.ofNat_add, Nat.two_mul]

set_option linter.unusedSimpArgs false in
/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx),
     .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)]) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_mov fun f uf _ _ => wp_add fun g' ug =>
    wp_mov fun h uh _ _ => wp_add fun i ui => wp_add fun j uj => wp_subi fun l ul _ => WP.block_nil ?_
  have x0 : d.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (dbl x0)
  have x2 := u2.gpr.trans (dbl x1)
  have x3 := u3.gpr.trans (dbl x2)
  have x4 := u4.gpr.trans (dbl x3)
  have x5 := u5.gpr.trans (dbl x4)
  have x6 : e6.gpr .rsi = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [u6.gpr.trans (dbl x5)]; exact congrArg (BitVec.ofNat _) (by omega_arith)
  have hm' : l.mem = saveMem s₀ := by
    rw [ul.mem, uj.mem, ui.mem, uh.mem, ug.mem, uf.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uh.rd, ug.rd, uf.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uh.wr, ug.wr, uf.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, sx64]
    show _ = bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
    rw [add_ofNat, ofNat_split (a := 64) (b := 64 * rr s₀ + 64 * rr s₀) (by omega_arith),
      show 64 * rr s₀ + 64 * rr s₀ - 64 = 128 * rr s₀ - 64 by omega_arith,
      BitVec.add_comm (BitVec.ofNat 64 64), ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_arith), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_arith]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_arith))

/-! ## The loop -/

/-- The loop's condition after pair `k`. -/
theorem eval_ne {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hz : s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) :
    isa.eval .ne s = some (decide (k + 1 ≠ rr s₀)) := by
  have lt := r_lt hp
  have e : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega_arith), Memory.toNat_ofNat_lt (by omega_arith),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega_arith
  rw [e] at hz
  show s.zf.map (!·) = _
  rw [hz]
  by_cases hl : k + 1 = rr s₀
  · simp [hl]
  · have hne : (BitVec.ofNat 64 (rr s₀ - (k + 1)) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [Memory.toNat_ofNat_lt (by omega_arith)] at this
      simp at this; omega_arith
    rw [Option.map_some, hne]; simp [hl]

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_arith, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block bmPrologue) s₀ (Inv s₀ 0) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

end VG.Proof.Scrypt.X86_64.BlockMix

/-!
# scryptBlockMix on x86-64: the public arguments

What two runs with the same public data agree on (`PubEq`, from the
contract's `pub` by `pubEq_of`).
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_addi)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.rr {s₀ s₀' : State} (hq : PubEq s₀ s₀') : rr s₀ = rr s₀' := by
  simp only [VG.Proof.Scrypt.X86_64.BlockMix.rr, hq.rsi]

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.blockMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end VG.Proof.Scrypt.X86_64.BlockMix

end

end

/-! ### `Scrypt.X86_64.FusedCT`, which only this module used -/

section

/-! ### `Scrypt.X86_64.FusedBody`, which this module and modules that import it used -/

section

/-! ### `Scrypt.X86_64.FusedSetup`, which this module and modules that import it used -/

section

/-! ### `Scrypt.X86_64.FusedInvariant`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

/-- The original BlockMix memory invariant, without its obsolete allocation
of public loop variables to the data registers. -/
structure Logical (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

def view (s₀ : State) (k : Nat) (s : State) : State :=
  {s with gpr := fun r => match r with
    | .rbx => bB s₀ k | .rbp => yE s₀ k | .r12 => yO s₀ k
    | .r13 => sc s₀ | .r14 => BitVec.ofNat 64 (rr s₀ - k) | .r15 => xP s₀ k
    | _ => s.gpr r}

theorem Logical.old {s₀ s : State} {k : Nat} (h : Logical s₀ k s) :
    BlockMix.Inv s₀ k (view s₀ k s) :=
  ⟨h.le, h.rd, h.wr, h.rsp, rfl, rfl, rfl, rfl, rfl, rfl, h.frame, h.saved, h.done, h.x⟩

theorem Logical.of_old {s₀ s : State} {k : Nat} (h : BlockMix.Inv s₀ k s) : Logical s₀ k s :=
  ⟨h.k_le, h.rd, h.wr, h.rsp, h.frame, h.saved, h.done, h.x⟩

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends Logical s₀ k s where
  words : Words (sc s₀) (memWords s.mem (xP s₀ k)) s
  metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem

theorem scratch_frame {s₀ : State} {m m' : Mem} (hf : Frame [⟨sc s₀, 64⟩] m m') :
    Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩

theorem scratch_oldframe {s₀ : State} {m m' : Mem} (hf : Frame [⟨sc s₀, 64⟩] m m') :
    Frame [slot s₀ 0, ⟨sc s₀, 64⟩, stkR s₀] m m' := hf.mono (by simp)

theorem x_s {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k ≤ rr s₀) :
    Region.Disjoint ⟨xP s₀ k, 64⟩ ⟨sc s₀, 64⟩ := by
  cases k with
  | zero =>
    exact (hp.b_s.sub_left (b_sub hp (by have := hp.pos; omega_using [this]))).sub_right (Region.sub_prefix (by decide))
  | succ k => exact slot_s hp (by omega_using [hk])

theorem Logical.scratch {s₀ s t : State} (hp : Pre s₀) {k : Nat} (h : Logical s₀ k s)
    (hf : Frame [⟨sc s₀, 64⟩] s.mem t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .rsp = s.gpr .rsp) : Logical s₀ k t := by
  have keep : ∀ a, Region.Disjoint ⟨a, 64⟩ ⟨sc s₀, 64⟩ → bytesAt t.mem a 64 = bytesAt s.mem a 64 :=
    fun a hd => Memory.frame_bytesAt hf (fun R hR => by
      simp only [List.mem_singleton] at hR; subst R; exact hd) (by decide)
  refine ⟨h.le, rd.trans h.rd, wr.trans h.wr, sp.trans h.rsp,
    h.frame.trans (scratch_frame hf), saved_keep hp (by have := hp.pos; omega_using [this]) (scratch_oldframe hf) h.saved,
    fun i hi => ?_, ?_⟩
  · rw [keep (yE s₀ i) (slot_s hp (by have := h.le; omega_using [hi, this])),
      keep (yO s₀ i) (slot_s hp (by have := h.le; omega_using [hi, this]))]
    exact h.done i hi
  · rw [keep (xP s₀ k) (x_s hp h.le), h.x]
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)
open VG.Proof.MdStream.X86_64 (wp_mov)

def metaSaved : List (Reg × Nat) := [(.rbx, 16), (.rbp, 24), (.r12, 32), (.r14, 40)]

theorem memWords_frame {rs : List Region} {m m' : Mem} {p : Addr}
    (hf : Frame rs m m') (hd : ∀ R ∈ rs, Region.Disjoint ⟨p, 64⟩ R) :
    memWords m' p = memWords m p := by
  apply Vector.ext
  intro j hj
  simp only [memWords, Vector.getElem_ofFn]
  exact hf.readW (r := ⟨p, 64⟩) (contains_off (by omega_using [hj]) (by omega_using [hj])) hd (by decide)

theorem setup_ok {s₀ s : State} (hp : Pre s₀) (h : BlockMix.Inv s₀ 0 s) :
    WP isa (.block fusedSetup) s (Inv s₀ 0) := by
  have pos := hp.pos
  have bound : ∀ p ∈ metaSaved, p.2 + 8 ≤ 64 := by decide
  change WP isa (.block (Spill.saveCode .r13 metaSaved ++
    [.mov .rsi (.reg .r13), .mov .rdi (.reg .r15)] ++ load)) s _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Spill.save_ok .r13 metaSaved s (fun p hp' => by
    rw [h.r13, h.wr, hp.wr]
    exact ⟨scR s₀, by simp, in_s s₀ (by have := bound p hp'; omega_using [this])⟩)) fun a ⟨ga, ra, wa, ma⟩ => ?_
  rw [h.r13] at ma
  have fa : Frame [⟨sc s₀, 64⟩] s.mem a.mem := by
    rw [ma]; exact Spill.saveMem_frame_base s.mem (sc s₀) s.gpr metaSaved bound (by decide)
  have sa := Spill.saveMem_saved s.mem (sc s₀) s.gpr metaSaved (by decide)
  rw [← ma] at sa
  have metadata : Meta (sc s₀) (bB s₀ 0) (yE s₀ 0) (yO s₀ 0) (BitVec.ofNat 64 (rr s₀ - 0)) a.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.rbx] using sa (.rbx, 16) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.rbp] using sa (.rbp, 24) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.r12] using sa (.r12, 32) (by simp [metaSaved])
    · simpa only [Spill.slot, bufAt, ofInt_natCast, h.r14] using sa (.r14, 40) (by simp [metaSaved])
  refine wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => WP.block_nil ?_
  have si : c.gpr .rsi = sc s₀ := by rw [uc.other _ (by decide), ub.gpr, ga, h.r13]
  have di : c.gpr .rdi = xP s₀ 0 := by rw [uc.gpr, ub.other _ (by decide), ga, h.r15]
  have rc : c.rd = s₀.rd := by rw [uc.rd, ub.rd, ra, h.rd]
  have wc : c.wr = s₀.wr := by rw [uc.wr, ub.wr, wa, h.wr]
  have mc : c.mem = a.mem := by rw [uc.mem, ub.mem]
  have spc : c.gpr .rsp = s.gpr .rsp := by rw [uc.other _ (by decide), ub.other _ (by decide), ga]
  have li : InRegions (c.rd ++ c.wr) (bp c) 64 := by
    rw [bp, di, rc, wc, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, in_b hp (by omega_using [pos])⟩
  have ls : InRegions c.wr (sp c) 64 := by
    rw [sp, si, wc, hp.wr]; exact ⟨scR s₀, by simp, by simpa using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  have ld : (VG.Proof.Scrypt.X86_64.bR (bp c)).Disjoint (VG.Proof.Scrypt.X86_64.scR (sp c)) := by
    rw [bp, sp, di, si]; exact x_s hp (by omega_using [])
  refine WP.mono (Retained.load_ok li ls ld) fun t ⟨wt, ft, rt, wrt, _, spt⟩ => ?_
  simp only [sp, bp, si, di] at wt ft
  have mprev : memWords t.mem (xP s₀ 0) = memWords c.mem (xP s₀ 0) :=
    memWords_frame ft fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact (x_s hp (by omega_using [])).sub_right (Region.sub_prefix (by decide))
  have f64 : Frame [⟨sc s₀, 64⟩] c.mem t.mem := ft.sub (sub_slot_sc _)
  have log := (Logical.of_old h).scratch hp (fa.trans (mc ▸ f64))
    (rt.trans (uc.rd.trans (ub.rd.trans ra))) (wrt.trans (uc.wr.trans (ub.wr.trans wa))) (spt.trans spc)
  refine ⟨log, ?_, ?_⟩
  · rw [mprev]; exact wt
  · have metac : Meta (sc s₀) (bB s₀ 0) (yE s₀ 0) (yO s₀ 0) (BitVec.ofNat 64 (rr s₀ - 0)) c.mem := mc ▸ metadata
    exact metac.frame (slot_s hp (o := 0) (by omega_using [pos])) (ft.sub fun R hR => by
      simp only [List.mem_singleton] at hR; subst R
      exact ⟨slotR (sc s₀), by simp, fun _ h => h⟩)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (bmPrologue ++ fusedSetup)) s₀ (Inv s₀ 0) := by
  rw [WP.block_append_iff]
  exact WP.mono (BlockMix.prologue_ok hp) fun s h => setup_ok hp h
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end

/-! ### `Scrypt.X86_64.FusedHalf`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (wp_movm wp_addi)
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)

structure Head (p src dst : Addr) (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rax : s.gpr .rax = src
  rdi : s.gpr .rdi = dst
  keep : ∀ r, r ≠ .rax → r ≠ .rdi → s.gpr r = s₀.gpr r

theorem head_ok {p b e o count : Addr} {s : State} (hsi : s.gpr .rsi = p)
    (hm : Meta p b e o count s.mem) (hs : InRegions s.wr p 64) (offset : Nat)
    (hoff : offset = 0 ∨ offset = 64) (odd : Bool) :
    WP isa (.block (fusedHead offset odd)) s (Head p (b + BitVec.ofNat 64 offset) (if odd then o else e) s) := by
  unfold fusedHead
  refine wp_movm (a := bufAt p 16) (by rw [ea_at, hsi])
    (Memory.InRegions.right (access hs (by decide))) fun a ua =>
    wp_addi fun c uc => ?_
  have si : c.gpr .rsi = p := by rw [uc.other _ (by decide), ua.other _ (by decide), hsi]
  refine wp_movm (a := bufAt p (if odd then 32 else 24)) (by rw [ea_at, si])
    (by rw [uc.rd, ua.rd, uc.wr, ua.wr]; exact Memory.InRegions.right (access hs (by cases odd <;> decide)
      (by cases odd <;> decide))) fun t ut => WP.block_nil ?_
  have mm : c.mem = s.mem := uc.mem.trans ua.mem
  refine ⟨ut.mem.trans mm, ut.rd.trans (uc.rd.trans ua.rd), ut.wr.trans (uc.wr.trans ua.wr), ?_, ?_,
    fun r h1 h2 => by rw [ut.other _ h2, uc.other _ h1, ua.other _ h1]⟩
  · rw [ut.other _ (by decide), uc.gpr, ua.gpr, hm.input]
    rcases hoff with rfl | rfl <;> rfl
  · rw [ut.gpr, mm]
    cases odd
    · exact hm.even
    · exact hm.odd

theorem half_ok {p b e o count prev : Addr} {s : State} (h : Words p (memWords s.mem prev) s)
    (hm : Meta p b e o count s.mem) (offset : Nat) (hoff : offset = 0 ∨ offset = 64) (odd : Bool)
    (hi : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 offset) 64)
    (hb : InRegions s.wr (if odd then o else e) 64) (hs : InRegions s.wr p 64)
    (hd : (bR (if odd then o else e)).Disjoint (scR p))
    (hsd : (bR (b + BitVec.ofNat 64 offset)).Disjoint (bR (if odd then o else e)))
    (hss : (bR (b + BitVec.ofNat 64 offset)).Disjoint (scR p)) :
    WP isa (fusedHalf offset odd) s fun t =>
      Words p (memWords t.mem (if odd then o else e)) t ∧
      bytesAt t.mem (if odd then o else e) 64 = Spec.Scrypt.salsa
        (xorBytes (bytesAt s.mem prev 64) (bytesAt s.mem (b + BitVec.ofNat 64 offset) 64)) ∧
      Frame [bR (if odd then o else e), slotR p, tempR p] s.mem t.mem ∧
      Meta p b e o count t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rsp = s.gpr .rsp := by
  refine WP.seq (WP.mono (head_ok h.rsi hm hs offset hoff odd) fun a ha => ?_)
  have hw : Words p (memWords a.mem prev) a := by
    rw [ha.mem]
    exact ⟨fun k hk => (ha.keep _ (wreg_ne k hk).1 (wreg_ne k hk).2.2.1).trans (h.regs k hk),
      fun k hk h12 => ha.mem ▸ h.slots k hk h12, (ha.keep _ (by decide) (by decide)).trans h.rsi⟩
  refine WP.mono (core_widen hw (by rw [ha.rd, ha.wr]; exact hi)
    (by rw [ha.wr]; exact hb) (by rw [ha.wr]; exact hs) hd hsd hss ha.rdi ha.rax)
    fun t ⟨wt, ot, ft, rt, wrt, _, spt⟩ => ?_
  rw [ha.mem] at ot ft
  exact ⟨wt, ot, ft, hm.frame hd ft, rt.trans ha.rd, wrt.trans ha.wr,
    spt.trans (ha.keep _ (by decide) (by decide))⟩
end VG.Proof.Scrypt.X86_64.Retained

end

end

/-! ### `Scrypt.X86_64.FusedTail`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (wp_movm wp_addi wp_subi wp_store)

abbrev MetaOff (n : Nat) : Prop := n = 16 ∨ n = 24 ∨ n = 32 ∨ n = 40

def metaR (p : Addr) : Region := ⟨bufAt p 16, 32⟩

theorem meta_contains (p : Addr) {off : Nat} (h : MetaOff off) :
    (metaR p).Contains (bufAt p off) 8 := by
  have h1 : 16 ≤ off := by rcases h with rfl | rfl | rfl | rfl <;> decide
  have h2 : off + 8 ≤ 48 := by rcases h with rfl | rfl | rfl | rfl <;> decide
  simpa only [metaR, bufAt, ofInt_natCast] using Offset.contains p h1 h2 (by decide)

theorem meta_read_write (m : Mem) (p : Addr) {i j : Nat} (hi : MetaOff i) (hj : MetaOff j) (v : Addr) :
    (m.writeW (bufAt p i) v).readW (bufAt p j) 64 = if i = j then v else m.readW (bufAt p j) 64 := by
  by_cases h : i = j
  · subst j; rw [ite_eq_left rfl, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    apply Mem.readW_writeW_sep _ (by decide)
    simp only [bufAt, ofInt_natCast]
    exact Offset.sep p (by rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl <;> decide)

theorem Meta.write {p b e o count : Addr} {m : Mem} (h : Meta p b e o count m)
    {off : Nat} (ho : MetaOff off) (v : Addr) :
    Meta p (if off = 16 then v else b) (if off = 24 then v else e)
      (if off = 32 then v else o) (if off = 40 then v else count) (m.writeW (bufAt p off) v) := by
  exact ⟨by rw [meta_read_write m p ho (by decide), h.input],
    by rw [meta_read_write m p ho (by decide), h.even],
    by rw [meta_read_write m p ho (by decide), h.odd],
    by rw [meta_read_write m p ho (by decide), h.count]⟩

structure TailStep (p : Addr) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  frame : Frame [metaR p] s₀.mem s.mem

theorem TailStep.trans {p : Addr} {s t u : State} (h : TailStep p s t) (h' : TailStep p t u) : TailStep p s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => (h'.keep r hr).trans (h.keep r hr), h.frame.trans h'.frame⟩

theorem advance_ok {p : Addr} {s : State} (si : s.gpr .rsi = p) (hs : InRegions s.wr p 64)
    (off inc : Nat) (ho : MetaOff off) (hn : inc = 64 ∨ inc = 128) :
    WP isa (.block (fusedAdvance off inc)) s fun t => TailStep p s t ∧
      t.mem = s.mem.writeW (bufAt p off) (s.mem.readW (bufAt p off) 64 + BitVec.ofNat 64 inc) := by
  have bound : off + 8 ≤ 64 := by rcases ho with rfl | rfl | rfl | rfl <;> decide
  unfold fusedAdvance
  refine wp_movm (a := bufAt p off) (by rw [ea_at, si])
    (Memory.InRegions.right (access hs bound (by omega_using [bound]))) fun a ua => wp_addi fun b ub => ?_
  have si' : b.gpr .rsi = p := by rw [ub.other _ (by decide), ua.other _ (by decide), si]
  refine wp_store (a := bufAt p off) (by rw [ea_at, si'])
    (by rw [ub.wr, ua.wr]; exact access hs bound (by omega_using [bound])) fun t gt mt rt wt => WP.block_nil ?_
  have val : b.gpr .rax = s.mem.readW (bufAt p off) 64 + BitVec.ofNat 64 inc := by
    rw [ub.gpr, ua.gpr]; rcases hn with rfl | rfl <;> rfl
  rw [val, ub.mem, ua.mem] at mt
  exact ⟨⟨rt.trans (ub.rd.trans ua.rd), wt.trans (ub.wr.trans ua.wr),
    fun r hr => by rw [gt, ub.other r hr, ua.other r hr],
    by rw [mt]; exact (Frame.refl _ _).writeW (by simp) _ (meta_contains p ho)⟩, mt⟩

theorem decrement_ok {p : Addr} {s : State} (si : s.gpr .rsi = p) (hs : InRegions s.wr p 64) :
    WP isa (.block [.mov .rax (.mem (at_ .rsi 40)), .alu .sub .rax (.imm 1), .store (at_ .rsi 40) .rax]) s
      fun t => TailStep p s t ∧
        t.mem = s.mem.writeW (bufAt p 40) (s.mem.readW (bufAt p 40) 64 - 1) ∧
        t.zf = some (s.mem.readW (bufAt p 40) 64 - 1 == 0) := by
  refine wp_movm (a := bufAt p 40) (by rw [ea_at, si])
    (Memory.InRegions.right (access hs (by decide))) fun a ua => wp_subi fun b ub hz => ?_
  have hea : b.ea (at_ .rsi 40) = bufAt p 40 := by
    rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), si]
  have hw : InRegions b.wr (bufAt p 40) 8 := by
    rw [ub.wr, ua.wr]; exact access hs (by decide)
  have val : b.gpr .rax = s.mem.readW (bufAt p 40) 64 - 1 := by
    rw [ub.gpr, ua.gpr]; rfl
  refine VG.Proof.MdStream.X86_64.WP.cons (s' := { b with mem := b.mem.writeW (bufAt p 40) (b.gpr .rax) })
    (by simp only [exec, State.store64, hea, hw, ite_true]) (WP.block_nil ?_)
  have mt : b.mem.writeW (bufAt p 40) (b.gpr .rax) =
      s.mem.writeW (bufAt p 40) (s.mem.readW (bufAt p 40) 64 - 1) := by rw [val, ub.mem, ua.mem]
  refine ⟨⟨ub.rd.trans ua.rd, ub.wr.trans ua.wr,
    fun r hr => by rw [ub.other r hr, ua.other r hr], ?_⟩, mt, ?_⟩
  · rw [mt]; exact (Frame.refl _ _).writeW (by simp) _ (meta_contains p (by decide))
  · rw [hz, ua.gpr]; rfl

theorem tail_ok {p b e o count : Addr} {s : State} (si : s.gpr .rsi = p)
    (hs : InRegions s.wr p 64) (hm : Meta p b e o count s.mem) :
    WP isa (.block fusedTail) s fun t => TailStep p s t ∧
      Meta p (b + 128) (e + 64) (o + 64) (count - 1) t.mem ∧
      t.zf = some (count - 1 == 0) := by
  unfold fusedTail
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  apply (advance_ok si hs 16 128 (by decide) (by decide)).mono
  intro a ⟨ha, ma⟩
  have hma : Meta p (b + 128) e o count a.mem := by
    rw [ma, hm.input]; exact hm.write (off := 16) (by decide) (b + 128)
  rw [WP.block_append_iff]
  apply (advance_ok (p := p) (by rw [ha.keep _ (by decide), si]) (by rw [ha.wr]; exact hs)
    24 64 (by decide) (by decide)).mono
  intro c ⟨hc, mc⟩
  have hmc : Meta p (b + 128) (e + 64) o count c.mem := by
    rw [mc, hma.even]; exact hma.write (off := 24) (by decide) (e + 64)
  have hac := ha.trans hc
  rw [WP.block_append_iff]
  apply (advance_ok (p := p) (by rw [hac.keep _ (by decide), si]) (by rw [hac.wr]; exact hs)
    32 64 (by decide) (by decide)).mono
  intro d ⟨hd, md⟩
  have hmd : Meta p (b + 128) (e + 64) (o + 64) count d.mem := by
    rw [md, hmc.odd]; exact hmc.write (off := 32) (by decide) (o + 64)
  have had := hac.trans hd
  apply (decrement_ok (p := p) (by rw [had.keep _ (by decide), si]) (by rw [had.wr]; exact hs)).mono
  intro t ⟨ht, mt, hz⟩
  refine ⟨had.trans ht, ?_, ?_⟩
  · rw [mt, hmd.count]; exact hmd.write (off := 40) (by decide) (count - 1)
  · rw [hmd.count] at hz; exact hz

theorem TailStep.scratch {p : Addr} {s t : State} (h : TailStep p s t) : Frame [⟨p, 64⟩] s.mem t.mem :=
  h.frame.sub fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    exact ⟨⟨p, 64⟩, by simp, by simpa only [metaR, bufAt, ofInt_natCast] using
      (Offset.sub_base p (d := 16) (n := 32) (k := 64) (by decide))⟩

theorem Words.tail {p : Addr} {v : Vector Spec.Scrypt.Word 16} {s t : State}
    (h : Words p v s) (ht : TailStep p s t) : Words p v t := by
  refine ⟨fun k hk => (ht.keep _ (wreg_ne k hk).1).trans (h.regs k hk), ?_,
    (ht.keep _ (by decide)).trans h.rsi⟩
  intro k hk h12
  rw [ht.frame.readW (r := slotR p) (by
    simpa only [slotR, bufAt, ofInt_natCast] using
      Offset.contains_base p (d := slotOff k) (n := 4) (k := 16)
        (by simp only [slotOff]; omega_using [hk]) (by simp only [slotOff]; omega_using [hk])) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    simpa only [slotR, metaR, bufAt, ofInt_natCast, BitVec.add_zero] using
      Offset.disjoint p (d := 0) (n := 16) (e := 16) (k := 32) (by decide) (by decide) (by decide)) (by decide)]
  exact h.slots k hk h12
end VG.Proof.Scrypt.X86_64.Retained

end

end


@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

/-- Lift only the core's actual writes into the established BlockMix frame. -/
theorem core_frame {s₀ : State} {off : Nat} {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86_64.bR (yP s₀ + BitVec.ofNat 64 off), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
      Retained.tempR (sc s₀)] m m') :
    Frame [slot s₀ off, ⟨sc s₀, 64⟩, stkR s₀] m m' := by
  apply hf.sub
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact ⟨slot s₀ off, by simp, fun _ h => h⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, by simpa only [Retained.tempR, bufAt, ofInt_natCast] using
      (Offset.sub_base (sc s₀) (d := 48) (n := 8) (k := 64) (by decide))⟩

theorem half_ok {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) {prev : Addr}
    (words : Words (sc s₀) (memWords s.mem prev) s)
    (metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem)
    (odd : Bool) :
    WP isa (fusedHalf (if odd then 64 else 0) odd) s fun t =>
      Words (sc s₀) (memWords t.mem (if odd then yO s₀ k else yE s₀ k)) t ∧
      bytesAt t.mem (if odd then yO s₀ k else yE s₀ k) 64 = Spec.Scrypt.salsa
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem prev 64)
          (bytesAt s.mem (bB s₀ k + BitVec.ofNat 64 (if odd then 64 else 0)) 64)) ∧
      Frame [VG.Proof.Scrypt.X86_64.bR (if odd then yO s₀ k else yE s₀ k), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
        Retained.tempR (sc s₀)] s.mem t.mem ∧
      Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rsp = s.gpr .rsp := by
  apply Retained.half_ok words metadata _ (by cases odd <;> simp) odd
  · rw [rd, wr, hp.rd, hp.wr]
    refine ⟨bR s₀, by simp, ?_⟩
    simp only [bB, Memory.add_ofNat]
    exact in_b hp (by cases odd <;> simp <;> omega_using [hk])
  · rw [wr, hp.wr]
    refine ⟨yR s₀, by simp, ?_⟩
    cases odd <;> exact in_y hp (by omega_using [hk])
  · rw [wr, hp.wr]
    exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  · cases odd <;> exact slot_s hp (by omega_using [hk])
  · simp only [bB, Memory.add_ofNat]
    cases odd <;> exact (yb_disj hp (by omega_using [hk]) (by simp; omega_using [hk])).symm
  · simp only [bB, Memory.add_ofNat]
    exact (hp.b_s.sub_left (b_sub hp (by cases odd <;> simp <;> omega_using [hk]))).sub_right
      (Region.sub_prefix (by decide))

theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa fusedBody s fun t => Inv s₀ (k + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0) := by
  unfold fusedBody
  refine WP.seq (WP.mono (half_ok hp hk h.rd h.wr h.words h.metadata false) fun a ha => ?_)
  obtain ⟨wa, ba, fa, ma, ra, wra, spa⟩ := ha
  simp only [Bool.false_eq_true, ite_false, BitVec.add_zero] at wa ba fa
  refine WP.seq (WP.mono (half_ok hp hk (ra.trans h.rd) (wra.trans h.wr) wa ma true) fun b hb => ?_)
  obtain ⟨wb, bb, fb, mb, rb, wrb, spb⟩ := hb
  simp only [ite_true] at wb bb fb
  have baddr : bB s₀ k + BitVec.ofNat 64 64 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [bB, Memory.add_ofNat]; congr 2; omega_using []
  rw [baddr] at bb
  obtain ⟨ff, saved, done⟩ := mem_ok hp hk h.toLogical.old (core_frame fa) ba (core_frame fb) bb
  have logical : Logical s₀ (k + 1) b :=
    ⟨by omega_using [hk], rb.trans (ra.trans h.rd), wrb.trans (wra.trans h.wr), spb.trans (spa.trans h.rsp),
      ff, saved, done, by show bytesAt b.mem (yO s₀ k) 64 = _; rw [(done k (by omega_using [])).2]; rfl⟩
  have hs : InRegions b.wr (sc s₀) 64 := by
    rw [logical.wr, hp.wr]; exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  refine WP.mono (Retained.tail_ok wb.rsi hs mb) fun t ⟨ht, mt, hz⟩ => ?_
  have lt := r_lt hp
  have nextb : bB s₀ k + 128 = bB s₀ (k + 1) := by
    change bP s₀ + BitVec.ofNat 64 (128 * k) + BitVec.ofNat 64 128 = _
    rw [Memory.add_ofNat]; congr 2
  have nexte : yE s₀ k + 64 = yE s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nexto : yO s₀ k + 64 = yO s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + k)) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nextc : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega_using [lt]), Memory.toNat_ofNat_lt (by omega_using [lt]),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hk, lt]
  rw [nextb, nexte, nexto, nextc] at mt
  refine ⟨⟨logical.scratch hp ht.scratch ht.rd ht.wr (ht.keep _ (by decide)), ?_, mt⟩, hz⟩
  have mw := memWords_frame ht.scratch (p := yO s₀ k) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst R; exact slot_s hp (by omega_using [hk]))
  change Words (sc s₀) (memWords t.mem (yO s₀ k)) t
  rw [mw]; exact wb.tail ht
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

structure Ready (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∃ prev, Words (sc s₀) (memWords s.mem prev) s
  metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem

theorem Inv.ready {s₀ s : State} {k : Nat} (h : Inv s₀ k s) : Ready s₀ k s :=
  ⟨h.rd, h.wr, ⟨_, h.words⟩, h.metadata⟩

theorem Ready.rsi {s₀ s : State} {k : Nat} (h : Ready s₀ k s) : s.gpr .rsi = sc s₀ :=
  h.words.elim fun _ hw => hw.rsi

theorem Ready.scratch {s₀ s : State} {k : Nat} (hp : Pre s₀) (h : Ready s₀ k s) :
    InRegions s.wr (sc s₀) 64 := by
  rw [h.wr, hp.wr]
  exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩

theorem half_ready {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
    (h : Ready s₀ k s) (odd : Bool) :
    WP isa (fusedHalf (if odd then 64 else 0) odd) s (Ready s₀ k) := by
  obtain ⟨prev, hw⟩ := h.words
  exact (half_ok hp hk h.rd h.wr hw h.metadata odd).mono fun _ ht =>
    ⟨ht.2.2.2.2.1.trans h.rd, ht.2.2.2.2.2.1.trans h.wr, ⟨_, ht.1⟩, ht.2.2.2.1⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem half_rel {k : Nat} (hk : k < rr s₀) (odd : Bool) :
    RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
      (fusedHalf (if odd then 64 else 0) odd) (fun s t => Ready s₀ k s ∧ Ready s₀' k t) := by
  let H (origin : State) (s : State) : Prop :=
    s.gpr .rax = bB origin k + BitVec.ofNat 64 (if odd then 64 else 0) ∧
    s.gpr .rdi = (if odd then yO origin k else yE origin k) ∧ s.gpr .rsi = sc origin
  have hw {origin s : State} (hp : Pre origin) (h : Ready origin k s) :
      WP isa (.block (fusedHead (if odd then 64 else 0) odd)) s (H origin) :=
    (Retained.head_ok h.rsi h.metadata (h.scratch hp) _ (by cases odd <;> simp) odd).mono
      fun _ ht => ⟨ht.rax, ht.rdi, (ht.keep _ (by decide) (by decide)).trans h.rsi⟩
  have head : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
      (.block (fusedHead (if odd then 64 else 0) odd)) (fun s t => H s₀ s ∧ H s₀' t) := by
    have ct : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t)
        (.block (fusedHead (if odd then 64 else 0) odd)) (fun _ _ => True) := by
      cases odd <;> exact RelCT.taint (A := taint) (Taint.ofRegs [.rsi])
        (fun _ _ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          rw [h.1.rsi, h.2.rsi, sc, sc, hq.r8]) (by taint_decide)
    exact (ct.wp fun _ _ h => ⟨hw hp h.1, hw hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have core : RelCT isa (fun s t => H s₀ s ∧ H s₀' t) fusedCore (fun _ _ => True) :=
    Retained.core_rel.mono (fun s t h => by
      obtain ⟨⟨a, d, si⟩, ⟨a', d', si'⟩⟩ := h
      rw [a, a', d, d', si, si']
      simp only [bB, bP, yO, yE, yP, sc, hq.rdi, hq.rdx, hq.r8, hq.rr, and_self])
      (fun _ _ h => h)
  exact ((head.seq core).wp fun _ _ h =>
    ⟨half_ready hp hk h.1 odd, half_ready hp' (hq.rr ▸ hk) h.2 odd⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel {k : Nat} (hk : k < rr s₀) :
    RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) fusedBody fun s t =>
      (Inv s₀ (k + 1) s ∧ s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) ∧
      (Inv s₀' (k + 1) t ∧ t.zf = some (BitVec.ofNat 64 (rr s₀' - k) - 1 == 0)) := by
  have tail : RelCT isa (fun s t => Ready s₀ k s ∧ Ready s₀' k t) (.block fusedTail) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rsi]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      rw [h.1.rsi, h.2.rsi, sc, sc, hq.r8]) (by taint_decide)
  have ct := ((half_rel hp hp' hq hk false).seq ((half_rel hp hp' hq hk true).seq tail)).mono
    (P' := fun s t => Inv s₀ k s ∧ Inv s₀' k t) (fun _ _ h => ⟨h.1.ready, h.2.ready⟩) (fun _ _ h => h)
  exact (ct.wp fun _ _ h => ⟨body_ok hp hk h.1, body_ok hp' (hq.rr ▸ hk) h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop fusedBody .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := fusedBody) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega_using [hn, hk], k + 1, rfl, by omega_using [hk, hl], i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') blockMixFused fun _ _ => True := by
  unfold blockMixFused
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (bmPrologue ++ fusedSetup))
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block (bmPrologue ++ fusedSetup)) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block (bmSaved.map fun (r, d) => .mov r (.mem (at_ .rsi d))))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rsi]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.words.rsi, h.2.words.rsi, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end

/-! ### `Scrypt.X86_64.FusedCorrect`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (InRegions.of_mem)
theorem loop_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop fusedBody .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  rw [eval_ne hp hk hz]
  by_cases hl : k + 1 = rr s₀
  · exact .inl ⟨by simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [hl], rr s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block (bmSaved.map fun (r, d) => .mov r (.mem (at_ .rsi d)))) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .rsi bmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.words.rsi]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := saved_bound p hp'
  rw [h.words.rsi, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega_using [this]))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa blockMixFused s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86_64.post s₀ s' := by
  unfold blockMixFused
  refine WP.seq (WP.mono (prologue_ok hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_y
    · exact hp.ret_s
    · exact ret_stk s₀
  · show Spec.Scrypt.bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

end

end


@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64
theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.blockMixFused s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.blockMixFused := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Scrypt.X86_64.BlockMix.Fused
