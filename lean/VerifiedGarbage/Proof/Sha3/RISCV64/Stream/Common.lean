module

import VerifiedGarbage.Proof.Sha3.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# The SHA-3 sponge on RISC-V: the frame of `absorb` and `squeeze`

`absorb` and `squeeze` run in a frame of 560 bytes (`withLoop`): the
permutation's scratch space, then the saved return address and `s2`–`s6`.
With the permutation's own frame below it, they use the 1168 bytes below the
stack pointer (`K`). `setup_ok` saves the registers, `Saved` says the frame
still holds them, and `epilogue_ok` returns the position and restores them.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream

section
variable (s₀ : State)

/-- The stack below the stack pointer that the function and the permutation use. -/
abbrev K : Addr := s₀.sp - BitVec.ofNat 64 1168
abbrev KR : Region := ⟨K s₀, 1168⟩
/-- The frame's base. -/
abbrev B : Addr := s₀.sp - BitVec.ofNat 64 560
/-- The frame's region. -/
abbrev BR : Region := ⟨B s₀, 560⟩

end

/-- The stack pointer: aligned, with room for the frames. -/
structure Stk (s₀ : State) : Prop where
  al : s₀.sp.toNat % 16 = 0
  sp : 1168 ≤ s₀.sp.toNat

/-- The parts of the stack used. -/
theorem sub_K (s₀ : State) {d n : Nat} (h : d + n ≤ 1168) :
    Region.Sub ⟨K s₀ + BitVec.ofNat 64 d, n⟩ (KR s₀) :=
  Offset.sub_base _ h

/-- The slots of the saved registers are not in the permutation's scratch
space. -/
theorem slot_scr (s₀ : State) {d : Nat} (h : 512 ≤ d) (h' : d + 8 ≤ 560) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀, 512⟩ :=
  Offset.disjoint_base _ (by omega) (by omega)

namespace Stk
variable {s₀ : State} (hk : Stk s₀)
include hk

theorem B_eq : B s₀ = K s₀ + BitVec.ofNat 64 608 := by
  have := hk.sp
  simp only [B, K]; bv_omega

theorem B_toNat : (B s₀).toNat = s₀.sp.toNat - 560 := by
  have := hk.sp
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]

theorem B_al : (B s₀).toNat % 16 = 0 := by
  rw [hk.B_toNat]; have := hk.al; have := hk.sp; omega

theorem B_608 : 608 ≤ (B s₀).toNat := by rw [hk.B_toNat]; have := hk.sp; omega

theorem below_eq : B s₀ - 608 = K s₀ := by
  rw [hk.B_eq]; exact BitVec.add_sub_cancel _ _

theorem B_off (d : Nat) : B s₀ + BitVec.ofNat 64 d = K s₀ + BitVec.ofNat 64 (608 + d) := by
  rw [hk.B_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem scr_sub : Region.Sub ⟨B s₀, 512⟩ (KR s₀) := by
  rw [show B s₀ = K s₀ + BitVec.ofNat 64 608 from hk.B_eq]; exact sub_K s₀ (by omega)

theorem below_sub : Region.Sub ⟨B s₀ - 608, 608⟩ (KR s₀) := by
  rw [hk.below_eq]; simpa using sub_K s₀ (d := 0) (n := 608) (by omega)

theorem BR_sub : Region.Sub (BR s₀) (KR s₀) := by
  simp only [BR]
  rw [show B s₀ = K s₀ + BitVec.ofNat 64 608 from hk.B_eq]; exact sub_K s₀ (by omega)

/-- A slot of the saved registers. -/
theorem slot_sub {d : Nat} (h : 512 ≤ d) (h' : d + 8 ≤ 560) :
    Region.Sub ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ (KR s₀) := by
  rw [hk.B_off]; exact sub_K s₀ (by omega)

theorem slot_below {d : Nat} (h : 512 ≤ d) (h' : d + 8 ≤ 560) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀ - 608, 608⟩ := by
  rw [hk.below_eq, hk.B_off]; exact Offset.disjoint_base _ (by omega) (by omega)

end Stk

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 ∧ p.2 % 8 = 0 := by decide

/-- The frame at `b` holds the caller's registers `g`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- Writes outside the slots keep them. -/
theorem Saved.frame {b : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved b g m) {rs : List Region}
    (hd : ∀ d, 512 ≤ d → d + 8 ≤ 560 → ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ r)
    (hf : Frame rs m m') : Saved b g m' := fun p hp => by
  have := saved_bound p hp
  rw [hf.readW (Region.contains_self _ _) (hd _ this.1 this.2.1) (by decide)]
  exact h p hp

theorem readW_writeW_off (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 =
      m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem save_eq : save = [.addSp .t0 0, .store .d .ra .t0 512, .store .d .s2 .t0 520,
    .store .d .s3 .t0 528, .store .d .s4 .t0 536, .store .d .s5 .t0 544, .store .d .s6 .t0 552] := rfl

/-- Saving the registers in the frame at the stack pointer. -/
theorem save_ok {rest : List Instr} {s : State} {Q : State → Prop} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8)
    (k : ∀ s', (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Saved s.sp s.gpr s'.mem → Frame [⟨s.sp + BitVec.ofNat 64 512, 48⟩] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₀ u₀ => ?_
  have g0 : s₀.gpr .t0 = s.sp := by rw [u₀.gpr]; exact BitVec.add_zero _
  have o : ∀ r, r ≠ .t0 → s₀.gpr r = s.gpr r := u₀.other
  have st : ∀ d, d % 8 = 0 → 512 ≤ d → d + 8 ≤ 560 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s'.wr (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₁ h₂ s' h₀ hw => ⟨by rw [h₀], al8 hal hd (by omega), by rw [hw]; exact hin d h₁ h₂⟩
  have hc : ∀ d, 512 ≤ d → d + 8 ≤ 560 →
      (⟨s.sp + BitVec.ofNat 64 512, 48⟩ : Region).Contains (s.sp + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  obtain ⟨a1, l1, i1⟩ := st 512 (by decide) (by omega) (by omega) s₀ g0 u₀.wr
  refine wp_sd (by decide) a1 l1 i1 fun s₁ g₁ => ?_
  obtain ⟨a2, l2, i2⟩ := st 520 (by decide) (by omega) (by omega) s₁ (by rw [g₁.gpr, g0])
    (by rw [g₁.wr, u₀.wr])
  refine wp_sd (by decide) a2 l2 i2 fun s₂ g₂ => ?_
  obtain ⟨a3, l3, i3⟩ := st 528 (by decide) (by omega) (by omega) s₂ (by rw [g₂.gpr, g₁.gpr, g0])
    (by rw [g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a3 l3 i3 fun s₃ g₃ => ?_
  obtain ⟨a4, l4, i4⟩ := st 536 (by decide) (by omega) (by omega) s₃
    (by rw [g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a4 l4 i4 fun s₄ g₄ => ?_
  obtain ⟨a5, l5, i5⟩ := st 544 (by decide) (by omega) (by omega) s₄
    (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a5 l5 i5 fun s₅ g₅ => ?_
  obtain ⟨a6, l6, i6⟩ := st 552 (by decide) (by omega) (by omega) s₅
    (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a6 l6 i6 fun s₆ g₆ => ?_
  have gg : s₆.gpr = s₀.gpr := by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  have hm : s₆.mem = (((((s.mem.writeW (s.sp + BitVec.ofNat 64 512) (s.gpr .ra)).writeW
      (s.sp + BitVec.ofNat 64 520) (s.gpr .s2)).writeW (s.sp + BitVec.ofNat 64 528) (s.gpr .s3)).writeW
      (s.sp + BitVec.ofNat 64 536) (s.gpr .s4)).writeW (s.sp + BitVec.ofNat 64 544) (s.gpr .s5)).writeW
      (s.sp + BitVec.ofNat 64 552) (s.gpr .s6) := by
    rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem, u₀.mem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr,
      g₁.gpr, o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide),
      o _ (by decide)]
  refine k s₆ (fun r hr => by rw [gg, o r hr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, u₀.rd])
    (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp, u₀.sp]) (fun p hp => ?_) ?_
  · rw [hm]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [Mem.readW_writeW_self64, readW_writeW_off]
  · rw [hm]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 512 (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (hc 520 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (hc 528 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (hc 536 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (hc 544 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (hc 552 (by omega) (by omega))

theorem restore_eq : restore = [.addSp .t0 0, .load .d .ra .t0 512, .load .d .s2 .t0 520,
    .load .d .s3 .t0 528, .load .d .s4 .t0 536, .load .d .s5 .t0 544, .load .d .s6 .t0 552] := rfl

/-- Returning the position and restoring the registers from the frame at the
stack pointer. -/
theorem epilogue_ok {s : State} {g : Reg → BitVec 64} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8)
    (hsv : Saved s.sp g s.mem) {Q : State → Prop}
    (k : ∀ s', s'.gpr .a0 = s.gpr .s4 → (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → r ≠ .a0 → r ≠ .t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (mov .a0 .s4 :: restore)) s Q := by
  refine wp_mv fun s₀ u₀ => ?_
  rw [restore_eq]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have g1 : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, u₀.sp]; exact BitVec.add_zero _
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  have ld : ∀ d, d % 8 = 0 → 512 ≤ d → d + 8 ≤ 560 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions (s'.rd ++ s'.wr) (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₁ h₂ s' h₀ hr hw => ⟨by rw [h₀], al8 hal hd (by omega), by rw [hr, hw]; exact hin d h₁ h₂⟩
  have rd₁ : s₁.rd = s.rd := by rw [u₁.rd, u₀.rd]
  have wr₁ : s₁.wr = s.wr := by rw [u₁.wr, u₀.wr]
  have m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  obtain ⟨a1, l1, i1⟩ := ld 512 (by decide) (by omega) (by omega) s₁ g1 rd₁ wr₁
  refine wp_ld (by decide) a1 l1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, l2, i2⟩ := ld 520 (by decide) (by omega) (by omega) s₂
    (by rw [u₂.other _ (by decide), g1]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁])
  refine wp_ld (by decide) a2 l2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, l3, i3⟩ := ld 528 (by decide) (by omega) (by omega) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g1]) (by rw [u₃.rd, u₂.rd, rd₁])
    (by rw [u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a3 l3 i3 fun s₄ u₄ => ?_
  obtain ⟨a4, l4, i4⟩ := ld 536 (by decide) (by omega) (by omega) s₄
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a4 l4 i4 fun s₅ u₅ => ?_
  obtain ⟨a5, l5, i5⟩ := ld 544 (by decide) (by omega) (by omega) s₅
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g1])
    (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a5 l5 i5 fun s₆ u₆ => ?_
  obtain ⟨a6, l6, i6⟩ := ld 552 (by decide) (by omega) (by omega) s₆
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a6 l6 i6 fun s₇ u₇ => WP.block_nil ?_
  have mm : ∀ (x : State), x.mem = s₁.mem → x.mem = s.mem := fun x h => h.trans m₁
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine k s₇ ?_ (fun p hp => ?_) (fun r hr h0 ht => ?_) m₇
    (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
    (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      u₀.gpr]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, v .ra 512 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁, v .s2 520 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem,
        u₂.mem, m₁, v .s3 528 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s4 536 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s5 544 (by simp [saved])]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, v .s6 552 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₇.other _ h6, u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1,
      u₁.other _ ht, u₀.other _ h0]

/-! ## The test for a lane -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

private theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

private theorem wp_andi7 {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& 7) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n 7 :: is)) s Q :=
  WP.cons (exec_logicImm (by decide)) (k _ (Upd.write _ _ _))

private theorem wp_sltu {d n m : Reg}
    (k : ∀ s', Upd s s' d (if s.gpr n < s.gpr m then 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.sltu d n m :: is)) s Q :=
  WP.cons exec_sltu (k _ (Upd.write _ _ _))

end

private theorem and7_eq_zero {x : BitVec 64} (h : x &&& 7 = 0) : x.toNat % 8 = 0 := by
  have h' := congrArg BitVec.toNat h
  rwa [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h'

/-- `laneCheck`, from `s2` = `st`, `s4` = `j` and `s6` = `n`: it changes only
`t1`–`t4`, leaves `st + j` in `t2`, and leaves `t1 = 0` only if `j`, `st + j`
and `s5` are multiples of 8 and `n ≥ 8`. -/
theorem laneCheck_ok {s : State} {st : Addr} {j n : Nat} (h2 : s.gpr .s2 = st)
    (h4 : s.gpr .s4 = BitVec.ofNat 64 j) (h6 : s.gpr .s6 = BitVec.ofNat 64 n) (hj : j < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    WP isa (.block laneCheck) s fun s' =>
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.gpr .t2 = st + BitVec.ofNat 64 j ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧
      (s'.gpr .t1 = 0 → j % 8 = 0 ∧ (st + BitVec.ofNat 64 j).toNat % 8 = 0 ∧
        (s.gpr .s5).toNat % 8 = 0 ∧ 8 ≤ n) := by
  unfold laneCheck
  refine wp_add fun s₁ u₁ => wp_or fun s₂ u₂ => wp_or fun s₃ u₃ => wp_andi7 fun s₄ u₄ =>
    wp_li (by decide) fun s₅ u₅ => wp_sltu fun s₆ u₆ => wp_or fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₇.other r h1, u₆.other r h3, u₅.other r h4, u₄.other r h1, u₃.other r h1,
        u₂.other r h1, u₁.other r h2]
  have ht2 : s₇.gpr .t2 = st + BitVec.ofNat 64 j := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2, h4]
  refine ⟨g, ht2, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], fun hz => ?_⟩
  have e6 : s₅.gpr .s6 = BitVec.ofNat 64 n := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h6]
  have e4 : s₂.gpr .s4 = BitVec.ofNat 64 j := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), h4]
  have e5 : s₁.gpr .s5 = s.gpr .s5 := u₁.other _ (by decide)
  have e2 : s₁.gpr .t2 = st + BitVec.ofNat 64 j := by rw [u₁.gpr, h2, h4]
  rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr,
    u₃.gpr, u₂.gpr, e6, e4, e5, e2] at hz
  obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hz
  rw [BitVec.and_or_distrib_right, BitVec.and_or_distrib_right] at ha
  obtain ⟨ha, h₃⟩ := BitVec.or_eq_zero_iff.mp ha
  obtain ⟨h₁, h₂⟩ := BitVec.or_eq_zero_iff.mp ha
  have h₃' := and7_eq_zero h₃
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at h₃'
  refine ⟨h₃', and7_eq_zero h₁, and7_eq_zero h₂, ?_⟩
  by_cases hl : BitVec.ofNat 64 n < 8#64
  · rw [ite_eq_left hl] at hb; exact absurd hb (by decide)
  · rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hl
    exact Nat.le_of_not_lt hl

end VG.Proof.Sha3.RISCV64.Stream
