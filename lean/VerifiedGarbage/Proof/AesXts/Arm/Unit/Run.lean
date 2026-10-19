module
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Call
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Contract

import VerifiedGarbage.Proof.AesXts.Arm.Unit.Pre
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Steps
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.AesCbc.Mem32

/-!
# XTS-AES of data units on ARMv7: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `r4`, `r5`, `r7`,
`r8` and `r9`, its caller's callee-saved registers (but `r10` and `r11`,
which it keeps in place) and its return address in their slots, and changes
memory only in the data, the scratch buffer and the 16 bytes below the stack
pointer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.MdStream.Arm (op2_reg wp_mov wp_ldrSp)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak, as addresses and as register values. -/
abbrev Tp : Addr := Sa s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := Sa s₀ + BitVec.ofNat 64 zO
abbrev Tv : BitVec 32 := S s₀ + BitVec.ofNat 32 tO
abbrev Zv : BitVec 32 := S s₀ + BitVec.ofNat 32 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (State.addr (K s₀)) (16 * (R s₀ + 1)))
    (bytesAt s₀.mem (State.addr (I s₀)) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher :=
  ciphOf enc (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r2
  r7 : s.gpr .r7 = stackArg s₀ 1
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = D s₀
  rest : ∀ r ∈ ([.r10, .r11] : List Reg), s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (Sa s₀) s₀.gpr saved

theorem saved_slots : Spill.Slots 2208 2236 saved := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11]

theorem rest_pinned : ∀ r ∈ ([.r10, .r11] : List Reg), r ∈ pinned := by decide

theorem pinned_pres : ∀ r ∈ pinned, r ∈ preserved ∧ r ≠ .lr := by decide

theorem r1_ofNat (s₀ : State) : BitVec.ofNat 32 (R s₀) = s₀.gpr .r2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data, the first 2208 bytes of the scratch buffer or the
stack below the stack pointer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨Sa s₀, 2208⟩ ∨ Region.Sub r (stkR s₀))
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  r4 := by rw [hg _ (by simp), h.r4]
  r5 := by rw [hg _ (by simp), h.r5]
  r7 := by rw [hg _ (by simp), h.r7]
  r8 := by rw [hg _ (by simp), h.r8]
  r9 := by rw [hg _ (by simp), h.r9]
  rest r hr := by rw [hg r (rest_pinned r hr), h.rest r hr]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stkR s₀, by simp, h⟩)
  saved := h.saved.frame saved_slots hf fun r hr => hp.slots_disj (hrs r hr)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : BitVec 32} {N Rr : Nat}
    (hT : Region.Sub ⟨State.addr T, 16⟩ ⟨Sa s₀, 2208⟩)
    (hD : Region.Sub ⟨State.addr Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨State.addr Dd, 16 * N⟩ ⟨Sa s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨State.addr T, 16⟩, ⟨State.addr Dd, 16 * N⟩, ⟨State.addr (S s₀), 2176⟩, stk16 s.sp])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [UPre.stk_eq h.sp]; exact fun _ h => h)))
    hc.frame (fun r hr => hc.saved r (pinned_pres r hr).1 (pinned_pres r hr).2) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zv s₀) (Tv s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (State.addr (I s₀)) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem UPre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  have := hp.sp_fit
  have e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
    simp only [stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega)]
    simp
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The slots, as seen from the memory after the saves. -/
theorem slots_in (d : Nat) (h₁ : d + 4 ≤ 2432) :
    InRegions s₀.wr (Sa s₀ + BitVec.ofNat 64 d) 4 := by
  rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ h₁)

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  have hsc := hp.scr_fit
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, save, List.cons_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_slots.bound hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, slots_in hp _ (by omega)⟩
  rw [h12, u₁.mem] at m₂
  have f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by
    rw [m₂]
    exact (Spill.saveMem_frame_slots saved_slots s₀.mem (Sa s₀) s₁.gpr).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, scr_sub (by decide)⟩
  have harg (k : Nat) (hk : k < 3) : s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
    refine f₂.readW (r := ⟨stackArgAddr s₀ k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp_fit
    refine (hp.scr_args.sub_right ?_).symm
    have e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
      simp only [stackArgAddr]
      rw [addr_add (by omega), addr_add (by omega)]
      simp
    rw [e]; exact Offset.sub_base _ (by omega)
  -- `setup`
  simp only [setup, mov, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  have sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have rdwr₅ : s₅.rd ++ s₅.wr = s₀.rd ++ s₀.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [sp₅]; rfl)
    (by rw [rdwr₅]; exact hp.arg_in (by decide)) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₆.sp, sp₅]; rfl)
    (by rw [u₆.rd, u₆.wr, rdwr₅]; exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r8₇ : s₇.gpr .r8 = S s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, h12]
  have k₇ : ∀ r, r ≠ .r8 → r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → r ≠ .r7 → r ≠ .r12 → s₇.gpr r = s₀.gpr r :=
    fun r h8 h4 h5 h9 h7 h12' => by
      rw [u₇.other r h7, u₆.other r h9, u₅.other r h5, u₄.other r h4, u₃.other r h8, congrFun g₂ r,
        u₁.other r h12']
  have r4₇ : s₇.gpr .r4 = W s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  have r5₇ : s₇.gpr .r5 = s₀.gpr .r2 := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  have r9₇ : s₇.gpr .r9 = D s₀ := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 0 (by decide)]
  have r7₇ : s₇.gpr .r7 = stackArg s₀ 1 := by
    rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, sp₅]
  have rdwr₇ : s₇.rd ++ s₇.wr = [schR s₀, tschR s₀, iR s₀, argsR s₀, dataR s₀, scrR s₀] := by
    rw [rd₇, wr₇, hp.rd, hp.wr]; rfl
  have wr₇' : s₇.wr = [dataR s₀, scrR s₀] := by rw [wr₇]; exact hp.wr
  -- The copy of `i`.
  rw [WP.block_append_iff]
  have r3₇ : s₇.gpr .r3 = I s₀ := k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₈, run₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ := copyI_ok s₇ (P := Tp s₀) (Q := State.addr (I s₀))
    (by rw [r3₇]; simp) (by rw [r3₇]; have := hp.i_fit; omega) (by rw [r8₇])
    (by rw [r8₇]; simp only [tO]; omega)
    (fun d n h => by
      rw [rdwr₇]
      exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ h (by omega)))
    (fun d n h => by rw [wr₇']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [tO]; omega)))
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  rw [WP.block_append_iff]
  have r8₈ : s₈.gpr .r8 = S s₀ := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  have wr₈' : s₈.wr = [dataR s₀, scrR s₀] := by rw [wr₈, wr₇']
  obtain ⟨s₉, run₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ := zeroZ_ok s₈ (Z := Zp s₀) (by rw [r8₈])
    (by rw [r8₈]; simp only [zO]; omega)
    (fun d n h => by rw [wr₈']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [zO]; omega)))
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  obtain ⟨s₁₀, run₁₀, x0, x1, x2, x3, x12, xlr, cs₁₀, sp₁₀', mem₁₀, rd₁₀, wr₁₀⟩ := tArgs_ok s₉
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  -- The registers.
  have k₉ : ∀ r, r ≠ .r12 → r ≠ .lr → r ≠ .r0 → r ≠ .r2 → s₉.gpr r = s₇.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g₉ r h₁, g₈ r h₁ h₂ h₃ h₄]
  have r8₉ : s₉.gpr .r8 = S s₀ := by rw [k₉ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  have cs (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) : s₁₀.gpr r = s₇.gpr r := by
    have := preserved_ne r hr hl
    rw [cs₁₀ r hr hl, k₉ r this.2.2.2.2 hl this.1 this.2.2.1]
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇]
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇]
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [sp₁₀', sp₉, sp₈, sp₇]
  -- The memory.
  have f₈ : Frame [⟨Tp s₀, 16⟩] s₇.mem s₈.mem := by rw [mem₈]; exact copy4_frame _ _ _
  have f₉ : Frame [⟨Zp s₀, 16⟩] s₈.mem s₉.mem := by rw [mem₉]; exact zero4_frame _ _
  have f₇ : Frame [scrR s₀] s₀.mem s₇.mem := by rw [m₇]; exact f₂
  have frame : Frame [scrR s₀] s₀.mem s₁₀.mem := by
    rw [mem₁₀]
    refine f₇.trans ((f₈.sub fun r hr => ?_).trans (f₉.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  have sv₇ : Spill.Saved s₇.mem (Sa s₀) s₀.gpr saved := by
    intro p hp'
    rw [m₇, m₂, Spill.saveMem_saved (Sa s₀) s₁.gpr s₀.mem saved saved_slots p hp']
    have hne : p.1 ≠ .r12 := by revert hp'; revert p; decide
    exact u₁.other _ hne
  have sdisj : ∀ (r : Region), Region.Sub r ⟨Sa s₀, 2208⟩ → ∀ r' ∈ [r],
      Region.Disjoint ⟨Sa s₀ + BitVec.ofNat 64 2208, 2236 - 2208⟩ r' := fun r hr r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hp.slots_disj (.inr (.inl hr))
  have sv₁₀ : Spill.Saved s₁₀.mem (Sa s₀) s₀.gpr saved := by
    rw [mem₁₀, mem₉]
    exact (sv₇.frame saved_slots f₈ (sdisj _ t_sub)).frame saved_slots (zero4_frame _ _) (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [preserved]) (by decide), r4₇], by rw [cs _ (by simp [preserved]) (by decide), r5₇],
    by rw [cs _ (by simp [preserved]) (by decide), r7₇], by rw [cs _ (by simp [preserved]) (by decide), r8₇],
    by rw [cs _ (by simp [preserved]) (by decide), r9₇], fun r hr => by
      have hr' : r ∈ preserved ∧ r ≠ .lr := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
      rw [cs r hr'.1 hr'.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp₁₀, rd₁₀', wr₁₀',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₁₀⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₁₀' wr₁₀' sp₁₀ ?_ ?_ (by rw [x2, r8₉]) (by rw [x3, r8₉]) x12 (by rw [xlr, r8₉])
    · rw [x0, k₉ _ (by decide) (by decide) (by decide) (by decide),
        k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x1, k₉ _ (by decide) (by decide) (by decide) (by decide), r5₇, r1_ofNat]
  · rw [mem₁₀, mem₉, Proof.Cmac.bytesAt_frame (zero4_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₈, copy4_bytes, m₇,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₁₀, mem₉, zero4_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stkR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stkR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {s₂ : State} (h₂ : ProPost s₀ s₂) : WP isa encCall s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have stk := UPre.stk_eq (s₀ := s₀) h₂.inv.sp
  have aT := hp.scrA (d := tO) (by decide)
  have aZ := hp.scrA (d := zO) (by decide)
  have eK : bytesAt s₂.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) =
      bytesAt s₀.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega)
  refine ⟨Inv.call hp h₂.inv (by rw [aZ]; exact z_sub) (.inr (by rw [aT]; exact t_sub)) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aZ]; exact sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩
  · have o := c.out
    rw [aZ, aT] at o
    have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (State.addr (K s₀)) (16 * (R s₀ + 1)))
      o h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp : WP isa tweak s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (Da s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length))) s
      (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc hpre) fun s' x => ?_
  have aT := hp.scrA (d := tO) (by decide)
  have stk := UPre.stk_eq (s₀ := s₀) h.inv.sp
  have dS : Region.Sub ⟨Da s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (Da s₀) N = Spec.Cbc.blocksAt s₀.mem (Da s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_fit; omega)
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl dS) x, ?_, ?_, ?_⟩
  · have o := x.out
    rw [aT] at o
    rw [o, eW, h.t, eD]
  · have o := x.tw
    rw [aT] at o
    rw [o, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (pinned_pres r hr).1 (pinned_pres r hr).2) hsp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

omit hp in
theorem restore_eq :
    restore = (saved.take 6 ++ [((Reg.r8, 2232) : Reg × Nat)]).map (fun (p : Reg × Nat) => Instr.ldr p.1 .r8 p.2) ++
      [] := rfl

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  have hsv : Spill.Saved s.mem (State.addr (s.gpr .r8)) s₀.gpr (saved.take 6 ++ [((Reg.r8, 2232) : Reg × Nat)]) := by
    rw [h.r8]; exact h.saved
  refine Spill.restoreBase_slots_ok (lo := 2208) (hi := 2236) (by decide) (by decide)
    (by rw [h.r8]; have := hp.scr_fit; omega) (fun d h₁ h₂ => ?_) hsv
    fun s' ld ho m _ _ sp => WP.block_nil ⟨⟨fun r hr => ?_, by rw [sp, h.sp]⟩, m⟩
  · rw [h.rd, h.wr, h.r8, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ (by omega))
  · by_cases hs : r ∈ (saved.take 6 ++ [(Reg.r8, 2232)]).map Prod.fst
    · exact Spill.restored_reg ld hs
    · have hk : ∀ r ∈ preserved, r ∉ (saved.take 6 ++ [(Reg.r8, 2232)]).map Prod.fst → r = .r10 ∨ r = .r11 := by
        decide
      rw [ho r hs]
      rcases hk r hr hs with rfl | rfl
      · exact h.rest _ (by simp)
      · exact h.rest _ (by simp)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : BitVec 32} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨State.addr Dd, 16 * N⟩)
    (hT : Region.Sub ⟨State.addr T, 16⟩ (scrR s₀)) (hsp : s.sp = s₀.sp)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [UPre.stk_eq hsp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.Arm.Unit
