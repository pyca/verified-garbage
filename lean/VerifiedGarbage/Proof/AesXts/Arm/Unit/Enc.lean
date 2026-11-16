module

public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Call
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Contract
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Pre
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Steps
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesXts.Arm.Unit.Run`, which only this module used -/

section

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
  obtain e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
    simp only [stackArgAddr]
    rw [addr_add (by omega_using [hk, this]), addr_add (by omega_using [])]
    simp
  rw [e]
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

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
    exact ⟨by omega_using [hb], by omega_using [hsc, hb], slots_in hp _ (by omega_using [hb])⟩
  rw [h12, u₁.mem] at m₂
  obtain f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by
    rw [m₂]
    exact (Spill.saveMem_frame_slots saved_slots s₀.mem (Sa s₀) s₁.gpr).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, scr_sub (by decide)⟩
  have harg (k : Nat) (hk : k < 3) : s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
    refine f₂.readW (r := ⟨stackArgAddr s₀ k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp_fit
    refine (hp.scr_args.sub_right ?_).symm
    obtain e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
      simp only [stackArgAddr]
      rw [addr_add (by omega_using [hk, this]), addr_add (by omega_using [])]
      simp
    rw [e]; exact Offset.sub_base _ (by omega_using [hk])
  -- `setup`
  simp only [setup, mov, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  obtain sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  obtain rdwr₅ : s₅.rd ++ s₅.wr = s₀.rd ++ s₀.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [sp₅]; rfl)
    (by rw [rdwr₅]; exact hp.arg_in (by decide)) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₆.sp, sp₅]; rfl)
    (by rw [u₆.rd, u₆.wr, rdwr₅]; exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  obtain m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain r8₇ : s₇.gpr .r8 = S s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, h12]
  obtain k₇ : ∀ r, r ≠ .r8 → r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → r ≠ .r7 → r ≠ .r12 → s₇.gpr r = s₀.gpr r :=
    fun r h8 h4 h5 h9 h7 h12' => by
      rw [u₇.other r h7, u₆.other r h9, u₅.other r h5, u₄.other r h4, u₃.other r h8, congrFun g₂ r,
        u₁.other r h12']
  obtain r4₇ : s₇.gpr .r4 = W s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  obtain r5₇ : s₇.gpr .r5 = s₀.gpr .r2 := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  obtain r9₇ : s₇.gpr .r9 = D s₀ := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 0 (by decide)]
  obtain r7₇ : s₇.gpr .r7 = stackArg s₀ 1 := by
    rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, sp₅]
  obtain rdwr₇ : s₇.rd ++ s₇.wr = [schR s₀, tschR s₀, iR s₀, argsR s₀, dataR s₀, scrR s₀] := by
    rw [rd₇, wr₇, hp.rd, hp.wr]; rfl
  obtain wr₇' : s₇.wr = [dataR s₀, scrR s₀] := by rw [wr₇]; exact hp.wr
  -- The copy of `i`.
  rw [WP.block_append_iff]
  obtain r3₇ : s₇.gpr .r3 = I s₀ := k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₈, run₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ := copyI_ok s₇ (P := Tp s₀) (Q := State.addr (I s₀))
    (by rw [r3₇]; simp) (by rw [r3₇]; have := hp.i_fit; omega_using [this]) (by rw [r8₇])
    (by rw [r8₇]; simp only [tO]; omega_using [hsc])
    (fun d n h => by
      rw [rdwr₇]
      exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ h (by omega_using [h])))
    (fun d n h => by rw [wr₇']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [tO]; omega_using [h])))
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  rw [WP.block_append_iff]
  obtain r8₈ : s₈.gpr .r8 = S s₀ := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  obtain wr₈' : s₈.wr = [dataR s₀, scrR s₀] := by rw [wr₈, wr₇']
  obtain ⟨s₉, run₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ := zeroZ_ok s₈ (Z := Zp s₀) (by rw [r8₈])
    (by rw [r8₈]; simp only [zO]; omega_using [hsc])
    (fun d n h => by rw [wr₈']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [zO]; omega_using [h])))
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  obtain ⟨s₁₀, run₁₀, x0, x1, x2, x3, x12, xlr, cs₁₀, sp₁₀', mem₁₀, rd₁₀, wr₁₀⟩ := tArgs_ok s₉
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  -- The registers.
  obtain k₉ : ∀ r, r ≠ .r12 → r ≠ .lr → r ≠ .r0 → r ≠ .r2 → s₉.gpr r = s₇.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g₉ r h₁, g₈ r h₁ h₂ h₃ h₄]
  obtain r8₉ : s₉.gpr .r8 = S s₀ := by rw [k₉ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  have cs (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) : s₁₀.gpr r = s₇.gpr r := by
    have := preserved_ne r hr hl
    rw [cs₁₀ r hr hl, k₉ r this.2.2.2.2 hl this.1 this.2.2.1]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇]
  obtain sp₁₀ : s₁₀.sp = s₀.sp := by rw [sp₁₀', sp₉, sp₈, sp₇]
  -- The memory.
  obtain f₈ : Frame [⟨Tp s₀, 16⟩] s₇.mem s₈.mem := by rw [mem₈]; exact copy4_frame _ _ _
  obtain f₉ : Frame [⟨Zp s₀, 16⟩] s₈.mem s₉.mem := by rw [mem₉]; exact zero4_frame _ _
  obtain f₇ : Frame [scrR s₀] s₀.mem s₇.mem := by rw [m₇]; exact f₂
  obtain frame : Frame [scrR s₀] s₀.mem s₁₀.mem := by
    rw [mem₁₀]
    refine f₇.trans ((f₈.sub fun r hr => ?_).trans (f₉.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  obtain sv₇ : Spill.Saved s₇.mem (Sa s₀) s₀.gpr saved := by
    intro p hp'
    rw [m₇, m₂, Spill.saveMem_saved (Sa s₀) s₁.gpr s₀.mem saved saved_slots p hp']
    obtain hne : p.1 ≠ .r12 := by revert hp'; revert p; decide
    exact u₁.other _ hne
  obtain sdisj : ∀ (r : Region), Region.Sub r ⟨Sa s₀, 2208⟩ → ∀ r' ∈ [r],
      Region.Disjoint ⟨Sa s₀ + BitVec.ofNat 64 2208, 2236 - 2208⟩ r' := fun r hr r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hp.slots_disj (.inr (.inl hr))
  obtain sv₁₀ : Spill.Saved s₁₀.mem (Sa s₀) s₀.gpr saved := by
    rw [mem₁₀, mem₉]
    exact (sv₇.frame saved_slots f₈ (sdisj _ t_sub)).frame saved_slots (zero4_frame _ _) (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [preserved]) (by decide), r4₇], by rw [cs _ (by simp [preserved]) (by decide), r5₇],
    by rw [cs _ (by simp [preserved]) (by decide), r7₇], by rw [cs _ (by simp [preserved]) (by decide), r8₇],
    by rw [cs _ (by simp [preserved]) (by decide), r9₇], fun r hr => by
      obtain hr' : r ∈ preserved ∧ r ≠ .lr := by
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
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {s₂ : State} (h₂ : ProPost s₀ s₂) : WP isa encCall s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain stk := UPre.stk_eq (s₀ := s₀) h₂.inv.sp
  obtain aT := hp.scrA (d := tO) (by decide)
  obtain aZ := hp.scrA (d := zO) (by decide)
  obtain eK : bytesAt s₂.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) =
      bytesAt s₀.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
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
  obtain aT := hp.scrA (d := tO) (by decide)
  obtain stk := UPre.stk_eq (s₀ := s₀) h.inv.sp
  obtain dS : Region.Sub ⟨Da s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (Da s₀) N = Spec.Cbc.blocksAt s₀.mem (Da s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_fit; omega_using [hN, this])
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
  obtain hsv : Spill.Saved s.mem (State.addr (s.gpr .r8)) s₀.gpr (saved.take 6 ++ [((Reg.r8, 2232) : Reg × Nat)]) := by
    rw [h.r8]; exact h.saved
  refine Spill.restoreBase_slots_ok (lo := 2208) (hi := 2236) (by decide) (by decide)
    (by rw [h.r8]; have := hp.scr_fit; omega_using [this]) (fun d h₁ h₂ => ?_) hsv
    fun s' ld ho m _ _ sp => WP.block_nil ⟨⟨fun r hr => ?_, by rw [sp, h.sp]⟩, m⟩
  · rw [h.rd, h.wr, h.r8, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ (by omega_using [h₂]))
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

end

end


/-!
# XTS-AES of data units on ARMv7: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue. The
data unit is `encWith` of the cipher and the tweak, which is
`aesXtsEncrypt` of any key whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (Da s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (Da s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  r0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (B s₀)
  z : s.z = decide (B s₀ = 0)

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- `r9 + r0 − 16` is the last whole block. -/
theorem last_of {s : State} (h9 : s.gpr .r9 = D s₀) (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) :
    s.gpr .r9 + s.gpr .r0 - 16 = Lv s₀ := by
  rw [h9, h0, last_eq _ hp.m_pos]

theorem UPre.l_fit : (Lv s₀).toNat + 16 + B s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := len_eq s₀; have := hp.m_pos
  rw [hp.dataN (by omega_arith)]
  omega_arith

theorem UPre.lb_in {s : State} (hwr : s.wr = s₀.wr) (i : Nat) (hi : i < 16 + B s₀) :
    InRegions s.wr (L s₀ + BitVec.ofNat 64 i) 1 := by
  have : B s₀ < 16 := Nat.mod_lt _ (by decide)
  rw [hwr, hp.wr]
  exact in_rw (r := dataR s₀) (by simp)
    (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi]) (by omega_using [hi, this])))

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) (h1 : s.gpr .r1 = BitVec.ofNat 32 (B s₀))
    (h2 : s.gpr .r2 = Lv s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (swap_ok s (Nat.pos_of_ne_zero hB) hb (by rw [h2]; exact hp.lA)
      (by rw [h2]; exact hp.l_fit) h1 (hp.lb_in hi.wr))
    fun s₂ ⟨mem₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x12₃, lr₃, cs₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    argsL_ok s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₂ _ (by decide) (by decide) (by decide) (by decide)
  obtain inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ sp₂ rd₂ wr₂
  obtain inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => cs₃ r (pinned_pres r hr).1 (pinned_pres r hr).2) sp₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr inv₃.sp ho (by rw [x0₃, inv₂.r4])
    (by rw [x1₃, inv₂.r5, r1_ofNat]) (by rw [x2₃, inv₂.r8]) ?_ x12₃ (by rw [lr₃, inv₂.r8]), by rw [mem₃, mem₂]⟩
  rw [x3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.r9 h0

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m)
    (hB : B s₀ ≠ 0) : WP isa encCall s (Fin true s₀) := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  obtain aT := hp.scrA (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call true h.pre) fun s₄ c => ?_
  obtain sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  obtain tS : Region.Sub ⟨State.addr (S s₀ + BitVec.ofNat 32 tO), 16⟩ (scrR s₀) := by
    rw [aT]; exact sub_trans t_sub s_sub
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_using [hb])
  · have o := c.out
    rw [aT, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) (by rw [aL]; exact hp.hd_l)
      tS h.inv.sp c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tS h.inv.sp c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .r2 = Lv s₀ → (∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block lastAddr) s Q := by
  obtain ⟨s', run', x2', g', sp', mem', rd', wr'⟩ := lastAddr_ok s
  exact WP.of_runBlock ⟨s', run', hq s' (by rw [x2']; exact last_of hp hi.r9 h0) g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_r2 {s s' : State} (hg : ∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) : ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => hg r (by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (lastAddr_wp hp h.all.inv h.r0 fun s₁ x2₁ g₁ sp₁ mem₁ rd₁ wr₁ => ?_))
  obtain h₁ := AllPost.keep hp h.all (keep_r2 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.r0])
    (by rw [g₁ _ (by decide), h.r1]) x2₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (Da s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))) :
    (unitArm enc).post s₀ s' := by
  intro key hk
  obtain hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (State.addr (I s₀)) 16) hk
  obtain hl : 16 ≤ (bytesAt s₀.mem (Da s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `r0`, the bytes after
them in `r1`, and Z set if there are none. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .r0 = BitVec.ofNat 32 (16 * M s₀) → s'.gpr .r1 = BitVec.ofNat 32 (B s₀) →
      s'.z = decide (B s₀ = 0) → (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', x0', x1', z', g', sp', mem', rd', wr'⟩ := split_ok s
  rw [h.r7] at x0' x1' z'
  exact WP.of_runBlock ⟨s', run', hq s' x0' x1' z' g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_r0r1 {s s' : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x12₂, lr₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  obtain h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.sp (N := M s₀)
    (by rw [len_eq s₀]; omega_using []) (by rw [x0₂, h.inv.r4]) (by rw [x1₂, h.inv.r5, r1_ofNat])
    (by rw [x2₂, h.inv.r8]) (by rw [x3₂, h.inv.r9]) (by rw [x12₂, h.inv.r7]) (by rw [lr₂, h.inv.r8])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ x0₄ x1₄ z₄ g₄ sp₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (keep_r0r1 g₄) sp₄ mem₄ rd₄ wr₄, x0₄, x1₄, z₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.z = decide (B s₀ = 0)) : isa.eval .eq s = some (decide (B s₀ = 0)) := by
  show VG.Arm.eval .eq s = _; rw [Proof.MdStream.Arm.eval_eq, h]

theorem encrypt_wp :
    WP isa Impl.AesXts.ArmUnit.encrypt s₀ fun s' => abiPreserved s₀ s' ∧ (unitArm true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.z)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.Arm.Unit
