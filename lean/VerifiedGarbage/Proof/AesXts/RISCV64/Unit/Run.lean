module

public import VerifiedGarbage.Impl.AesXts.RISCV64Unit
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Call
public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Pre
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Steps
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# XTS-AES of data units on RISC-V: the tweak, and what every piece keeps

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Run.lean`). `Inv`: between the
calls the code keeps its arguments in `s1`, `s2`, `s4`, `s5` and `s6`, its
caller's other callee-saved registers, the saved registers and its return
address in their slots at `sv`, the stack pointer, and changes memory only in
the data and the scratch buffer (`Inv.step`, for any code whose frame is in
the data, the tweaks or the working space). `tweak_wp`: the prologue and the
call enciphering the tweak value leave `T = AES-enc(Key2, i)` in the tweak
(`TwPost`). `fin_wp`: the epilogue restores the registers and the return
address.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.RISCV64 (modeRISCV64)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

/-- The slots of the return address and the registers, from `sv`. -/
abbrev saveL : List (Reg × Nat) := saved

/-- What the slots hold: the registers on entry (`t0` holds `sv`). -/
abbrev saveG : Reg → BitVec 64 := (s₀.write .t0 (sv s₀)).gpr

end

theorem save_eq : save = savePtr .a6 ++ Spill.saveCode .t0 saveL := rfl

theorem restore_eq : restore = savePtr .s6 ++ Spill.restoreCode .t0 saveL := rfl

theorem copyI_eq : copyI = Impl.AesCbc.RISCV64.copy .s6 .a3 := rfl

theorem tp_eq (s₀ : State) : Tp s₀ = S s₀ := by simp [Tp, tO]

/-- `t0 :=` the register `n`'s value plus 32, rounded up. -/
theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 32 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 32)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 39 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [align_off_eq _ (off := 32) (by decide) (by decide)]

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6]

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a2
  s4 : s.gpr .s4 = D s₀
  s5 : s.gpr .s5 = s₀.gpr .a5
  s6 : s.gpr .s6 = S s₀
  rest : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (sv s₀) (saveG s₀) saveL s.mem

theorem saved_bound : ∀ p ∈ saveL, p.2 + 8 ≤ 56 := by decide

theorem a2_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .a2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega)

/-- A saved register's slot, within the scratch buffer. -/
theorem slot_contains (s₀ : State) (d : Nat) (h : d + 8 ≤ 56) :
    (scrR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := pad_lt (S s₀ + BitVec.ofNat 64 32)
  rw [align_add]; exact Offset.contains_base _ (by omega) (by omega)

/-- The slots, within the slot region. -/
theorem slots_sub (s₀ : State) : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 0, 56⟩ (slotR s₀) := by
  have := pad_lt (S s₀ + BitVec.ofNat 64 32)
  rw [align_add]; exact Offset.sub _ (by omega) (by omega)

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem ne_s3 {r : Reg} (hv : r ∉ vars) : r ≠ .s3 := fun e => hv (by simp [e])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the callee-saved registers (but `s3`) and
writes only within `rs`, each in the data, the tweaks or the working space. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, ∃ r' ∈ Wr s₀, Region.Sub r r')
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  s1 := by rw [hg _ (by decide) (by decide), h.s1]
  s2 := by rw [hg _ (by decide) (by decide), h.s2]
  s4 := by rw [hg _ (by decide) (by decide), h.s4]
  s5 := by rw [hg _ (by decide) (by decide), h.s5]
  s6 := by rw [hg _ (by decide) (by decide), h.s6]
  rest r hr hv := by rw [hg r hr (ne_s3 hv), h.rest r hr hv]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    obtain ⟨r', hr', hs⟩ := hrs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, hs⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs tz_sub⟩
    · exact ⟨scrR s₀, by simp, sub_trans hs wk_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (sv_slot p.2 (saved_bound p hp'))

/-- `Inv` across code that keeps the registers it pins and memory. -/
theorem Inv.regs {s s' : State} (h : Inv s₀ s) (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' :=
  Inv.step hp h (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk' T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ (tzR s₀))
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ (tzR s₀))
    (hc : XPost enc s Wk' T Dd (Wk s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨Wk s₀, 2176⟩]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨tzR s₀, by simp, hT⟩
      · rcases hD with hD | hD
        · exact ⟨dataR s₀, by simp, hD⟩
        · exact ⟨tzR s₀, by simp, hD⟩
      · exact ⟨wkR s₀, by simp, fun _ h => h⟩)
    hc.frame (fun r hr _ => hc.saved r hr) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (Wk s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  rw [pro, save_eq]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .a6) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine Spill.save_ok (b := .t0) (l := saveL) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ _ this)
  generalize hs₂ : ({ (s₀.write .t0 (sv s₀)) with
    mem := Spill.saveMem (s₀.write .t0 (sv s₀)).mem ((s₀.write .t0 (sv s₀)).gpr .t0)
      (s₀.write .t0 (sv s₀)).gpr saveL } : State) = s₂
  have gpr₂ (r : Reg) (hr : r ≠ .t0) : s₂.gpr r = s₀.gpr r := by
    rw [← hs₂]; exact RegUpd.gpr_write_of_ne _ _ hr
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]; rfl
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]; rfl
  have sp₂ : s₂.sp = s₀.sp := by rw [← hs₂]; rfl
  have mem₂ : s₂.mem = Spill.saveMem s₀.mem (sv s₀) (saveG s₀) saveL := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [t₀]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (setup_wp s₂) fun s₃ ⟨s1₃, s2₃, s4₃, s5₃, s6₃, g₃, mem₃', rd₃', wr₃', sp₃'⟩ => ?_
  rw [gpr₂ _ (by decide)] at s1₃ s2₃ s4₃ s5₃ s6₃
  have k₃ : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂ r h₀]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  have wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  have rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  have tS : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  rw [copyI_eq]
  refine AesCbc.RISCV64.copy_wp (P := Tp s₀) (Q := I s₀) (by decide) (by decide)
    (by rw [tp_eq, s6₃]) (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    ⟨iR s₀, by rw [rdwr₃]; simp, fun _ h => h⟩ ⟨scrR s₀, by rw [wr₃'']; simp, tS⟩
    (hp.i_scr.symm.sub_left tS) fun s₄ g₄ b₄ f₄ rd₄ wr₄ sp₄ => ?_
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  refine WP.mono (zeroZ_wp s₄ (Z := Zp s₀) (by rw [g₄ _ (by decide), s6₃]) fun i hi => by
      rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO]; omega)))
    fun s₅ ⟨g₅, z₅, f₅, rd₅, wr₅, sp₅⟩ => ?_
  refine WP.mono (tArgs_wp s₅) fun s₆ ⟨a0₆, a1₆, a2₆, a3₆, a4₆, a5₆, cs₆, mem₆, rd₆, wr₆, sp₆⟩ => ?_
  -- The registers.
  have k₅ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₅.gpr r = s₃.gpr r := fun r h₁ h₃ => by rw [g₅ r h₁, g₄ r h₃]
  have s6₅ : s₅.gpr .s6 = S s₀ := by rw [k₅ _ (by decide) (by decide), s6₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (pres_ne hr (by decide)) (pres_ne hr (by decide))]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  -- The memory.
  have f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by
    rw [mem₂]
    refine (Spill.saveMem_frame (lo := 0) (n := 56) (fun p hp' => ⟨Nat.zero_le _, by
      have := saved_bound p hp'; omega⟩) (by decide) s₀.mem (sv s₀) (saveG s₀)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, sub_trans (slots_sub s₀) slot_scr⟩
  have m₃ : s₃.mem = s₂.mem := mem₃'
  have frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₂.trans ((by rw [← m₃]; exact f₄ : Frame _ s₂.mem s₄.mem).sub (fun r hr => ?_) |>.trans
      (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, tS⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans z_sub tz_sub⟩
  have sv₂ : Spill.Saved (sv s₀) (saveG s₀) saveL s₂.mem := by
    rw [mem₂]; exact Spill.saveMem_saved (by decide) _ _ _
  have sdisj : ∀ (r : Region), Region.Sub r (tzR s₀) → ∀ p ∈ saveL, ∀ r' ∈ [r],
      Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj ⟨tzR s₀, by simp, hr⟩).sub_left (sv_slot p.2 (saved_bound p hp'))
  have sv₆ : Spill.Saved (sv s₀) (saveG s₀) saveL s₆.mem := by
    rw [mem₆]
    exact ((by rw [m₃]; exact sv₂ : Spill.Saved _ _ _ s₃.mem).frame f₄ (sdisj _ t_sub)).frame f₅
      (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by decide), s1₃], by rw [cs _ (by decide), s2₃], by rw [cs _ (by decide), s4₃],
    by rw [cs _ (by decide), s5₃], by rw [cs _ (by decide), s6₃], fun r hr hv => ?_,
    by rw [sp₆, sp₅, sp₄, sp₃', sp₂], rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := hv
    rw [cs r hr]
    exact k₃ r (pres_ne hr (by decide)) h1 h2 h4 h5 h6
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [a2₆, s6₅]) (by rw [a3₆, s6₅]) a4₆ (by rw [a5₆, s6₅])
    · rw [a0₆, k₅ _ (by decide) (by decide),
        k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [a1₆, k₅ _ (by decide) (by decide), s2₃, a2_ofNat]
  · rw [mem₆, Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), b₄, m₃,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, z₅]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s'

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa} (ok : XtsOk true c) (nf : c.noFrames = true) {s₂ : State}
    (h₂ : ProPost s₀ s₂) : WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega)
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub tz_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub tz_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) : WP isa tweak s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp ok nf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa} (ok : XtsOk enc c)
    (nf : c.noFrames = true) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (Wk s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr.sub_left dS) (by have := hp.data_wrap; omega)
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub tz_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.regs hp h.inv (fun r hr _ => hg r hr) hsp hm hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

/-- The callee-saved registers and the return address restored. -/
def Restored (s₀ s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => Restored s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₃ e => ?_
  subst e
  rw [h.s6]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saveL) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) h.saved) fun s₄ r₄ => ?_
  · show InRegions (s.rd ++ s.wr) _ 8
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ _ (saved_bound p hp'))
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨⟨fun r hr => ?_, ?_⟩, r₄.mem, r₄.rd, r₄.wr, r₄.sp⟩
  · have h0 : r ≠ .t0 := pres_ne hr (by decide)
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h.rest r hr hv, g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk' T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (c : XPost enc s Wk' T Dd (Wk s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub) hn

end

end VG.Proof.AesXts.RISCV64.Unit
