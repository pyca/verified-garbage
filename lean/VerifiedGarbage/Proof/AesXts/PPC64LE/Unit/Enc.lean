module

import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Pre
import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Steps
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.Mem
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Impl.AesXts.PPC64LEUnit
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Call
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Unit.Contract
public import VerifiedGarbage.Spec.Xts
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesXts.PPC64LE.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on PPC64LE: the tweak, and what every piece keeps

As on AArch64 (`Proof/AesXts/AArch64/Unit/Run.lean`). `Inv`: between the
calls the code keeps its arguments in `r14`, `r15`, `r17`, `r18` and `r19`,
its caller's other nonvolatile registers, the saved registers and its return
address in their slots, and changes memory only in the data and the scratch
buffer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers and the return address. No code changes the stack
pointer (`wp_sp`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE (modePPC64LE)
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

/-- The slots: the return address (through `r0`) and the registers. -/
abbrev saveL : List (Reg × Nat) := (.r0, lrOff) :: saved

/-- What the slots hold: the registers on entry, and the return address. -/
abbrev saveG : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr

end

theorem save_eq : save = .mflr .r0 :: Spill.saveCode .r9 saveL := rfl

theorem restore_eq : restore = Spill.restoreCode .r19 saveL ++ ([.mtlr .r0] : List Instr) := rfl

/-- The registers the code saves. -/
abbrev vars : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19]

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r5
  r17 : s.gpr .r17 = D s₀
  r18 : s.gpr .r18 = s₀.gpr .r8
  r19 : s.gpr .r19 = S s₀
  rest : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (S s₀) (saveG s₀) saveL s.mem

theorem saved_bound : ∀ p ∈ saveL, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2264 := by decide

theorem r4_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .r5 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem preserved_ne16 {r : Reg} (hv : r ∉ vars) : r ≠ .r16 := fun e => hv (by simp [e])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the nonvolatile registers (but `r16`) and
writes only within `rs`, each in the data or the first 2208 bytes of the
scratch buffer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩)
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  r14 := by rw [hg _ (by decide) (by decide), h.r14]
  r15 := by rw [hg _ (by decide) (by decide), h.r15]
  r17 := by rw [hg _ (by decide) (by decide), h.r17]
  r18 := by rw [hg _ (by decide) (by decide), h.r18]
  r19 := by rw [hg _ (by decide) (by decide), h.r19]
  rest r hr hv := by rw [hg r hr (preserved_ne16 hv), h.rest r hr hv]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

/-- `Inv` across code that keeps the registers it pins and memory. -/
theorem Inv.regs {s s' : State} (h : Inv s₀ s) (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' :=
  Inv.step hp h (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr hT
      · exact hD
      · exact .inr (Region.sub_prefix (by decide)))
    hc.frame (fun r hr _ => hc.saved r hr) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  refine WP.mono (wp_sp (Q := fun s => s.sp = s₀.sp → ProPost s₀ s) ?_) fun s ⟨h, hsp⟩ => h hsp
  rw [pro, save_eq]
  simp only [List.append_assoc, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r9) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  rw [WP.block_append_iff]
  generalize hs₂ : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r9) (s₀.write .r0 s₀.lr).gpr
      saveL) } : State) = s₂
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, hr]
  have gpr₂ (r : Reg) (hr : r ≠ .r0) : s₂.gpr r = s₀.gpr r := by rw [← hs₂]; exact g₀ r hr
  obtain rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]; rfl
  obtain wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]; rfl
  obtain mem₂ : s₂.mem = Spill.saveMem s₀.mem (S s₀) (saveG s₀) saveL := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [g₀ .r9 (by decide)]; rfl
  refine WP.mono (setup_wp s₂) fun s₃ ⟨r14₃, r15₃, r17₃, r18₃, r19₃, g₃, mem₃', rd₃', wr₃'⟩ => ?_
  rw [gpr₂ _ (by decide)] at r14₃ r15₃ r17₃ r18₃ r19₃
  obtain mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) (saveG s₀) saveL := by rw [mem₃', mem₂]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  obtain k₃ : ∀ r, r ≠ .r0 → r ≠ .r14 → r ≠ .r15 → r ≠ .r17 → r ≠ .r18 → r ≠ .r19 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂ r h₀]
  obtain rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  obtain wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  obtain cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  obtain r6₃ : s₃.gpr .r6 = I s₀ := k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine AesCbc.PPC64LE.copy_wp (dst := .r19) (src := .r6) (d := tO) (e := 0) (P := Tp s₀) (Q := I s₀)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r19₃]) (by rw [r19₃, ← Offset.add_add]) (by rw [r6₃]; simp) (by rw [r6₃])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
  rw [WP.block_append_iff]
  obtain wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  refine WP.mono (zeroZ_wp s₄ (Z := Zp s₀) (by rw [g₄ _ (by decide), r19₃])
    (by rw [g₄ _ (by decide), r19₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO]))))
    fun s₅ ⟨g₅, mem₅, rd₅, wr₅⟩ => ?_
  refine WP.mono (tArgs_wp s₅) fun s₆ ⟨r3₆, r4₆, r5₆, r6₆, r7₆, r8₆, cs₆, mem₆, rd₆, wr₆⟩ hsp => ?_
  -- The registers.
  obtain k₅ : ∀ r, r ≠ .r9 → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  obtain r19₅ : s₅.gpr .r19 = S s₀ := by rw [k₅ _ (by decide), r19₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (preserved_ne r hr).2.2.2.2.2.2.2.1]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  -- The memory.
  obtain f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base (n := 2264) (fun p hp' => (saved_bound p hp').2) (by decide) s₀.mem (S s₀)
      _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  obtain f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  obtain f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  obtain frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  obtain sv₃ : Spill.Saved (S s₀) (saveG s₀) saveL s₃.mem := by
    rw [mem₃]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saveL, ∀ r' ∈ [r],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  obtain sv₆ : Spill.Saved (S s₀) (saveG s₀) saveL s₆.mem := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by decide), r14₃], by rw [cs _ (by decide), r15₃], by rw [cs _ (by decide), r17₃],
    by rw [cs _ (by decide), r18₃], by rw [cs _ (by decide), r19₃], fun r hr hv => ?_, hsp, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨h14, h15, -, h17, h18, h19⟩ := hv
    rw [cs r hr]
    exact k₃ r (preserved_ne r hr).1 h14 h15 h17 h18 h19
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [r5₆, r19₅]) (by rw [r6₆, r19₅]) r7₆ (by rw [r8₆, r19₅])
    · rw [r3₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [r4₆, k₅ _ (by decide), r15₃, r4_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modePPC64LE (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode enc)).post s s'

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa} (ok : XtsOk true c) (nf : c.noFrames = true) {s₂ : State}
    (h₂ : ProPost s₀ s₂) : WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) : WP isa tweak s₀ (TwPost s₀) :=
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
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  obtain dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.data_scr.sub_left dS) (by have := hp.data_wrap; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩

/-- `TwPost` across code that keeps the nonvolatile registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.regs hp h.inv (fun r hr _ => hg r hr) hsp hm hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

/-- The nonvolatile registers and the return address restored. -/
def Restored (s₀ s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => Restored s₀ s' ∧ s'.mem = s.mem := by
  obtain rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h.r19 (by decide) (by decide)
    (fun p hp' => ?_) h.saved fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  refine WP.cons exec_mtlr (wp_nil ⟨⟨fun r hr => ?_, ?_⟩, r₃.mem⟩)
  · show s₃.gpr r = _
    obtain h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne r hr).1
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h.rest r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub) hn

end

end VG.Proof.AesXts.PPC64LE.Unit

end

end


/-!
# XTS-AES of data units on PPC64LE: encryption

As on AArch64 (`Proof/AesXts/AArch64/Unit/Enc.lean`). `encrypt_wp`: the
tweak, the call on the whole blocks, and for a partial block the swap and
the call on the last whole block, then the epilogue. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE.Unit

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LEUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.regs hp h.inv hg hsp hm hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  r10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (B s₀)

/-- `r17 + r10 − 16` is the last whole block. -/
theorem last_of {s : State} (h17 : s.gpr .r17 = D s₀) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .r17 + s.gpr .r10 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h17, h10, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (B s₀))
    (h12 : s.gpr .r12 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (wp_sp (swap_wp s (Nat.pos_of_ne_zero hB) hb h12 h11 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi']) (by omega_using [hb, hi']))))))
    fun s₂ ⟨⟨mem₂, g₂, rd₂, wr₂⟩, sp₂⟩ => ?_)
  refine WP.mono (wp_sp (argsL_wp' s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)))
    fun s₃ ⟨⟨r3₃, r4₃, r5₃, r6₃, r7₃, r8₃, cs₃, mem₃, rd₃, wr₃⟩, sp₃⟩ => ?_
  have k₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h8, h9, -, h11, h12⟩ := preserved_ne r hr
    exact g₂ r h8 h9 h11 h12
  obtain inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) (fun r hr _ => k₂ r hr) sp₂ rd₂ wr₂
  obtain inv₃ : Inv s₀ s₃ := Inv.regs hp inv₂ (fun r hr _ => cs₃ r hr) sp₃ mem₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [r3₃, inv₂.r14])
    (by rw [r4₃, inv₂.r15, r4_ofNat]) (by rw [r5₃, inv₂.r19]) ?_ r7₃ (by rw [r8₃, inv₂.r19]),
    by rw [mem₃, mem₂]⟩
  rw [r6₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.r17 h10

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa encCall s (Fin true s₀) := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  obtain sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l
      (sub_trans t_sub s_sub) c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * M s₀)) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .r12 = L s₀ ∧ (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (wp_sp (lastAddr_wp' s)) fun _ ⟨⟨r12, g, mem, rd, wr⟩, sp⟩ =>
    ⟨by rw [r12]; exact last_of hp hi.r17 h10, g, sp, mem, rd, wr⟩

omit hp in
theorem keep_r12 {s s' : State} (hg : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (preserved_ne r hr).2.2.2.2.2.2.2.2.2.2

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (WP.mono (lastAddr_wp hp h.all.inv h.r10) fun s₁ ⟨r12₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_))
  obtain h₁ := AllPost.keep hp h.all (keep_r12 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.r10])
    (by rw [g₁ _ (by decide), h.r11]) r12₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitPPC64LE enc).post s₀ s' := by
  intro key hk
  obtain hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  obtain hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `r10`, and the bytes
after them in `r11`. -/
theorem split_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block split) s fun s' => s'.gpr .r10 = BitVec.ofNat 64 (16 * M s₀) ∧
      s'.gpr .r11 = BitVec.ofNat 64 (B s₀) ∧ (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (wp_sp (split_wp' s)) fun _ ⟨⟨r10, r11, g, mem, rd, wr⟩, sp⟩ =>
    ⟨by rw [r10, h.r18], by rw [r11, h.r18], g, sp, mem, rd, wr⟩

omit hp in
theorem keep_r10r11 {s s' : State} (hg : ∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .r16 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (preserved_ne r hr).2.2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.2.1

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) :=
  WP.mono (wp_sp (argsAll_wp' s)) fun s₂ ⟨⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩, sp₂⟩ =>
    have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
    ⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
      (by rw [len_eq s₀]; omega_using []) (by rw [r3₂, h.inv.r14]) (by rw [r4₂, h.inv.r15, r4_ofNat])
      (by rw [r5₂, h.inv.r19]) (by rw [r6₂, h.inv.r17]) (by rw [r7₂, h.inv.r18]) (by rw [r8₂, h.inv.r19])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  WP.mono (split_wp h.inv) fun _ ⟨r10, r11, g, sp, mem, rd, wr⟩ =>
    ⟨AllPost.keep hp h (keep_r10r11 g) sp mem rd wr, r10, r11⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .r11 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .d .r11) s = some (decide (B s₀ = 0)) :=
  eval_zero_ofNat s .r11 (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega_using [this]) h

theorem encrypt_wp (ok : XtsOk true Impl.AesXts.PPC64LE.encrypt)
    (nf : Impl.AesXts.PPC64LE.encrypt.noFrames = true) :
    WP isa Impl.AesXts.PPC64LEUnit.encrypt s₀ fun s' => Restored s₀ s' ∧ (unitPPC64LE true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.r11)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.PPC64LE.Unit
