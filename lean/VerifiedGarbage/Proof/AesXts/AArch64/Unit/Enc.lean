module

public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Call
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Contract
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Pre
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Steps
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesXts.AArch64.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on AArch64: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `x19`, `x20`,
`x22`, `x23` and `x24`, its caller's callee-saved registers and its return
address in their slots, and changes memory only in the data and the scratch
buffer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
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

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x2
  x22 : s.gpr .x22 = s₀.gpr .x5
  x23 : s.gpr .x23 = D s₀
  x24 : s.gpr .x24 = S s₀
  rest : ∀ r ∈ ([.x25, .x26, .x27, .x28] : List Reg), s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (S s₀) s₀.gpr saved s.mem

theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2264 := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

theorem rest_pinned : ∀ r ∈ ([.x25, .x26, .x27, .x28] : List Reg), r ∈ pinned := by decide

theorem pinned_pres : ∀ r ∈ pinned, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem x1_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .x2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega_using [h])

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data or the first 2208 bytes of the scratch buffer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩)
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  x19 := by rw [hg _ (by simp), h.x19]
  x20 := by rw [hg _ (by simp), h.x20]
  x22 := by rw [hg _ (by simp), h.x22]
  x23 := by rw [hg _ (by simp), h.x23]
  x24 := by rw [hg _ (by simp), h.x24]
  rest r hr := by
    rw [hg r (rest_pinned r hr), h.rest r hr]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

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
    hc.frame (fun r hr => hc.saved r (pinned_pres r hr).1 (pinned_pres r hr).2) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, save_eq]
  refine Spill.save_ok (l := saved) (b := .x6) (by decide) (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  rw [WP.block_append_iff]
  generalize hs₂ : ({ s₀ with mem := Spill.saveMem s₀.mem (s₀.gpr .x6) s₀.gpr saved } : State) = s₂
  have gpr₂ : s₂.gpr = s₀.gpr := by rw [← hs₂]
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂]
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂]
  have sp₂ : s₂.sp = s₀.sp := by rw [← hs₂]
  have mem₂ : s₂.mem = Spill.saveMem s₀.mem (S s₀) s₀.gpr saved := by rw [← hs₂]
  obtain ⟨s₃, run₃, x24₃, x19₃, x20₃, x23₃, x22₃, g₃, sp₃', mem₃', rd₃', wr₃'⟩ := setup_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [gpr₂] at x24₃ x19₃ x20₃ x23₃ x22₃
  have mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) s₀.gpr saved := by rw [mem₃', mem₂]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂]
  have sp₃ : s₃.sp = s₀.sp := by rw [sp₃', sp₂]
  have k₃ : ∀ r, r ≠ .x24 → r ≠ .x19 → r ≠ .x20 → r ≠ .x23 → r ≠ .x22 → s₃.gpr r = s₀.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂]
  have rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  have wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  have cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  rw [WP.block_append_iff]
  have x3₃ : s₃.gpr .x3 = I s₀ := k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ := AesCbc.AArch64.copy_ok s₃ (dst := .x24) (src := .x3) (d := tO)
    (e := 0) (P := Tp s₀) (Q := I s₀) (by rw [x24₃]) (by rw [x24₃, ← Offset.add_add])
    (by rw [x3₃]; simp) (by rw [x3₃])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  obtain ⟨s₅, run₅, g₅, sp₅, mem₅, rd₅, wr₅⟩ := zeroZ_ok s₄ (Z := Zp s₀)
    (by rw [g₄ _ (by decide), x24₃]) (by rw [g₄ _ (by decide), x24₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, x0₆, x1₆, x2₆, x3₆, x4₆, x5₆, cs₆, sp₆', mem₆, rd₆, wr₆⟩ := tArgs_ok s₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- The registers.
  have k₅ : ∀ r, r ≠ .x9 → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  have x24₅ : s₅.gpr .x24 = S s₀ := by rw [k₅ _ (by decide), x24₃]
  have cs (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (preserved_ne r hr).2.2.2.2.2.2]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have sp₆ : s₆.sp = s₀.sp := by rw [sp₆', sp₅, sp₄, sp₃]
  -- The memory.
  have f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base (n := 2264) (fun p hp' => (saved_bound p hp').2) (by decide) s₀.mem (S s₀)
      _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  have f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  have f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  have frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  have sv₃ : Spill.Saved (S s₀) s₀.gpr saved s₃.mem := by
    rw [mem₃]; exact Spill.saveMem_saved (by decide) _ _ _
  have sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saved, ∀ r' ∈ [r],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  have sv₆ : Spill.Saved (S s₀) s₀.gpr saved s₆.mem := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [preserved]), x19₃], by rw [cs _ (by simp [preserved]), x20₃],
    by rw [cs _ (by simp [preserved]), x22₃], by rw [cs _ (by simp [preserved]), x23₃],
    by rw [cs _ (by simp [preserved]), x24₃], fun r hr => by
      have hr' : r ∈ preserved := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [cs r hr']
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), sp₆, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₆' wr₆' ?_ ?_ (by rw [x2₆, x24₅]) (by rw [x3₆, x24₅]) x4₆ (by rw [x5₆, x24₅])
    · rw [x0₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x1₆, k₅ _ (by decide), x20₃, x1_ofNat]
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
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s')
    (nf : c.noFrames = true) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nf h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
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

theorem tweak_wp {f : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s')
    (nf : f.code.noFrames = true) :
    WP isa (tweak f) s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp ok nf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nf hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
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

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (pinned_pres r hr).1) hsp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp (B := S s₀) h.x24 (by decide) (by decide) (fun p hp' => ?_) h.saved)
    fun s' r => ⟨⟨fun x hx => ?_, by rw [r.sp, h.sp]⟩, r.mem⟩
  · have := saved_bound p hp'
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega_using [this]))
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact r.gpr_of (.inl (by decide))
      | exact r.gpr_of (.inr (h.rest _ (by simp)))

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

end VG.Proof.AesXts.AArch64.Unit

end

end


/-!
# XTS-AES of data units on AArch64: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue,
for any implementation `f` of the whole-block encryption. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc.AArch64 (modeAArch64)
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

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s'

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

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  x9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀)

/-- `x23 + x9 − 16` is the last whole block. -/
theorem last_of {s : State} (h23 : s.gpr .x23 = D s₀) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .x23 + s.gpr .x9 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h23, h9, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) (h10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀))
    (h11 : s.gpr .x11 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (swap_ok s (Nat.pos_of_ne_zero hB) hb h11 h10 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi']) (by omega_using [hb, hi'])))))
    fun s₂ ⟨mem₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x4₃, x5₃, cs₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    argsL_ok s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₂ _ (by decide) (by decide) (by decide) (by decide)
  have inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ sp₂ rd₂ wr₂
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => cs₃ r (pinned_pres r hr).1) sp₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [x0₃, inv₂.x19])
    (by rw [x1₃, inv₂.x20, x1_ofNat]) (by rw [x2₃, inv₂.x24]) ?_ x4₃ (by rw [x5₃, inv₂.x24]), by rw [mem₃, mem₂]⟩
  rw [x3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.x23 h9

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa (.call f.name f.code) s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
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
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x11 = L s₀ → (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block lastAddr) s Q := by
  obtain ⟨s', run', x11', g', sp', mem', rd', wr'⟩ := lastAddr_ok s
  exact WP.of_runBlock ⟨s', run', hq s' (by rw [x11']; exact last_of hp hi.x23 h9) g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x11 {s s' : State} (hg : ∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) : ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => hg r (by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (lastAddr_wp hp h.all.inv h.x9 fun s₁ x11₁ g₁ sp₁ mem₁ rd₁ wr₁ => ?_))
  have h₁ := AllPost.keep hp h.all (keep_x11 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.x9])
    (by rw [g₁ _ (by decide), h.x10]) x11₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (encSteal f) s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitAArch64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `x9`, and the bytes
after them in `x10`. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x9 = BitVec.ofNat 64 (16 * M s₀) → s'.gpr .x10 = BitVec.ofNat 64 (B s₀) →
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', x9', x10', g', sp', mem', rd', wr'⟩ := split_ok s
  rw [h.x22] at x9' x10'
  exact WP.of_runBlock ⟨s', run', hq s' x9' x10' g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x9x10 {s s' : State} (hg : ∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, x5₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
    (by rw [len_eq s₀]; omega_using []) (by rw [x0₂, h.inv.x19]) (by rw [x1₂, h.inv.x20, x1_ofNat])
    (by rw [x2₂, h.inv.x24]) (by rw [x3₂, h.inv.x23]) (by rw [x4₂, h.inv.x22]) (by rw [x5₂, h.inv.x24])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ x9₄ x10₄ g₄ sp₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (keep_x9x10 g₄) sp₄ mem₄ rd₄ wr₄, x9₄, x10₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .x10 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .x .x10) s = some (decide (B s₀ = 0)) :=
  eval_z h (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega_using [this])

theorem encrypt_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true) :
    WP isa (Impl.AesXts.AArch64Unit.encrypt f) s₀ fun s' => GprAbi s₀ s' ∧ (unitAArch64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.x10)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.AArch64.Unit
