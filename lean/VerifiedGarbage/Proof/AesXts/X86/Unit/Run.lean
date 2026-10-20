module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Steps
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacAes.X86.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# XTS-AES of data units on x86: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps `esp` and the permissions, its
caller's callee-saved registers in their slots, and changes memory only in
the data, the scratch buffer and the 52 bytes below `esp` (`Inv.step`, for
any code whose frame is in those); the arguments stay readable on the stack
(`Inv.args`). `tweak_wp`: the prologue and the call enciphering the tweak
value leave `T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the
epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86 (modeX86)
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_addi)
open VG.Spec.Aes (bytesAt)

/-- A whole-block function, verified. -/
structure XFn (enc : Bool) (f : Impl.Aes.X86.Blocks) : Prop where
  ok : XtsOk enc f.code
  ct : ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub f.code
  nosp : NoSp f.code
  stack : stackUse f.code ≤ 24

section
variable (s₀ : State)

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1))) (bytesAt s₀.mem ((I s₀).setWidth 64) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher :=
  ciphOf enc (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))

/-- The memory after the saves. -/
def sMem : Mem := Spill.saveMem s₀.mem (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saved_fits : Spill.Fits 2224 saved := by decide
theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 4 ≤ 2224 := by decide
theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide
theorem save_eq : save = Spill.saveCode .eax saved := rfl
theorem restore_eq : restore = .mov .eax (argOp 6) :: (Spill.restoreCode .eax saved ++ []) := rfl

section
variable {s₀ : State} (hp : UPre s₀)
include hp

omit hp in
theorem slot_in {p : Reg × Nat} (h : p ∈ saved) :
    (⟨Sa s₀ + BitVec.ofNat 64 2208, 16⟩ : Region).Contains (Sa s₀ + BitVec.ofNat 64 p.2) 4 :=
  Offset.contains _ (saved_bound p h).1 (by have := saved_bound p h; omega) (by decide)

theorem UPre.cvS {d n : Nat} (h : d + n ≤ 2432) : Covers [⟨Sa s₀ + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem Inv.args {s : State} (h : Inv s₀ s) : ArgsOk s₀ s := hp.argsOk h.esp h.rd h.wr h.frame

/-- `Inv` across code that keeps `esp` and writes only within `rs`, each in
the data, the first 2208 bytes of the scratch buffer or the stack below
`esp`. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨Sa s₀, 2208⟩ ∨ Region.Sub r (stkR s₀))
    (hf : Frame rs s.mem s'.mem) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv s₀ s' where
  esp := by rw [hesp, h.esp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stkR s₀, by simp, h⟩)
  saved := h.saved.of_frame hf (fun _ hp' => slot_in hp') fun r hr => hp.slots_disj (hrs r hr)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : BitVec 32} {N Rr : Nat}
    (hT : Region.Sub ⟨T.setWidth 64, 16⟩ ⟨Sa s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd.setWidth 64, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd.setWidth 64, 16 * N⟩ ⟨Sa s₀, 2208⟩)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h
    (rs := [⟨T.setWidth 64, 16⟩, ⟨Dd.setWidth 64, 16 * N⟩, ⟨(S s₀).setWidth 64, 2176⟩, below (s.gpr .esp) 52])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [hp.stk_eq h.esp]; exact fun _ h => h)))
    c.frame (c.saved .esp (by simp [calleeSaved])) c.rd c.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zv s₀) (Tv s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem ((I s₀).setWidth 64) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem sMem_frame : Frame [scrR s₀] s₀.mem (sMem s₀) :=
  Spill.saveMem_frame (List.mem_singleton_self _) _ _ saved s₀.mem fun p hp' =>
    hp.cS _ _ (by have := saved_bound p hp'; omega)

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  have hif : (arg s₀ 3).toNat + 16 ≤ 2 ^ 32 := hp.i_fit
  have hsc' : (S s₀).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, save_eq, List.cons_append,
    List.nil_append]
  refine wp_argA hp.argsOk₀ (i := 6) (by decide) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [e₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [e₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, hp.cS _ _ (by omega)⟩
  have m₂ : s₂.mem = sMem s₀ := by
    rw [u₂.mem, u₁.mem, e₁, sMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by rw [m₂]; exact sMem_frame hp
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have h₂ : ArgsOk s₀ s₂ := hp.argsOk esp₂ rd₂ wr₂ (f₂.mono (by simp))
  rw [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => ?_
  have bp₃ : s₃.gpr .ebp = S s₀ := by rw [u₃.gpr, u₂.gpr, e₁]
  have h₃ := h₂.upd u₃ (by decide)
  rw [copyI, List.cons_append]
  refine wp_argA h₃ (i := 3) (by decide) fun s₄ u₄ => ?_
  have h₄ := h₃.upd u₄ (by decide)
  have bp₄ : s₄.gpr .ebp = S s₀ := by rw [u₄.other _ (by decide), bp₃]
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂]
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine copy_wp (P := Tp s₀) (Q := (I s₀).setWidth 64) (by decide) (by decide) (by rw [u₄.gpr]; simp)
    (by rw [u₄.gpr]; omega) (by rw [bp₄]) (by rw [bp₄]; simp only [tO]; omega)
    (hp.i_scr.symm.sub_left (sub_trans t_sub s_sub))
    (fun d n hd => by
      rw [rd₄, wr₄, hp.rd]; exact ⟨iR s₀, by simp, Offset.contains_base _ hd (by omega)⟩)
    (fun d n hd => by
      rw [wr₄, hp.wr]
      exact ⟨scrR s₀, by simp, by rw [Offset.add_add]; exact hp.cS _ _ (by simp only [tO]; omega)⟩)
    fun s₅ c₅ => ?_
  have bp₅ : s₅.gpr .ebp = S s₀ := by rw [c₅.gpr _ (by decide), bp₄]
  have wr₅ : s₅.wr = s₀.wr := by rw [c₅.wr, wr₄]
  have h₅ : ArgsOk s₀ s₅ := hp.argsOk_frame h₄ (c₅.gpr _ (by decide)) c₅.rd c₅.wr
    (by rw [c₅.mem]; exact copy4_frame _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_right (sub_trans t_sub s_sub)
  rw [zeroZ]
  refine VG.Proof.CmacAes.X86.zero4_ok (b := .ebp) (d := zO) (by decide)
    (by rw [bp₅]; simp only [zO]; omega) (by rw [bp₅, wr₅]; exact hp.cvS (by simp only [zO]; omega))
    fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  rw [bp₅] at m₆
  have h₆ : ArgsOk s₀ s₆ := hp.argsOk_frame h₅ (g₆ _ (by decide)) rd₆ wr₆
    (by rw [m₆]; exact Proof.Cmac.frame_store4 _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_right (sub_trans z_sub s_sub)
  have bp₆ : s₆.gpr .ebp = S s₀ := by rw [g₆ _ (by decide), bp₅]
  simp only [tArgs]
  refine wp_argA h₆ (i := 1) (by decide) fun s₇ u₇ => ?_
  have h₇ := h₆.upd u₇ (by decide)
  refine wp_argA h₇ (i := 2) (by decide) fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => wp_addi fun s₁₂ u₁₂ => ?_
  refine wp_movi fun s₁₃ u₁₃ => WP.block_nil ?_
  have c := ((((((Chg.refl s₆ [.eax, .ecx, .edx, .ebx, .edi]).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉
    (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide) |>.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  have bp : s₁₃.gpr .ebp = S s₀ := by rw [c.gpr _ (by decide), bp₆]
  have esp : s₁₃.gpr .esp = s₀.gpr .esp := by
    rw [c.gpr _ (by decide), g₆ _ (by decide), c₅.gpr _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), esp₂]
  have rd : s₁₃.rd = s₀.rd := by rw [c.rd, rd₆, c₅.rd, rd₄]
  have wr : s₁₃.wr = s₀.wr := by rw [c.wr, wr₆, wr₅]
  have mem : s₁₃.mem = Proof.Cmac.zero4 (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) (Zp s₀) := by
    rw [c.mem, m₆, c₅.mem, m₄, m₂]
  have fT : Frame [⟨Tp s₀, 16⟩] (sMem s₀) (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) := copy4_frame _ _ _
  have fZ : Frame [⟨Zp s₀, 16⟩] (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64))
      (Proof.Cmac.zero4 (copy4 (sMem s₀) (Tp s₀) ((I s₀).setWidth 64)) (Zp s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  have frame : Frame [scrR s₀] s₀.mem s₁₃.mem := by
    rw [mem]
    refine (sMem_frame hp).trans ((fT.sub fun r hr => ?_).trans (fZ.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
  have sv : Spill.Saved (sMem s₀) (Sa s₀ + BitVec.ofNat 64 ·) s₀.gpr saved :=
    Spill.saveMem_saved_ofNat _ _ _ saved_fits (by decide)
  have sdisj : ∀ (r : Region), Region.Sub r ⟨Sa s₀, 2208⟩ → ∀ r' ∈ [r],
      Region.Disjoint ⟨Sa s₀ + BitVec.ofNat 64 2208, 16⟩ r' := fun r hr r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hp.slots_disj (.inr (.inl hr))
  refine ⟨⟨esp, rd, wr, frame.mono (by simp), ?_⟩, ?_, frame, ?_, ?_⟩
  · rw [mem]
    exact (sv.of_frame fT (fun _ h => slot_in h) (sdisj _ t_sub)).of_frame fZ (fun _ h => slot_in h)
      (sdisj _ z_sub)
  · refine xpre_tweak hp rd wr esp ?_ ?_ ?_ ?_ ?_ bp
    · simp (disch := decide) only [u₁₃.other, u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.other, u₇.gpr]
    · simp (disch := decide) only [u₁₃.other, u₁₂.other, u₁₁.other, u₁₀.other, u₉.other, u₈.gpr, r_ofNat]
    · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr,
        u₈.other _ (by decide), u₇.other _ (by decide), bp₆]
    · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), bp₆]
    · exact u₁₃.gpr
  · rw [mem, Proof.Cmac.bytesAt_frame fZ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), copy4_bytes,
      Proof.Cmac.bytesAt_frame (sMem_frame hp) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem, Proof.Cmac.zero4_bytes]; rfl

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stkR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stkR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (xcall f) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true hf.ok hf.nosp hf.stack h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have stk := hp.stk_eq h₂.inv.esp
  have aT := hp.scrW (d := tO) (by decide)
  have aZ := hp.scrW (d := zO) (by decide)
  have eK : bytesAt s₂.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1)) =
      bytesAt s₀.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1)) :=
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
    have := Proof.AesXts.Unit.tweak_of (R := R s₀)
      (w := bytesAt s₂.mem ((K s₀).setWidth 64) (16 * (R s₀ + 1))) o h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) : WP isa (tweak f) s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp hf h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (Da s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem s.mem

theorem blocks_call {enc : Bool} {f : Impl.Aes.X86.Blocks} (hf : XFn enc f) {N : Nat} (hN : 16 * N ≤ Len s₀)
    {s : State} (h : TwPost s₀ s) (hpre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (xcall f) s fun s' => AllPost enc s₀ N s' ∧ s'.gpr .esi = s.gpr .esi := by
  refine WP.mono (xts_call enc hf.ok hf.nosp hf.stack hpre) fun s' x => ⟨?_, x.saved .esi (by simp [calleeSaved])⟩
  have aT := hp.scrW (d := tO) (by decide)
  have stk := hp.stk_eq h.inv.esp
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

/-- `TwPost` across code that keeps `esp` and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hesp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hesp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have hsc : (arg s₀ 6).toNat + 2432 ≤ 2 ^ 32 := hp.scr_fit
  rw [restore_eq]
  refine wp_argA (Inv.args hp h) (i := 6) (by decide) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact h.saved p hp') fun s₂ r₂ => WP.block_nil
      ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, h.rd, h.wr, hp.wr]
    exact ⟨scrR s₀, by simp, hp.cS _ _ (by omega)⟩
  · rw [r₂.mem, u₁.mem]
    have := hp.esp_fit
    have rs : (retR s₀).Disjoint (stkR s₀) := Offset.base_disjoint_below _ (by decide)
    exact h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_data
      · exact hp.ret_scr
      · exact rs) (by decide)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : BitVec 32} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd.setWidth 64, 16 * N⟩)
    (hT : Region.Sub ⟨T.setWidth 64, 16⟩ (scrR s₀)) (hesp : s.gpr .esp = s₀.gpr .esp)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [hp.stk_eq hesp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.X86.Unit
