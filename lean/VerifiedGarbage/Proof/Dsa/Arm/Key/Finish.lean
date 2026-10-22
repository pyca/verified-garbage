module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Saved
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Prepare
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Key.Scan
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# The randomized signer's exit (32-bit ARM)

`finish` zeros `out` unless signing succeeded (`zeroOut_ok`), clears the
nonce, publishes the consumption to `used`, returns the status and restores
the callee-saved registers, `r11` last (`rfinish_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str wp_strb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-- Registers but `r11` and memory where the body may write change. -/
theorem RReady.congrW {s₀ t u : State} {ws : List Reg} {rs : List Region} (h : RReady s₀ t) (R : Rest ws t u)
    (hm : Frame rs t.mem u.mem) (hrs : ∀ r ∈ rs, r ∈ rWrites s₀) (h11 : .r11 ∉ ws := by decide) : RReady s₀ u :=
  ⟨h.rf.of_rest R h11, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr, h.frame.trans (hm.mono hrs)⟩

/-! ## Zeroing the output -/

/-- The output, after `k` of its bytes are zeroed. -/
structure ZeroInv (s₀ t₀ : State) (k : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  r1 : t.gpr .r1 = s₀.gpr .r0 + BitVec.ofNat 32 k
  r2 : t.gpr .r2 = BitVec.ofNat 32 ((s₀.gpr .r1).toNat - k)
  r0 : t.gpr .r0 = 0
  frame : Frame [rOut s₀] t₀.mem t.mem
  zero : ∀ i < k, t.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = 0
  rest : Rest [.r0, .r1, .r2] t₀ t

theorem zeroStep_ok {s₀ t₀ t : State} (A : KeyABI s₀) {k : Nat} (hk : k < (s₀.gpr .r1).toNat)
    (I : ZeroInv s₀ t₀ k t) :
    WP isa (.block [.strb .r0 .r1 0, .dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) t
      fun u => ZeroInv s₀ t₀ (k + 1) u ∧ u.z = decide ((s₀.gpr .r1).toNat - (k + 1) = 0) := by
  have hb := A.outBound
  have hw : InRegions t.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) 1 :=
    ⟨rOut s₀, by rw [I.ready.wr, A.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_strb (by decide) (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega)]) hw fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  have hv : (t.gpr .r0).setWidth 8 = 0 := by rw [I.r0]; rfl
  rw [hv] at m₁
  have R : Rest [.r0, .r1, .r2] t u₃ := (m₁.rest _).trans ((v₂.rest (by decide)).trans (v₃.rest (by decide)))
  have mem₃ : u₃.mem = t.mem.writeW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [rOut s₀] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨I.ready.congrW R fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites]),
    ?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.rest.trans R⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r1, Offset.add_ofNat_add_one]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.r0]
  · rw [mem₃]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · have ho : ofs (State.addr (s₀.gpr .r0)) (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = i := by
        rw [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [show State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k = off (State.addr (s₀.gpr .r0)) k from rfl,
        writeW8_outside _ _ (d := k) _ (by omega) _ (by rw [ho]; omega)]
      exact I.zero i (by omega)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega), ofNat_beq_zero (by omega),
      Nat.sub_sub]

theorem zeroOut_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa zeroOut t fun u => RReady s₀ u ∧ Frame [rOut s₀] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        List.replicate (s₀.gpr .r1).toNat 0 ∧ Rest [.r0, .r1, .r2] t u := by
  have hL : 0 < (s₀.gpr .r1).toNat := by
    have := A.outLength; have := A.lengths; unfold Spec.Dsa.lengthsValid at *; omega
  unfold zeroOut
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ?_)
  have R₃ : Rest [.r0, .r1, .r2] t t₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZeroInv s₀ t 0 t₃ := ⟨h.congr R₃ (by rw [m₃]; exact Frame.refl _ _),
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), R₃⟩
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = (s₀.gpr .r1).toNat - k ∧
      k < (s₀.gpr .r1).toNat ∧ ZeroInv s₀ t k u) (fun n u hu => ?_) _ t₃ ⟨0, rfl, hL, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok A hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : (s₀.gpr .r1).toNat - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, J.ready, J.frame, ?_, J.rest⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega)
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, _, by omega, k + 1, rfl, by omega, J⟩

/-- A write apart from the stack keeps the frame's slots. -/
theorem apart_slot {s₀ : State} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hd : (rStack s₀).Disjoint r)
    {d : Nat} (hd' : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      refine hd.sub_left ?_
      rw [rBase_off]; exact Offset.sub_base _ (by unfold frameBytes at hd'; omega)) (by decide)

/-! ## The exit -/

/-- After the attempts, ready to finish. -/
structure RFin (s₀ t : State) : Prop where
  ready : RReady s₀ t
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  saved : Saved s₀ t.mem

/-- What the signer returns, writes and publishes, before the frame is freed. -/
structure Finished (s₀ u : State) : Prop where
  sp : u.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : u.rd = s₀.rd
  wr : u.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem u.mem
  r0 : u.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status
  regs : ∀ r ∈ preserved, u.gpr r = s₀.gpr r
  out : Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  usedLo : slot u.mem (State.addr (s₀.gpr .r2)) 0 = BitVec.ofNat 32 (rResult s₀).used
  usedHi : slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0

theorem restore_eq : ((savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) : List Instr) =
    [ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32] := rfl

theorem clearMem_frame (s₀ : State) (m : Mem) : ∀ k, k ≤ 8 → Frame [rStack s₀] m (clearMem m (rBase s₀) k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => (clearMem_frame s₀ m k (by omega)).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce frameBytes; omega) 0)

/-- The last block: clear the nonce, publish the consumption, restore the registers. -/
abbrev finalList : List Instr :=
  [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
    ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28]

theorem finalBlock_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem)
    {used st : BitVec 32} (hu : slot t.mem (rBase s₀) oUsed = used)
    (hs : slot t.mem (rBase s₀) oStatus = st) :
    WP isa (.block (clearNonce ++ finalList)) t fun u =>
      u.sp = t.sp ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ Frame [rStack s₀, rUsed s₀] t.mem u.mem ∧ u.gpr .r0 = st ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ slot u.mem (State.addr (s₀.gpr .r2)) 0 = used ∧
      slot u.mem (State.addr (s₀.gpr .r2)) 4 = 0 := by
  have hub := A.usedBound
  refine clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_
  have fr₁ : Frame [rStack s₀] t.mem t₁.mem := by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide)
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  have sl₁ : ∀ d, d + 4 ≤ oNonce → slot t₁.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Nat.le_refl _) hd
      (by unfold oNonce at hd; omega)
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ld (h₁.upd u₂) (by decide) fun t₃ u₃ => ?_
  have h₃ := (h₁.upd u₂).upd u₃
  have r4₃ : t₃.gpr .r4 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.gpr]; exact sv₁.2.2.2.1
  have r0₃ : t₃.gpr .r0 = used := by rw [u₃.gpr, u₂.mem, sl₁ _ (by decide), hu]
  have hU : (rUsed s₀) ∈ t₃.wr := by rw [h₃.wr, A.wr]; simp
  refine wp_str (a := State.addr (s₀.gpr .r2)) (by decide) (by rw [BitVec.add_zero, r4₃])
    ⟨_, hU, by
      have := Offset.contains_base (State.addr (s₀.gpr .r2)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩ fun t₄ m₄ => wp_mov (op2_imm (by decide)) fun t₅ u₅ => ?_
  refine wp_str (a := State.addr (s₀.gpr .r2) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₅.other _ (by decide), m₄.gpr, r4₃, VG.Arm.addr_add (by omega)])
    ⟨_, by rw [u₅.wr, m₄.wr]; exact hU, Offset.contains_base _ (by decide) (by decide)⟩ fun t₆ m₆ => ?_
  have mem₆ : t₆.mem = (t₃.mem.writeW (off (State.addr (s₀.gpr .r2)) 0) used).writeW
      (off (State.addr (s₀.gpr .r2)) 4) (0 : BitVec 32) := by
    rw [m₆.mem, u₅.gpr, u₅.mem, m₄.mem, r0₃, off, BitVec.add_zero]
  have fu : Frame [rUsed s₀] t₃.mem t₆.mem := by
    rw [mem₆]
    exact (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have ap : ∀ d, d + 4 ≤ frameBytes → slot t₆.mem (rBase s₀) d = slot t₃.mem (rBase s₀) d := fun d hd =>
    apart_slot fu A.stackUsed hd
  have m₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have h₆ : RReady s₀ t₆ := h₃.congrW (ws := [.r0]) ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _))) fu
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])
  have sv₆ : Saved s₀ t₆.mem := sv₁.of_slots fun d _ hd => by rw [ap d hd, m₃]
  have hst₆ : slot t₆.mem (rBase s₀) oStatus = st := by rw [ap _ (by decide), m₃, sl₁ _ (by decide), hs]
  obtain ⟨sr, -⟩ := sv₆
  refine wp_ld h₆ (by decide) fun t₇ u₇ => ?_
  have h₇ := h₆.upd u₇
  refine wp_ld h₇ (by decide) fun t₈ u₈ => wp_ld (h₇.upd u₈) (by decide) fun t₉ u₉ =>
    wp_ld ((h₇.upd u₈).upd u₉) (by decide) fun t₁₀ u₁₀ =>
    wp_ld (((h₇.upd u₈).upd u₉).upd u₁₀) (by decide) fun t₁₁ u₁₁ =>
    wp_ld ((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁) (by decide) fun t₁₂ u₁₂ =>
    wp_ld (((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂) (by decide) fun t₁₃ u₁₃ =>
    wp_ld ((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃) (by decide) fun t₁₄ u₁₄ =>
    wp_ld (((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄) (by decide) fun t₁₅ u₁₅ =>
    wp_ld ((((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄).upd u₁₅) (by decide)
      fun t₁₆ u₁₆ => WP.block_nil ?_
  have mm : t₁₆.mem = t₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have R : Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] t₆ t₁₆ :=
    (u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
      ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans ((u₁₃.rest (by decide)).trans
      ((u₁₄.rest (by decide)).trans ((u₁₅.rest (by decide)).trans (u₁₆.rest (by decide))))))))))
  have R₆ : Rest [.r0, .r2, .r4] t t₆ := ((k₁.mono (by decide)).trans ((u₂.rest (by decide)).trans
    (u₃.rest (by decide)))).trans ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _)))
  have hm : ∀ t' : State, t'.mem = t₆.mem → ∀ i < 9, slot t'.mem (rBase s₀) (4 * i) =
      s₀.gpr (savedRegs.getD i .r0) := fun t' e i hi => by rw [e]; exact sr i hi
  refine ⟨by rw [R.sp, R₆.sp], by rw [R.rd, R₆.rd], by rw [R.wr, R₆.wr], ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [mm]; exact (fr₁.mono (by simp)).trans ((show Frame [rUsed s₀] t₁.mem t₆.mem by rw [← m₃]; exact fu).mono
      (by simp))
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.gpr, hst₆]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, u₉.get, reduceCtorEq, ↓reduceIte,
        u₈.gpr, u₇.mem]
      exact hm t₆ rfl 0 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, reduceCtorEq, ↓reduceIte, u₉.gpr]
      exact hm t₈ (by rw [u₈.mem, u₇.mem]) 1 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, reduceCtorEq, ↓reduceIte, u₁₀.gpr]
      exact hm t₉ (by rw [u₉.mem, u₈.mem, u₇.mem]) 2 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, reduceCtorEq, ↓reduceIte, u₁₁.gpr]
      exact hm t₁₀ (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 3 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, u₁₃.get, reduceCtorEq, ↓reduceIte, u₁₂.gpr]
      exact hm t₁₁ (by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 4 (by decide)
    · simp only [u₁₆.get, u₁₅.get, u₁₄.get, reduceCtorEq, ↓reduceIte, u₁₃.gpr]
      exact hm t₁₂ (by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 5 (by decide)
    · simp only [u₁₆.get, u₁₅.get, reduceCtorEq, ↓reduceIte, u₁₄.gpr]
      exact hm t₁₃ (by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 6 (by decide)
    · rw [u₁₆.gpr]
      exact hm t₁₅ (by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 7
        (by decide)
    · simp only [u₁₆.get, reduceCtorEq, ↓reduceIte, u₁₅.gpr]
      exact hm t₁₄ (by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]) 8 (by decide)
  · rw [mm, mem₆, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]
  · rw [mm, mem₆, slot_write_self]

theorem finishBlock_eq : (clearNonce ++ [ld .r4 oUsedPtr, ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0),
    .str .r0 .r4 4, ld .r0 oStatus] ++ (savedRegs.zipIdx.filter (·.1 != .r11)).map (fun (r, i) => ld r (4 * i)) ++
    [ld .r11 28] : List Instr) = clearNonce ++ finalList := by
  rw [restore_eq]; rfl

theorem rfinish_ok {s₀ t : State} (A : KeyABI s₀) (F : RFin s₀ t) (hR : (rResult s₀).status ≤ 2)
    (hsig : (rResult s₀).status ≠ 1 → (rResult s₀).key = none) :
    WP isa finish t fun u => Finished s₀ u := by
  have h := F.ready
  have hb := A.outBound
  have hout : ∀ {m m' : Mem}, Frame [rStack s₀, rUsed s₀] m m' →
      Spec.Rsa.bytesAt m' (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        Spec.Rsa.bytesAt m (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat := fun hf =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.stackOut.symm
      · exact A.outUsed) (by omega)
  unfold finish
  rw [finishBlock_eq]
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  have h₂ := (h.upd u₁).fupd f₂
  have m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  have R₂ : Rest [.r0] t t₂ := (u₁.rest (by decide)).trans (f₂.rest _)
  rw [u₁.gpr, F.status, one_beq (by omega)] at z₂
  have fin : ∀ v : State, RReady s₀ v → Rest [.r0, .r1, .r2] t v → Frame (rWrites s₀) t.mem v.mem →
      Saved s₀ v.mem → slot v.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used →
      slot v.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status →
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0) →
      WP isa (.block (clearNonce ++ finalList)) v fun u => Finished s₀ u := fun v hv Rv fv sv hu hs ho =>
    WP.mono (finalBlock_ok A hv sv hu hs) fun u ⟨sp, rd, wr, fr, r0, regs, lo, hi⟩ =>
      ⟨by rw [sp, Rv.sp, h.sp], by rw [rd, Rv.rd, h.rd], by rw [wr, Rv.wr, h.wr],
        hv.frame.trans (fr.mono (by simp [rWrites])), r0, regs, by rw [hout fr]; exact ho, lo, hi⟩
  by_cases h1 : (rResult s₀).status = 1
  · refine WP.seq (WP.ite false (by rw [eval_ne, z₂, decide_eq_true h1]; rfl)
      (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact fin t₂ h₂ (R₂.mono (by decide)) (by rw [m₂]; exact Frame.refl _ _) (by rw [m₂]; exact F.saved)
      (by rw [m₂]; exact F.usedW) (by rw [m₂]; exact F.status) (by rw [m₂]; exact F.out h1)
  · refine WP.seq (WP.ite true (by rw [eval_ne, z₂, decide_eq_false h1]; rfl)
      (fun _ => WP.mono (zeroOut_ok A h₂ (by rw [m₂]; exact F.saved)) fun v ⟨hv, fv, zv, Rv⟩ => ?_)
      (fun e => Bool.noConfusion e))
    have ap : ∀ d, d + 4 ≤ frameBytes → slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd => by
      rw [apart_slot fv A.stackOut hd, m₂]
    exact fin v hv ((R₂.mono (by decide)).trans Rv) (by rw [← m₂]; exact fv.mono (by simp [rWrites]))
      (F.saved.of_slots fun d _ hd => ap d hd) (by rw [ap _ (by decide)]; exact F.usedW)
      (by rw [ap _ (by decide)]; exact F.status) (by rw [zv, hsig h1]; rfl)

end VG.Proof.Dsa.Arm.Key
