module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Prepare
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Draw
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Saved
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! ### `Dsa.Arm.Key.Finish`, which this module and modules that import it used -/

section

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
  obtain hw : InRegions t.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) 1 :=
    ⟨rOut s₀, by rw [I.ready.wr, A.wr]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine wp_strb (by decide) (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega_arith)]) hw fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  obtain hv : (t.gpr .r0).setWidth 8 = 0 := by rw [I.r0]; rfl
  rw [hv] at m₁
  obtain R : Rest [.r0, .r1, .r2] t u₃ := (m₁.rest _).trans ((v₂.rest (by decide)).trans (v₃.rest (by decide)))
  obtain mem₃ : u₃.mem = t.mem.writeW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  obtain fr : Frame [rOut s₀] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨⟨I.ready.congrW R fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites]),
    ?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.rest.trans R⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r1, Offset.add_ofNat_add_one]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.r0]
  · rw [mem₃]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · have ho : ofs (State.addr (s₀.gpr .r0)) (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) = i := by
        rw [ofs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      rw [show State.addr (s₀.gpr .r0) + BitVec.ofNat 64 k = off (State.addr (s₀.gpr .r0)) k from rfl,
        writeW8_outside _ _ (d := k) _ (by omega_arith) _ (by rw [ho]; omega_arith)]
      exact I.zero i (by omega_arith)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.r2, ofNat_sub_one (by omega_arith), ofNat_beq_zero (by omega_arith),
      Nat.sub_sub]

theorem zeroOut_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa zeroOut t fun u => RReady s₀ u ∧ Frame [rOut s₀] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        List.replicate (s₀.gpr .r1).toNat 0 ∧ Rest [.r0, .r1, .r2] t u := by
  obtain hL : 0 < (s₀.gpr .r1).toNat := by
    have := A.outLength; have := A.lengths; unfold Spec.Dsa.lengthsValid at *; omega_arith
  unfold zeroOut
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ?_)
  obtain R₃ : Rest [.r0, .r1, .r2] t t₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain I₀ : ZeroInv s₀ t 0 t₃ := ⟨h.congr R₃ (by rw [m₃]; exact Frame.refl _ _),
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
      exact J.zero i (by omega_arith)
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, _, by omega_arith, k + 1, rfl, by omega_arith, J⟩

/-- A write apart from the stack keeps the frame's slots. -/
theorem apart_slot {s₀ : State} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hd : (rStack s₀).Disjoint r)
    {d : Nat} (hd' : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      refine hd.sub_left ?_
      rw [rBase_off]; exact Offset.sub_base _ (by unfold frameBytes at hd'; omega_arith)) (by decide)

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
  | k + 1, hk => (clearMem_frame s₀ m k (by omega_arith)).trans
      (frame_store s₀ _ (d := oNonce + 4 * k) (by unfold oNonce frameBytes; omega_arith) 0)

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
  obtain fr₁ : Frame [rStack s₀] t.mem t₁.mem := by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide)
  obtain o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  obtain sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  obtain sl₁ : ∀ d, d + 4 ≤ oNonce → slot t₁.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Nat.le_refl _) hd
      (by unfold oNonce at hd; omega_arith)
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ld (h₁.upd u₂) (by decide) fun t₃ u₃ => ?_
  obtain h₃ := (h₁.upd u₂).upd u₃
  obtain r4₃ : t₃.gpr .r4 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.gpr]; exact sv₁.2.2.2.1
  obtain r0₃ : t₃.gpr .r0 = used := by rw [u₃.gpr, u₂.mem, sl₁ _ (by decide), hu]
  obtain hU : (rUsed s₀) ∈ t₃.wr := by rw [h₃.wr, A.wr]; simp
  refine wp_str (a := State.addr (s₀.gpr .r2)) (by decide) (by rw [BitVec.add_zero, r4₃])
    ⟨_, hU, by
      have := Offset.contains_base (State.addr (s₀.gpr .r2)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩ fun t₄ m₄ => wp_mov (op2_imm (by decide)) fun t₅ u₅ => ?_
  refine wp_str (a := State.addr (s₀.gpr .r2) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₅.other _ (by decide), m₄.gpr, r4₃, VG.Arm.addr_add (by omega_arith)])
    ⟨_, by rw [u₅.wr, m₄.wr]; exact hU, Offset.contains_base _ (by decide) (by decide)⟩ fun t₆ m₆ => ?_
  obtain mem₆ : t₆.mem = (t₃.mem.writeW (off (State.addr (s₀.gpr .r2)) 0) used).writeW
      (off (State.addr (s₀.gpr .r2)) 4) (0 : BitVec 32) := by
    rw [m₆.mem, u₅.gpr, u₅.mem, m₄.mem, r0₃, off, BitVec.add_zero]
  obtain fu : Frame [rUsed s₀] t₃.mem t₆.mem := by
    rw [mem₆]
    exact (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain ap : ∀ d, d + 4 ≤ frameBytes → slot t₆.mem (rBase s₀) d = slot t₃.mem (rBase s₀) d := fun d hd =>
    apart_slot fu A.stackUsed hd
  obtain m₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  obtain h₆ : RReady s₀ t₆ := h₃.congrW (ws := [.r0]) ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _))) fu
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])
  obtain sv₆ : Saved s₀ t₆.mem := sv₁.of_slots fun d _ hd => by rw [ap d hd, m₃]
  obtain hst₆ : slot t₆.mem (rBase s₀) oStatus = st := by rw [ap _ (by decide), m₃, sl₁ _ (by decide), hs]
  obtain ⟨sr, -⟩ := sv₆
  refine wp_ld h₆ (by decide) fun t₇ u₇ => ?_
  obtain h₇ := h₆.upd u₇
  refine wp_ld h₇ (by decide) fun t₈ u₈ => wp_ld (h₇.upd u₈) (by decide) fun t₉ u₉ =>
    wp_ld ((h₇.upd u₈).upd u₉) (by decide) fun t₁₀ u₁₀ =>
    wp_ld (((h₇.upd u₈).upd u₉).upd u₁₀) (by decide) fun t₁₁ u₁₁ =>
    wp_ld ((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁) (by decide) fun t₁₂ u₁₂ =>
    wp_ld (((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂) (by decide) fun t₁₃ u₁₃ =>
    wp_ld ((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃) (by decide) fun t₁₄ u₁₄ =>
    wp_ld (((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄) (by decide) fun t₁₅ u₁₅ =>
    wp_ld ((((((((h₇.upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂).upd u₁₃).upd u₁₄).upd u₁₅) (by decide)
      fun t₁₆ u₁₆ => WP.block_nil ?_
  obtain mm : t₁₆.mem = t₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain R : Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] t₆ t₁₆ :=
    (u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
      ((u₁₁.rest (by decide)).trans ((u₁₂.rest (by decide)).trans ((u₁₃.rest (by decide)).trans
      ((u₁₄.rest (by decide)).trans ((u₁₅.rest (by decide)).trans (u₁₆.rest (by decide))))))))))
  obtain R₆ : Rest [.r0, .r2, .r4] t t₆ := ((k₁.mono (by decide)).trans ((u₂.rest (by decide)).trans
    (u₃.rest (by decide)))).trans ((m₄.rest _).trans ((u₅.rest (by decide)).trans (m₆.rest _)))
  obtain hm : ∀ t' : State, t'.mem = t₆.mem → ∀ i < 9, slot t'.mem (rBase s₀) (4 * i) =
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
  obtain hout : ∀ {m m' : Mem}, Frame [rStack s₀, rUsed s₀] m m' →
      Spec.Rsa.bytesAt m' (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        Spec.Rsa.bytesAt m (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat := fun hf =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.stackOut.symm
      · exact A.outUsed) (by omega_arith)
  unfold finish
  rw [finishBlock_eq]
  refine WP.seq (wp_ld h (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_)
  obtain h₂ := (h.upd u₁).fupd f₂
  obtain m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  obtain R₂ : Rest [.r0] t t₂ := (u₁.rest (by decide)).trans (f₂.rest _)
  rw [u₁.gpr, F.status, one_beq (by omega_arith)] at z₂
  obtain fin : ∀ v : State, RReady s₀ v → Rest [.r0, .r1, .r2] t v → Frame (rWrites s₀) t.mem v.mem →
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
    obtain ap : ∀ d, d + 4 ≤ frameBytes → slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd => by
      rw [apart_slot fv A.stackOut hd, m₂]
    exact fin v hv ((R₂.mono (by decide)).trans Rv) (by rw [← m₂]; exact fv.mono (by simp [rWrites]))
      (F.saved.of_slots fun d _ hd => ap d hd) (by rw [ap _ (by decide)]; exact F.usedW)
      (by rw [ap _ (by decide)]; exact F.status) (by rw [zv, hsig h1]; rfl)

end VG.Proof.Dsa.Arm.Key

end

end

/-!
# DSA key generation on 32-bit ARM: the body

The entry saves the registers (`entry_ok`); the domain check's call
(`callCheck_ok`) decides whether to sample; one budget of draws
(`sample_ok`) gives x or the status; with x, the derivation's call
(`callDerive_ok`) writes the key and its status. Every path leaves what
`rfinish_ok` needs: the specification's status, consumption and key.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

variable {umaal : Bool}

/-! ## The specification's result -/

/-- The checks of the domain, as the specification makes them. -/
abbrev rChecked (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- With valid lengths, the result is the check, the sampling and the derivation's. -/
theorem rResult_eq {s₀ : State} (A : KeyABI s₀) :
    rResult s₀ = if rChecked s₀ then
        match (spl s₀ 128 0).scalar with
        | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0), (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace⟩
        | some x =>
          let res := Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
            (Spec.Dsa.encodeBE (rInput s₀).qLen x)
          ⟨res, Spec.Dsa.signStatus res, (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace ++ [if res.isSome then 5 else 6]⟩
      else ⟨none, 0, 0, [4]⟩ := by
  obtain hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  rw [rResult, VG.Proof.Dsa.generateKeyBytes_eq hl hk, spl, List.drop_zero, ← rQ_decode]
  cases h : (Spec.Dsa.Random.sample (rq s₀) 128 (rInput s₀).rand).scalar <;>
    simp [VG.Proof.Dsa.Random.sampleStatus, h]

/-- A checked domain has q > 1. -/
theorem rq_of_checked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = true) : 1 < rq s₀ := by
  obtain hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  have := (VG.Proof.Dsa.Arm.checkParametersBytes_iff hl hk).mp hc
  obtain B := VG.Proof.Dsa.supported_bounds this.1.1
  rw [rQ_decode]; omega_arith

theorem rResult_unchecked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = false) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_eq A, hc]; rfl

/-! ## Memory the calls keep -/

abbrev frameR (s₀ : State) : Region := ⟨rBase s₀, frameBytes⟩

theorem frameR_sub (s₀ : State) : Region.Sub (frameR s₀) (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 32) (n := frameBytes) (k := 144) (by decide)
  exact this

/-- The frame's slots, apart from what a call wrote. -/
theorem slot_keep {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (frameR s₀) r) {d : Nat} (hd' : d + 4 ≤ frameBytes) :
    slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have : frameBytes = 112 := rfl; omega_arith))) (by decide)

theorem frame_low (s₀ : State) : Region.Disjoint (frameR s₀) ⟨rLow s₀, 32⟩ :=
  Offset.disjoint_base _ (Nat.le_refl 32) (by decide)

theorem check_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ checkWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [checkWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

theorem derive_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ deriveWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [deriveWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut.sub_left (frameR_sub s₀)
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

/-- The domain's bytes, which nothing writes. -/
theorem key_bytes {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
    Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (by have := (stackArg s₀ 0).isLt; omega_arith)
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-! ## The entry -/

/-- Before `r11` holds the frame's base, `r12` does. -/
structure PreR (s₀ t : State) : Prop where
  r12 : t.gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- `str r, [r12, #d]`, a slot of the frame. -/
theorem wp_strP {s₀ t : State} (A : KeyABI s₀) (P : PreR s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, PreR s₀ u → u.mem = t.mem.writeW (off (rBase s₀) d) (t.gpr r) → u.gpr = t.gpr →
      WP isa (.block is) u Q) :
    WP isa (.block (.str r .r12 d :: is)) t Q := by
  obtain hb := rBase_toNat A
  have hs := A.stackBound
  have hl := A.stackLow
  obtain ha : State.addr (t.gpr .r12 + BitVec.ofNat 32 d) = off (rBase s₀) d := by
    rw [P.r12, VG.Arm.addr_add (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_arith),
      alloc_base A]
  refine wp_str (by unfold frameBytes at hd; omega_arith) ha
    ⟨_, by rw [P.wr]; exact List.mem_cons_self, Offset.contains_base _ hd (by unfold frameBytes at *; omega_arith)⟩
    fun u m => k u ⟨by rw [m.gpr]; exact P.r12, m.sp.trans P.sp, m.rd.trans P.rd, m.wr.trans P.wr,
      P.frame.trans (by
        rw [m.mem]
        exact (frame_store s₀ t.mem hd (t.gpr r)).mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [rWrites])⟩ m.mem m.gpr

theorem entry_eq : GenerateKey.entry = [.addSp .r12 0, .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12,
    .str .r8 .r12 16, .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28, .str .lr .r12 32,
    .mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, st .r0 oStatus] := rfl

/-- Save the callee-saved registers and the register arguments, and start the counts. -/
theorem entry_ok {s₀ : State} (A : KeyABI s₀) :
    WP isa (.block GenerateKey.entry) (allocated frameBytes s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 ∧
      (∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s₀.gpr r) := by
  rw [entry_eq]
  refine VG.Proof.X25519.Arm.WP.cons (s' := (allocated frameBytes s₀).setReg .r12
    ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) (by simp [exec]) ?_
  obtain P₀ : PreR s₀ ((allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) :=
    ⟨by simp [State.setReg, allocated], rfl, rfl, by
      show ⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ :: s₀.wr = _; rw [alloc_base A],
      Frame.refl _ _⟩
  obtain g₀ : ∀ r, r ≠ .r12 → ((allocated frameBytes s₀).setReg .r12
      ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)).gpr r = s₀.gpr r := fun r h => by
    simp [State.setReg, allocated, h]
  refine wp_strP A P₀ (by decide) fun t₁ P₁ m₁ g₁ => wp_strP A P₁ (by decide) fun t₂ P₂ m₂ g₂ =>
    wp_strP A P₂ (by decide) fun t₃ P₃ m₃ g₃ => wp_strP A P₃ (by decide) fun t₄ P₄ m₄ g₄ =>
    wp_strP A P₄ (by decide) fun t₅ P₅ m₅ g₅ => wp_strP A P₅ (by decide) fun t₆ P₆ m₆ g₆ =>
    wp_strP A P₆ (by decide) fun t₇ P₇ m₇ g₇ => wp_strP A P₇ (by decide) fun t₈ P₈ m₈ g₈ =>
    wp_strP A P₈ (by decide) fun t₉ P₉ m₉ g₉ => wp_mov (op2_reg _ _) fun t₁₀ u₁₀ => ?_
  obtain gg : ∀ r, r ≠ .r12 → t₉.gpr r = s₀.gpr r := fun r h => by
    rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact g₀ r h
  obtain nw : (rBase s₀).toNat + frameBytes + 28 ≤ 2 ^ 32 := by
    rw [rBase_toNat A]; have := A.stackBound; have := A.stackLow; unfold frameBytes; omega_arith
  obtain h₁₀ : RReady s₀ t₁₀ :=
    ⟨⟨by rw [u₁₀.gpr, P₉.r12, alloc_base A], by rw [u₁₀.wr, P₉.wr]; exact List.mem_cons_self,
      by rw [u₁₀.rd, P₉.rd, A.rd, rBase_args A]; simp, nw⟩,
      u₁₀.sp.trans P₉.sp, u₁₀.rd.trans P₉.rd, u₁₀.wr.trans P₉.wr, by rw [u₁₀.mem]; exact P₉.frame⟩
  refine wp_st h₁₀ (by decide) fun t₁₁ m₁₁ h₁₁ => wp_st h₁₁ (by decide) fun t₁₂ m₁₂ h₁₂ =>
    wp_st h₁₂ (by decide) fun t₁₃ m₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ m₁₄ h₁₄ =>
    wp_mov (op2_imm (by decide)) fun t₁₅ u₁₅ => wp_st (h₁₄.upd u₁₅) (by decide) fun t₁₆ m₁₆ h₁₆ =>
    wp_st h₁₆ (by decide) fun t₁₈ m₁₈ h₁₈ => WP.block_nil ?_
  obtain e₁₄ : ∀ r, r ≠ .r11 → r ≠ .r12 → t₁₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [m₁₄.gpr, m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ h]; exact gg r h'
  obtain hm : t₁₈.mem = ((((((((((((((s₀.mem.writeW (off (rBase s₀) 0) (s₀.gpr .r4)).writeW
      (off (rBase s₀) 4) (s₀.gpr .r5)).writeW (off (rBase s₀) 8) (s₀.gpr .r6)).writeW
      (off (rBase s₀) 12) (s₀.gpr .r7)).writeW (off (rBase s₀) 16) (s₀.gpr .r8)).writeW
      (off (rBase s₀) 20) (s₀.gpr .r9)).writeW (off (rBase s₀) 24) (s₀.gpr .r10)).writeW
      (off (rBase s₀) 28) (s₀.gpr .r11)).writeW (off (rBase s₀) 32) (s₀.gpr .lr)).writeW
      (off (rBase s₀) oOut) (s₀.gpr .r0)).writeW (off (rBase s₀) oOutLen) (s₀.gpr .r1)).writeW
      (off (rBase s₀) oUsedPtr) (s₀.gpr .r2)).writeW (off (rBase s₀) oKey) (s₀.gpr .r3)).writeW
      (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := by
    obtain v0 : t₁₀.gpr .r0 = s₀.gpr .r0 := by rw [u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v1 : t₁₁.gpr .r1 = s₀.gpr .r1 := by rw [m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v2 : t₁₂.gpr .r2 = s₀.gpr .r2 := by
      rw [m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    obtain v3 : t₁₃.gpr .r3 = s₀.gpr .r3 := by
      rw [m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    rw [m₁₈.mem, m₁₆.gpr, u₁₅.gpr, m₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄.mem, m₁₃.mem, m₁₂.mem, m₁₁.mem, v0, v1, v2, v3,
      u₁₀.mem, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    simp only [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, g₀ _ (by decide : Reg.r4 ≠ .r12), g₀ _ (by decide : Reg.r5 ≠ .r12),
      g₀ _ (by decide : Reg.r6 ≠ .r12), g₀ _ (by decide : Reg.r7 ≠ .r12), g₀ _ (by decide : Reg.r8 ≠ .r12),
      g₀ _ (by decide : Reg.r9 ≠ .r12), g₀ _ (by decide : Reg.r10 ≠ .r12), g₀ _ (by decide : Reg.r11 ≠ .r12),
      g₀ _ (by decide : Reg.lr ≠ .r12)]
    rfl
  refine ⟨h₁₈, ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h0 h11 h12 => ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by omega_arith
    all_goals (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; rfl)
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | skip
  rw [m₁₈.gpr, m₁₆.gpr, u₁₅.other _ h0]; exact e₁₄ r h11 h12


/-! ## The results -/

theorem sampleStatus_none {S : Spec.Dsa.Random.Sample} (h : S.scalar = none) :
    VG.Proof.Dsa.Random.sampleStatus S ≠ 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; simp only [h]; split <;> omega_arith

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} {k : Nat} (h : S.scalar = some k) :
    VG.Proof.Dsa.Random.sampleStatus S = 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; rw [h]

theorem rResult_status_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_eq A]
  split
  · split
    · exact sampleStatus_le _
    · have := status_lt (Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen ‹_›)); dsimp only; omega_arith
  · decide

theorem rResult_key {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≠ 1 → (rResult s₀).key = none := by
  rw [rResult_eq A]
  split
  · split
    · intro _; rfl
    · dsimp only; unfold Spec.Dsa.signStatus; split
      · intro h; exact absurd rfl h
      · next h => intro _; simpa using h
  · intro _; rfl

/-! ## The body -/

theorem body_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (body check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) (allocated frameBytes s₀)
      fun u => Finished s₀ u := by
  obtain hql := rQBytes_le A
  obtain hqn := rQBytes_length A
  obtain hfit := rWidth_le s₀
  have hF : frameBytes = 112 := rfl
  unfold body
  refine WP.seq (WP.mono (entry_ok A) fun t₁ ⟨h₁, sv₁, us₁, st₁, _⟩ => ?_)
  refine WP.seq (WP.mono (checkArgs_ok A h₁ sv₁) fun t₂ ⟨h₂, m₂, C₂, _⟩ => ?_)
  refine WP.seq (WP.mono (callCheck_ok A h₂ C₂ check) fun t₃ ⟨h₃, f₃, _, r0₃⟩ => ?_)
  obtain sl₃ : ∀ d, d + 4 ≤ frameBytes → slot t₃.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd => by
    rw [slot_keep f₃ (check_keeps A) hd, m₂]
  obtain hck : checkResult s₀ t₂ = rChecked s₀ := by
    unfold checkResult; rw [key_bytes A h₂]; rfl
  rw [hck] at r0₃
  obtain sv₃ : Saved s₀ t₃.mem := sv₁.of_slots fun d _ hd => sl₃ d hd
  refine WP.seq (wp_cmp0 fun t₄ f₄ z₄ => WP.block_nil ?_)
  obtain h₄ := h₃.fupd f₄
  have m₄ : t₄.mem = t₃.mem := f₄.mem
  rw [r0₃] at z₄
  suffices H : WP isa (.ite .eq (.block []) (generate derive (Generate.deriveChecked umaal))) t₄ (RFin s₀) from
    WP.seq (WP.mono H fun u hu => rfinish_ok A hu (rResult_status_le A) (rResult_key A))
  by_cases hc : rChecked s₀ = true
  · rw [hc] at z₄
    refine WP.ite false (by rw [eval_eq, z₄]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    obtain hq := rq_of_checked A hc
    obtain sv₄ : Saved s₀ t₄.mem := by rw [m₄]; exact sv₃
    unfold generate
    refine WP.seq (WP.mono (prepare_ok A h₄ sv₄.2.2.2.2) fun t₅ ⟨_, P₅, h₅, o₅, _⟩ => ?_)
    obtain P := P₅ hq
    obtain lo₅ : ∀ d, d + 4 ≤ oQ → slot t₅.mem (rBase s₀) d = slot t₄.mem (rBase s₀) d := fun d hd =>
      outs_low o₅ (by decide) hd (by unfold oQ at hd; omega_arith)
    obtain us₅ : slot t₅.mem (rBase s₀) oUsed = BitVec.ofNat 32 0 := by
      rw [lo₅ _ (by decide), m₄, sl₃ _ (by decide)]; exact us₁
    obtain S₅ : Smp s₀ 0 (slot t₅.mem (rBase s₀) oDraws).toNat t₅ :=
      ⟨h₅, P.q, P.width, P.mask, us₅, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => P.nonce i (by omega_arith), Nat.zero_le _⟩
    obtain sv₅ : Saved s₀ t₅.mem := sv₄.of_outs o₅ (by decide)
    refine WP.seq (WP.mono (sample_ok A S₅ hq) fun t₆ ⟨O₆, r0₆, h₆, o₆, _⟩ => ?_)
    obtain sv₆ : Saved s₀ t₆.mem := sv₅.of_outs o₆ (by decide)
    obtain ⟨d₆, Sm₆⟩ := O₆.smp
    obtain hR := rResult_eq A
    simp only [hc, ↓reduceIte] at hR
    unfold derived
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun t₇ f₇ z₇ => WP.block_nil ?_)
    obtain h₇ := h₆.fupd f₇
    have m₇ : t₇.mem = t₆.mem := f₇.mem
    rw [r0₆, one_beq (by have := sampleStatus_le (spl s₀ 128 0); omega_arith)] at z₇
    cases hk : (spl s₀ 128 0).scalar with
    | none =>
      simp only [hk] at hR
      obtain hn := sampleStatus_none hk
      refine WP.ite false (by rw [eval_eq, z₇, decide_eq_false hn]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨h₇, ?_, ?_, fun e => by rw [hR] at e; exact absurd e hn, by rw [m₇]; exact sv₆⟩
      · rw [m₇, Sm₆.usedW, hR]; simp
      · rw [m₇, O₆.status, hR]
    | some k =>
      simp only [hk] at hR
      obtain h1 := sampleStatus_some hk
      refine WP.ite true (by rw [eval_eq, z₇, decide_eq_true h1]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine WP.seq (WP.mono (deriveArgs_ok A h₇ (by rw [m₇]; exact sv₆)) fun t₈ ⟨h₈, m₈, C₈, _⟩ => ?_)
      refine WP.seq (WP.mono (callDerive_ok A h₈ C₈ derive (by rw [key_bytes A h₈]; exact hc))
        fun t₉ ⟨h₉, f₉, _, r0₉, out₉⟩ => ?_)
      refine wp_st h₉ (by decide) fun t₁₀ mm₁₀ h₁₀ => WP.block_nil ?_
      -- What the derivation read.
      obtain hres : deriveResult s₀ t₈ = Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
          (Spec.Dsa.encodeBE (rInput s₀).qLen k) := by
        unfold deriveResult
        rw [key_bytes A h₈, m₈, m₇, ← hqn, O₆.nonce k hk, hqn]
        rfl
      rw [hres] at r0₉ out₉
      obtain sl₉ : ∀ d, d + 4 ≤ frameBytes → slot t₉.mem (rBase s₀) d = slot t₆.mem (rBase s₀) d := fun d hd => by
        rw [slot_keep f₉ (derive_keeps A) hd, m₈, m₇]
      have mem₁₀ : t₁₀.mem = t₉.mem.writeW (off (rBase s₀) oStatus) (t₉.gpr .r0) := mm₁₀.mem
      refine ⟨h₁₀, ?_, ?_, fun _ => ?_, ?_⟩
      · rw [mem₁₀, slot_write_ne _ _ _ (by decide) (by decide) (by decide), sl₉ _ (by decide), Sm₆.usedW, hR]
        simp
      · rw [mem₁₀, slot_write_self, r0₉, hR]
      · rw [mem₁₀, rBytes_frame (frame_store s₀ t₉.mem (by decide) _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm)
          (by have := (s₀.gpr .r1).isLt; omega_arith), out₉, hR]
      · exact sv₆.of_slots fun d hd hd' => by
          rw [mem₁₀, slot_write_ne _ _ _ (by unfold oStatus; omega_arith) (by omega_arith) (by decide), sl₉ d hd']
  · have hc' : rChecked s₀ = false := by simpa using hc
    rw [hc'] at z₄
    refine WP.ite true (by rw [eval_eq, z₄]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    obtain hR := rResult_unchecked A hc'
    refine ⟨h₄, ?_, ?_, fun e => by rw [hR] at e; exact absurd e (by decide), by rw [m₄]; exact sv₃⟩
    · rw [m₄, sl₃ _ (by decide), us₁, hR]; rfl
    · rw [m₄, sl₃ _ (by decide), st₁, hR]; rfl

end VG.Proof.Dsa.Arm.Key
