module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Aes

/-!
# AES-CFB8 on RISC-V: the contracts, and the loop

As on PPC64LE (`Proof/AesCfb8/PPC64LE/Loop.lean`): the artifacts' contracts
are the shared ones of `Spec/Cfb8/Contract.lean`, which imply these
(`Verified.lean`): `cfb8RISCV64 enc`, for encryption (`enc = true`) and
decryption. The functions have AES-CBC's arguments, with `len` counting
bytes, and its prologue and epilogue (`Proof/AesCbc/RISCV64/Loop.lean`),
whose stride-free lemmas this reuses.

The invariant after `k` bytes (`LInv`): `s1`–`s6` hold the arguments (`s4`
the next byte, `s5` the bytes left), the other callee-saved registers are
our caller's, only the input block, the data, the block function's working
space and the block at `sv` have changed since the registers were saved,
the first `k` bytes are CFB8's of the first `k` bytes on entry and the rest
are unchanged, and the input block is the one after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes (`BodyOk`), `whole body` meets the contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Proof.AesCbc.RISCV64 (wK W R Iv Dp N S q sv schR ivR scrR wsR cR iv0 saveL saveG savedMem vars
  in_rw savedMem_frame saved_bound save_eq restore_eq a1_ofNat a4_ofNat bytesAt_frame savePtr_ok
  slots_sub slot_sub slot_contains q_lt sv_eq sv_add cR_sub wsR_sub)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = a0, rounds = a1, iv = a2, data = a3, len = a4, scratch = a5)`. -/
def cfb8RISCV64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .a1).toNat (bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .a2) 16
    let xs := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
    bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .a2) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

section
variable (s₀ : State)

abbrev dataR : Region := ⟨Dp s₀, N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem (Dp s₀) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 k

/-- The first `k` bytes after CFB8. -/
abbrev outK (enc : Bool) (k : Nat) : List Byte := cfb8 enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- The input block after the first `k` bytes. -/
abbrev inKk (enc : Bool) (k : Nat) : List Byte := inK enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- What the code may write once the registers are saved. -/
abbrev Mut : List Region := [ivR s₀, dataR s₀, wsR s₀, cR s₀]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8RISCV64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = byt s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (Mut s₀) (savedMem s₀) s.mem
  data : bytesAt s.mem (Dp s₀) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = inKk s₀ enc k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem UPre.byt_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem UPre.cR_wsR (hp : UPre s₀) : (cR s₀).Disjoint (wsR s₀) := by
  have := q_lt s₀
  have := hp.scr_wrap
  rw [cR, sv_eq]; exact Offset.disjoint_base _ (by omega) (by omega)

end

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame (Mut s₀) (savedMem s₀) m) : Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slots_sub s₀⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, wsR_sub⟩
    · exact ⟨scrR s₀, by simp, cR_sub⟩)

/-- The bytes after a step that changed only byte `k`, the input block, the
working space and the block at `sv`. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, wsR s₀, cR s₀] m m') :
    bytesAt m' (Dp s₀) (N s₀) = (bytesAt m (Dp s₀) (N s₀)).set k (m' (byt s₀ k)) := by
  refine AesCfb8.bytesAt_set fun j hj hjk => ?_
  have e := bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right wsR_sub
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right cR_sub

end

theorem length_bs (s₀ : State) : (bs s₀).length = N s₀ := by simp [bytesAt]

/-- Byte `k` before the step, from the invariant. -/
theorem LInv.byte {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    s.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_arith
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem (by simp [bytesAt]; exact hk),
    List.getElem?_eq_getElem (by rw [length_bs]; exact hk)] at this
  simpa [bytesAt] using Option.some.inj this

theorem take_succ_bs (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (bs s₀).take (k + 1) = (bs s₀).take k ++ [(bs s₀)[k]'(by rw [length_bs]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk)]
  rfl

/-- What `advance` leaves after byte `k`: the registers of byte `k + 1`. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State} {Φ : State → Prop}
    (h4 : s.gpr .s4 = byt s₀ k) (h5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k))
    (h : ∀ s', s'.gpr .s4 = byt s₀ (k + 1) → s'.gpr .s5 = BitVec.ofNat 64 (N s₀ - (k + 1)) →
      (∀ r, r ≠ .s4 → r ≠ .s5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block Impl.AesCfb8.RISCV64.advance) s Φ := by
  have hN := (s₀.gpr .a4).isLt
  unfold Impl.AesCfb8.RISCV64.advance
  refine wp_addi (imm := 1) (by decide) fun s₁ u₁ => wp_subi (imm := 1) (by decide) fun s₂ u₂ =>
    WP.block_nil ?_
  refine h s₂ ?_ ?_ (fun r h₁ h₂ => ?_) ?_ ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr, h4, Offset.add_add_eq _ (c := k + 1) (by omega_arith)]
  · rw [u₂.gpr, u₁.other _ (by decide), h5, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  · rw [u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s (LInv enc s₀ (k + 1))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) :
    WP isa (.loop body (.nonzero .s5)) s (LInv enc s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .s5) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat s' .s5 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.s5
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv enc s₀ 0) := by
  have hN := (s₀.gpr .a4).isLt
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine Spill.save_ok (b := .t0) (l := saveL) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  unfold setup mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] →
      ∀ r' ∈ [(⟨sv s₀ + BitVec.ofNat 64 16, 56⟩ : Region)], r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (slots_sub s₀)
    · exact hp.data_scr.sub_right (slots_sub s₀)
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : bytesAt (savedMem s₀) (Dp s₀) (N s₀) = bs s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega_arith)
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    show Spill.saveMem s₀.mem ((s₀.write .t0 (sv s₀)).gpr .t0) _ _ = _
    rw [t₀]
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv s₀)).gpr r = s₀.gpr r :=
    RegUpd.gpr_write_of_ne _ _ hr
  exact {
    s1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .a0 (by decide)
    s2 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .a1 (by decide)
    s3 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a2 (by decide)
    s4 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a3 (by decide)]; simp
    s5 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a4 (by decide), a4_ofNat]; rfl
    s6 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a5 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
      rw [u₆.other _ h6, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
      exact g₀ _ (fun e => by subst e; revert hr; decide)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    data := by rw [m₆, dataS]; simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
    iv := by rw [m₆, ivS]; simp only [inKk, List.take_zero, inK_nil] }

/-- No bytes, or `mid` on all of them. -/
theorem ends_mid_wp {enc : Bool} {mid : Prog isa} {s₀ : State} {s₁ : State}
    (hm : 0 < N s₀ → WP isa mid s₁ (LInv enc s₀ (N s₀))) (h : LInv enc s₀ 0 s₁) :
    WP isa (.ite (.zero .s5) (.block []) mid) s₁ (LInv enc s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  have ev := eval_zero_ofNat s₁ .s5 (k := N s₀ - 0) (by omega_arith) h.s5
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hm (by omega_arith)

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ p ∈ saveL, ∀ r ∈ Mut s₀, Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  intro p hp' r hr
  have hb := saved_bound p hp'
  have := q_lt s₀
  have := hp.scr_wrap
  have hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := slot_sub s₀ hb.1 hb.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left hsub
  · exact hp.data_scr.symm.sub_left hsub
  · rw [sv_add]; exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [sv_add, cR, sv_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The postcondition of the whole function, but for the stack pointer. -/
def Done (enc : Bool) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ (cfb8RISCV64 enc).post s₀ s'

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (Done enc s₀) := by
  have hsv : Spill.Saved (sv s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame (slots_disj hp)
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₃ e => ?_
  subst e
  rw [h₂.s6]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saveL) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := saved_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 : r ≠ .t0 := fun e => by subst e; revert hr; decide
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr hv, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · show bytesAt s₄.mem (Dp s₀) (N s₀) = _
    rw [r₄.mem]
    show bytesAt s₂.mem (Dp s₀) (N s₀) = _
    rw [h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₄.mem (Iv s₀) 16 = _
    rw [r₄.mem]
    show bytesAt s₂.mem (Iv s₀) 16 = _
    rw [h₂.iv]; simp only [inKk, hall]

/-- The registers saved and the arguments set up, `mid` run unless there are
no bytes, and the registers restored. -/
theorem ends_wp {enc : Bool} {mid : Prog isa} {s₀ : State} (h0 : (cfb8RISCV64 enc).pre s₀)
    (hm : UPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv enc s₀ 0 s₁ → WP isa mid s₁ (LInv enc s₀ (N s₀))) :
    WP isa (.seq (.block (save ++ setup)) (.seq (.ite (.zero .s5) (.block []) mid) (.block restore)))
      s₀ (Done enc s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (ends_mid_wp (fun hn => hm hp hn h₁) h₁) fun _ h₂ => epilogue_wp hp h₂))

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State}
    (h0 : (cfb8RISCV64 enc).pre s₀) : WP isa (whole body) s₀ (Done enc s₀) :=
  ends_wp h0 fun hp hn _ h => loop_ok hb hp hn h

end VG.Proof.AesCfb8.RISCV64
