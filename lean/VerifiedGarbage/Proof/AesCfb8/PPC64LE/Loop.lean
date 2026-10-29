module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
public import VerifiedGarbage.Impl.AesCfb8.PPC64LE
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Aes

/-!
# AES-CFB8 on PPC64LE: the contracts, and the loop

As on x86-64 (`Proof/AesCfb8/X86_64/Loop.lean`): the artifacts' contracts
are the shared ones of `Spec/Cfb8/Contract.lean`, which imply these
(`Verified.lean`): `cfb8PPC64LE enc`, for encryption (`enc = true`) and
decryption. The functions have AES-CBC's arguments, with `len` counting
bytes, and its prologue and epilogue (`Proof/AesCbc/PPC64LE/Loop.lean`),
whose stride-free lemmas this reuses.

The invariant after `k` bytes (`LInv`): `r14`–`r19` hold the arguments
(`r17` the next byte, `r18` the bytes left), the other nonvolatile
registers are our caller's, only the input block, the data and the first
2064 bytes of the scratch buffer have changed since the registers were
saved, the first `k` bytes are CFB8's of the first `k` bytes on entry and
the rest are unchanged, and the input block is the one after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes (`BodyOk`), `whole body` meets the contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE
open VG.Proof.AesCbc.PPC64LE (wK W R Iv Dp N S schR ivR scrR iv0 saveL saveG savedMem vars in_rw
  savedMem_frame saved_bound save_eq restore_eq preserved_ne_r0 r4_ofNat r7_ofNat bytesAt_frame)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = r3, rounds = r4, iv = r5, data = r6, len = r7, scratch = r8)`. -/
def cfb8PPC64LE (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .r4).toNat (bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .r5) 16
    let xs := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
    bytesAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .r5) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

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

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8PPC64LE enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = byt s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  data : bytesAt s.mem (Dp s₀) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = inKk s₀ enc k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem UPre.byt_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

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
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

/-- The bytes after a step that changed only byte `k`, the input block and
the first 2064 bytes of the scratch buffer. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩] m m') :
    bytesAt m' (Dp s₀) (N s₀) = (bytesAt m (Dp s₀) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))

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
    (h17 : s.gpr .r17 = byt s₀ k) (h18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k))
    (h : ∀ s', s'.gpr .r17 = byt s₀ (k + 1) → s'.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + 1)) →
      (∀ r, r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → Φ s') :
    WP isa (.block Impl.AesCfb8.PPC64LE.advance) s Φ := by
  have hN := (s₀.gpr .r7).isLt
  unfold Impl.AesCfb8.PPC64LE.advance
  refine wp_addi (by decide) (by decide) fun s₁ u₁ => wp_subi (by decide) (by decide) fun s₂ u₂ => wp_nil ?_
  refine h s₂ ?_ ?_ (fun r h₁ h₂ => ?_) ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr, h17, Offset.add_add_eq _ (c := k + 1) (by omega_arith)]
  · rw [u₂.gpr, u₁.other _ (by decide), h18, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  · rw [u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s (LInv enc s₀ (k + 1))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) :
    WP isa (.loop body (.nonzero .d .r18)) s (LInv enc s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d .r18) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat' s' .r18 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.r18
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv enc s₀ 0) := by
  have hN := (s₀.gpr .r7).isLt
  rw [save_eq, List.cons_append]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saveL) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := saved_bound p hp'
    show InRegions s₀.wr (S s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  unfold setup mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] →
      ∀ r' ∈ [⟨S s₀ + BitVec.ofNat 64 2064, 56⟩], r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : bytesAt (savedMem s₀) (Dp s₀) (N s₀) = bs s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega_arith)
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; rfl
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  exact {
    r14 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .r3 (by decide)
    r15 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .r4 (by decide)
    r16 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r5 (by decide)
    r17 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r6 (by decide)]; simp
    r18 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .r7 (by decide), r7_ofNat]; rfl
    r19 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .r8 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h14, h15, h16, h17, h18, h19⟩ := hv
      rw [u₆.other _ h19, u₅.other _ h18, u₄.other _ h17, u₃.other _ h16, u₂.other _ h15, u₁.other _ h14]
      exact g₀ _ (preserved_ne_r0 r hr)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    data := by rw [m₆, dataS]; simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
    iv := by rw [m₆, ivS]; simp only [inKk, List.take_zero, inK_nil] }

/-- No bytes, or `mid` on all of them. -/
theorem ends_mid_wp {enc : Bool} {mid : Prog isa} {s₀ : State} {s₁ : State}
    (hm : 0 < N s₀ → WP isa mid s₁ (LInv enc s₀ (N s₀))) (h : LInv enc s₀ 0 s₁) :
    WP isa (.ite (.zero .d .r18) (.block []) mid) s₁ (LInv enc s₀ (N s₀)) := by
  have hN := (s₀.gpr .r7).isLt
  have ev := eval_zero_ofNat s₁ .r18 (k := N s₀ - 0) (by omega_arith) h.r18
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hm (by omega_arith)

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ p ∈ saveL, ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩],
      Region.Disjoint ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  intro p hp' r hr
  have hb := saved_bound p hp'
  have hsub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := UPre.scr_sub (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left hsub
  · exact hp.data_scr.symm.sub_left hsub
  · exact Offset.disjoint_base _ (by omega_arith) (by have := hp.scr_wrap; omega_arith)

/-- The postcondition of the whole function, but for the stack pointer. -/
def Done (enc : Bool) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ (cfb8PPC64LE enc).post s₀ s'

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (Done enc s₀) := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved (S s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame (slots_disj hp)
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore_eq]
  refine Spill.restore_ok (b := .r19) (l := saveL) (by decide) h₂.r19 (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => ?_
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by have := hp.scr_wrap; omega_arith))
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_, ?_⟩)
  · show s₃.gpr r = _
    have h0 : saveG s₀ r = s₀.gpr r := ite_eq_right_iff.mpr fun h => absurd h (preserved_ne_r0 r hr)
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h₂.keep r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, lrOff) (by decide)]; rfl
  · show bytesAt s₃.mem (Dp s₀) (N s₀) = _
    rw [r₃.mem, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [r₃.mem, h₂.iv]; simp only [inKk, hall]

/-- The registers saved and the arguments set up, `mid` run unless there are
no bytes, and the registers restored. -/
theorem ends_wp {enc : Bool} {mid : Prog isa} {s₀ : State} (h0 : (cfb8PPC64LE enc).pre s₀)
    (hm : UPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv enc s₀ 0 s₁ → WP isa mid s₁ (LInv enc s₀ (N s₀))) :
    WP isa (.seq (.block (save ++ setup)) (.seq (.ite (.zero .d .r18) (.block []) mid) (.block restore)))
      s₀ (Done enc s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (ends_mid_wp (fun hn => hm hp hn h₁) h₁) fun _ h₂ => epilogue_wp hp h₂))

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State}
    (h0 : (cfb8PPC64LE enc).pre s₀) : WP isa (whole body) s₀ (Done enc s₀) :=
  ends_wp h0 fun hp hn _ h => loop_ok hb hp hn h

end VG.Proof.AesCfb8.PPC64LE
