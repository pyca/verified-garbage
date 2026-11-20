module

public import VerifiedGarbage.Proof.AesCfb8.Rounds
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.AesCbc.AArch64.Body
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Body
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCfb8.AArch64
public import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
public import VerifiedGarbage.Proof.AesCfb8.Spec
meta import VerifiedGarbage.Impl.AesCfb8.AArch64
meta import VerifiedGarbage.Proof.AesCfb8.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Block
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
meta import VerifiedGarbage.Proof.AesCfb8.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Aes.AArch64.ModesScrub
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `AesCfb8.AArch64.CT`, which only this module used -/

section

/-! ### `AesCfb8.AArch64.Body`, which this module and modules that import it used -/

section

/-! ### `AesCfb8.AArch64.Loop`, which this module and modules that import it used -/

section

/-!
# AES-CFB8 on AArch64: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8AArch64 enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/AArch64/Loop.lean`), whose stride-free lemmas this reuses.

The invariant after `k` bytes (`LInv`): the registers hold the arguments
(`x22` the next byte, `x23` the bytes left), the other callee-saved
registers and the stack pointer are unchanged, only the input block, the
data and the first 2064 bytes of the scratch buffer have changed since the
registers were saved, the first `k` bytes are CFB8's of the first `k` bytes
on entry and the rest are unchanged, and the input block is the one after
them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes (`BodyOk`), `whole body` meets the contract.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR scrR iv0 wK in_rw savedMem savedMem_frame savedMem_slot
  slot_contains prologue_ok restore_ok x4_ofNat eval_x23 eval_zero_x23)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`
`(schedule = x0, rounds = x1, iv = x2, data = x3, len = x4, scratch = x5)`. -/
def cfb8AArch64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let iv : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .x2) 16
    let xs := bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
    bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .x2) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

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

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8AArch64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = byt s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
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
  Offset.sub_base _ (by omega_using [hk])

theorem UPre.byt_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_using [hjk]) (by omega_using [hj, this]) (by omega_using [hk, this])

end

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
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
  have e := Proof.Cmac.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
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
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega_using [hl]), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem (by simp [bytesAt]; exact hk),
    List.getElem?_eq_getElem (by rw [length_bs]; exact hk)] at this
  simpa [bytesAt] using Option.some.inj this

theorem take_succ_bs (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (bs s₀).take (k + 1) = (bs s₀).take k ++ [(bs s₀)[k]'(by rw [length_bs]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk)]
  rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.AesCfb8.AArch64.advance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 1 ∧ s'.gpr .x23 = s.gpr .x23 - 1 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [Impl.AesCfb8.AArch64.advance, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁, h₂]

/-- What `advance` leaves after byte `k`: the registers of byte `k + 1`. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State}
    (h22 : s.gpr .x22 = byt s₀ k) (h23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa Impl.AesCfb8.AArch64.advance s = some s' ∧ s'.gpr .x22 = byt s₀ (k + 1) ∧
      s'.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + 1)) ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, x22', x23', keep, sp', mem', rd', wr'⟩ := advance_ok s
  have hN := (s₀.gpr .x4).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hk])]; rfl
  refine ⟨s', run, ?_, ?_, keep, sp', mem', rd', wr'⟩
  · rw [x22', h22, Offset.add_add_eq _ (c := k + 1) (by omega_using [])]
  · rw [x23', h23, dec]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s (LInv enc s₀ (k + 1))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) :
    WP isa (.loop body (.nonzero .x .x23)) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .nonzero .x .x23) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hN]) h'.x23
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv enc s₀ 0) := by
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x24₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂]))
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] → ∀ r' ∈ [⟨s₀.gpr .x5 + BitVec.ofNat 64 2064, 56⟩],
      r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : bytesAt (savedMem s₀) (Dp s₀) (N s₀) = bs s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega_using [])
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  exact { x19 := x19₁, x20 := x20₁, x21 := x21₁
          x22 := by rw [x22₁]; simp
          x23 := by rw [x23₁, x4_ofNat]; rfl
          x24 := x24₁
          other := fun r _ h19 h20 h21 h22 h23 h24 _ => keep₁ r h19 h20 h21 h22 h23 h24
          sp := sp₁, rd := rd₁, wr := wr₁
          frame := by rw [mem₁]; exact Frame.refl _ _
          data := by
            rw [mem₁, dataS]
            simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
          iv := by
            rw [mem₁, ivS]
            simp only [inKk, List.take_zero, inK_nil] }

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23))) s₁ (LInv enc s₀ (N s₀)) := by
  have hN := (s₀.gpr .x4).isLt
  have ev := eval_zero_x23 (x := N s₀) hN (by rw [h.x23]; rfl)
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega_using [hn]) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩], (⟨S s₀ + BitVec.ofNat 64 2064, 56⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 8 ≤ 2120) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 56⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => GprAbi s₀ s' ∧ (cfb8AArch64 enc).post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, slot₃, keep₃, sp₃, mem₃⟩ :=
    restore_ok s₂ h₂.x24 fun d _ h₂' => by
      rw [rdwr, hp.rd, hp.wr]
      exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega_using [h₂']) (by have := hp.scr_wrap; omega_using [h₂']))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₃.gpr r = s₀.gpr r := by
    have hd : 2064 ≤ d ∧ d + 8 ≤ 2120 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      omega
    rw [slot₃ r d h, slot_read hp h₂.frame hd.1 hd.2, savedMem_slot s₀ h]
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp]⟩, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2064) (by simp [saved])
    · exact sl (d := 2072) (by simp [saved])
    · exact sl (d := 2080) (by simp [saved])
    · exact sl (d := 2088) (by simp [saved])
    · exact sl (d := 2096) (by simp [saved])
    · exact sl (d := 2112) (by simp [saved])
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact sl (d := 2104) (by simp [saved])
  · show bytesAt s₃.mem (Dp s₀) (N s₀) = _
    rw [mem₃, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [mem₃, h₂.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State}
    (h0 : (cfb8AArch64 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => GprAbi s₀ s' ∧ (cfb8AArch64 enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp hb hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.AArch64

end

end

/-! ### `AesCfb8.AArch64.Steps`, which only this module used -/

section

/-!
# AES-CFB8 on AArch64: the code between the calls

The straight-line pieces of a byte, run once each: the arguments of the
call on the copy of the input block (`args`), the data byte XORed with the
first byte of the enciphered block (`encByte`, `decByte`), and the input
block shifted (`shift`), with their memories as explicit writes
(`shiftMemX`, `Proof/AesCfb8/Mem.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb8.AArch64
open VG.Impl.AesCbc.AArch64 (mov cOff copy)

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

/-- The arguments of the call on the copy of the input block. -/
def args : List Instr := [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 2048, .movz .x .x3 1 0, mov .x4 .x24]

theorem pre_eq : pre = copy .x24 cOff .x21 0 ++ args := rfl

theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 2048 ∧
      s'.gpr .x3 = 1 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [args, exec_addImm_x (show 2048 < 4096 by decide)], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The byte instructions of `encPost`. -/
def encByte : List Instr := [.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x22 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr := [.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x10 .x10 .x9, .strb .x10 .x22 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ Impl.AesCfb8.AArch64.advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ Impl.AesCfb8.AArch64.advance) := rfl

theorem zext_zext (a : Byte) : (a.setWidth 32).setWidth 64 = a.setWidth 64 := by
  ext i hi; simp

theorem low_xor (a b : Byte) :
    (((a.setWidth 32).setWidth 64 ^^^ (b.setWidth 32).setWidth 64).setWidth 32).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem encByte_ok (s : State) {P T : Addr} (hp : s.gpr .x22 = P) (ht : s.gpr .x24 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa encByte s = some s' ∧ s'.gpr .x9 = (s.mem P ^^^ s.mem T).setWidth 64 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [encByte, cOff, read1, write1, hp, ht, rP, rT, wP], ?_⟩
  refine ⟨by simp [gpr_write], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem decByte_ok (s : State) {P T : Addr} (hp : s.gpr .x22 = P) (ht : s.gpr .x24 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1) :
    ∃ s', runBlock isa decByte s = some s' ∧ s'.gpr .x9 = (s.mem P).setWidth 64 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [decByte, cOff, read1, write1, hp, ht, rP, rT, wP], ?_⟩
  refine ⟨by simp [gpr_write, zext_zext], fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [low_xor]

theorem shift_ok (s : State) {Q : Addr} {c : Byte} (hq : s.gpr .x21 = Q) (hc : s.gpr .x9 = c.setWidth 64)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa shift s = some s' ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = AesCfb8.shiftMemX s.mem Q c ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [shift, hq, hc, r0, r8, w0, w8], ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, ?_, rfl, rfl⟩
  simp only [AesCfb8.shiftMemX, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

end VG.Proof.AesCfb8.AArch64

end

end


/-!
# AES-CFB8 on AArch64: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`). The input block is copied to the
scratch buffer and enciphered there (`call_ok`), the data byte is replaced,
and the input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb8.AArch64
open VG.Impl.AesCbc.AArch64 (cOff copy)
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR scrR iv0 wK in_rw Sv cIv0 cIv8 cSv0 cSv8 sv8 copy_ok
  CallPre CallPost blk_call x1_ofNat preserved_ne)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := Proof.Cmac.bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem LInv.regs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, this])

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨S s₀, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])

theorem UPre.sv_wrap : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega_using [this])]
  omega_using [this]

/-- The arguments of a call on the copy of the input block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPre {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = Sv s₀)
    (x3 : s.gpr .x3 = 1) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  wrap := hp.sv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Sv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copyMem s.mem (Sv s₀) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .x24) (src := .x21) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.x24]; rfl) (by rw [h.x24]; exact sv8 _)
      (by rw [h.x21]; simp) (by rw [h.x21])
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1]
  refine ⟨hp.callPre (by rw [x0₂, g₁ _ (by decide), h.x19]) (by rw [x1₂, g₁ _ (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide), h.x24]) x3₂ (by rw [x4₂, g₁ _ (by decide), h.x24])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]), keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨S s₀, 2064⟩] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => hq s₂ ?_)
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r hr h30 => by rw [c.saved r hr h30, a.saved r hr], by rw [c.sp, a.sp], by rw [c.rd, a.rd],
    by rw [c.wr, a.wr], (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · rw [← headD_bytesAt s₂.mem (Sv s₀), c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copyMem_bytes _ hp.iv_sv.symm, h.iv]

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `x9`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → s₃.gpr r = s₂.gpr r) (sp₃ : s₃.sp = s₂.sp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : s₃.gpr .x9 = (if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)).setWidth 64) :
    WP isa (.block (shift ++ Impl.AesCfb8.AArch64.advance)) s₃ (LInv enc s₀ (k + 1)) := by
  have g₃' (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (preserved_ne hr).1 (preserved_ne hr).2, a.g r hr h30]
  have rl : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, a.rd, a.wr, h.regs hp]
  have wl : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wrs hp]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    shift_ok s₃ (Q := Iv s₀) (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21]) hc
      (by rw [rl]; exact in_rw (by simp) cIv0) (by rw [rl]; exact in_rw (by simp) cIv8)
      (by rw [wl]; exact in_rw (by simp) cIv0) (by rw [wl]; exact in_rw (by simp) cIv8)
  obtain ⟨s₅, run₅, x22₅, x23₅, keep₅, sp₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x22 (by simp [preserved]) (by decide),
      h.x22])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x23 (by simp [preserved]) (by decide),
      h.x23])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₅.gpr r = s.gpr r := by
    have hne : r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [keep₅ r h22 h23, g₄ r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2, g₃' r hr h30]
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMemX_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have newByte : s₅.mem (byt s₀ k) = v := by
    rw [mem₅, mem₄, byte_frame (AesCfb8.shiftMemX_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃, writeW8_self]
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = inKk s₀ enc k := by
    rw [mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (one _ _ _ (hp.iv_scr.sub_right (Region.sub_prefix (by decide))))
        (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨?_, ?_, ?_, x22₅, x23₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20]
  · rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21]
  · rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24]
  · intro r hr h19 h20 h21 h22 h23 h24 h30
    rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]
  · rw [sp₅, sp₄, sp₃, a.sp, h.sp]
  · rw [rd₅, rd₄, rd₃, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₅, mem₄, AesCfb8.shiftMemX_bytes, ivIn]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

/-- The data byte after the call. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.byt_sv hk), h.byte hk]

theorem AfterCall.args {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.gpr .x22 = byt s₀ k ∧ s₂.gpr .x24 + BitVec.ofNat 64 2048 = Sv s₀ ∧
      InRegions (s₂.rd ++ s₂.wr) (byt s₀ k) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (Sv s₀) 1 ∧
      InRegions s₂.wr (byt s₀ k) 1 := by
  have rl : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  refine ⟨by rw [a.g .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [a.g .x24 (by simp [preserved]) (by decide), h.x24], ?_, ?_, ?_⟩
  · rw [rl]; exact in_rw (by simp) (hp.cByt hk)
  · rw [rl]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  · rw [a.wr, h.wrs hp]; exact in_rw (by simp) (hp.cByt hk)

theorem encBody_ok (v : BlocksImpl) : BodyOk true (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, x9₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := encByte_ok s₂ eP eT rP rT wP
  rw [encPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [x9₃]; rfl

theorem decBody_ok (v : BlocksImpl) : BodyOk false (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, x9₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := decByte_ok s₂ eP eT rP rT wP
  rw [decPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [x9₃, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.AArch64

end

end

/-!
# AES-CFB8 on AArch64: constant time

AES-CBC's argument (`Proof/AesCbc/AArch64/CT.lean`) for the CFB8 loop: two
runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`),
and each call of a block function is constant time by its own proof
(`blk_rel`). `whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.Impl.AesCbc.AArch64 VG.Impl.AesCfb8.AArch64
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S Sv CallPre CallPost blk_call blk_rel eval_x23 eval_zero_x23)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cfb8AArch64 enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_x1 : s₀.gpr .x1 = s₀'.gpr .x1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_x1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_byt (k : Nat) : byt s₀ k = byt s₀' k := by rw [byt, byt, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) s₁ s₂ := by
  refine agree_of (by rw [h₁.sp, h₂.sp, pub_sp hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, pub_W hq]
  · rw [h₁.x20, h₂.x20, pub_x1 hq]
  · rw [h₁.x21, h₂.x21, pub_Iv hq]
  · rw [h₁.x22, h₂.x22, pub_byt hq]
  · rw [h₁.x23, h₂.x23, pub_N hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

end

/-- One run of `body` from `k` bytes is constant time. -/
def BodyCt (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (cfb8AArch64 enc).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) body fun _ _ => True

/-! ## One byte -/

/-- What is known between the code before the call and the call, on the
block at `D`. -/
structure Mid (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre s (W s₀) D (S s₀) (R s₀)
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = byt s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = byt s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {s₀ : State} {k : Nat} {D : Addr} {s s₁ : State} {enc : Bool} (h : LInv enc s₀ k s)
    (pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)) (saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r)
    (sp : s₁.sp = s.sp) : Mid s₀ k D s₁ :=
  ⟨pre, by rw [saved .x21 (by simp [preserved]), h.x21], by rw [saved .x22 (by simp [preserved]), h.x22],
    by rw [saved .x23 (by simp [preserved]), h.x23], by rw [saved .x24 (by simp [preserved]), h.x24],
    by rw [sp, h.sp]⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {D : Addr}
    {s s' : State} (h : Mid s₀ k D s) (hc : CallPost f s (W s₀) D (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .x21 (by simp [preserved]) (by decide), h.x21],
    by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.x23],
    by rw [hc.saved .x24 (by simp [preserved]) (by decide), h.x24], by rw [hc.sp, h.sp]⟩

/-- A body: code before the call (`pre`), the call of `b` on the block at
`D s₀ k` (public), and code after it (`post`), constant time when `pre`'s
addresses and branches depend only on the registers the invariant pins and
`post`'s on `x21` to `x24`. -/
theorem body_ct {enc : Bool} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (cfb8AArch64 enc).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    {b : Impl.Aes.AArch64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
      WP isa (.block pre) s (Mid s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8AArch64 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint)
    (P := fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := Mid s₀ k (D s₀ k)) (F₂ := Mid s₀' k (D s₀' k)) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel ok ct (P := fun s₁ s₂ => Mid s₀ k (D s₀ k) s₁ ∧ Mid s₀' k (D s₀' k) s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call ok nf h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call ok nf h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x21, h.2.x21, pub_Iv hq]
      · rw [h.1.x22, h.2.x22, pub_byt hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]
      · rw [h.1.x24, h.2.x24, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block pre) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem pub_Sv {enc : Bool} {s₀ s₀' : State} (hq : (cfb8AArch64 enc).pub s₀ s₀') : Sv s₀ = Sv s₀' := by
  rw [Sv, Sv, pub_S hq]

theorem encBody_ct (v : BlocksImpl) : BodyCt true (body v.enc encPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNoFrames
    pre_taint encPost_taint
    (@fun _ hp _ _ _ h => WP.mono (pre_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt false (body v.enc decPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNoFrames
    pre_taint decPost_taint
    (@fun _ hp _ _ _ h => WP.mono (pre_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂

theorem loop_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8AArch64 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop body (.nonzero .x .x23))
      fun s₁ s₂ => LInv enc s₀ (N s₀) s₁ ∧ LInv enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp
    (F₁ := LInv enc s₀ (k + 1)) (F₂ := LInv enc s₀' (k + 1))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have hbd : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have e₁ := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hbd]) l₁.x23
  have e₂ := eval_x23 (x := N s₀ - (k + 1)) (by omega_using [hbd]) (by rw [l₂.x23, ← hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

/-! ## The whole function -/

theorem whole_rel {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (h0 : (cfb8AArch64 enc).pre s₀) (h0' : (cfb8AArch64 enc).pre s₀')
    (hq : (cfb8AArch64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have hbd : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      refine agree_of h7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := LInv enc s₀ 0) (F₂ := LInv enc s₀' 0)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {s : State} (h : LInv enc s₀ 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hbd (by rw [h.x23]; rfl)
  have ev' {s : State} (h : LInv enc s₀' 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hbd (by rw [h.x23, ← hN]; rfl)
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b) ∧ isa.eval (.zero .x .x23) a = some true) _
    (fun a b h => agree_of (by rw [h.1.1.sp, h.1.2.sp, pub_sp hq]) fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b)
      (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23)))
      (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev' h.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1, h.1.2⟩)
        fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x24, h.2.x24, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body) :
    ConstantTime isa (cfb8AArch64 enc).pre (cfb8AArch64 enc).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCfb8.AArch64

end

end

/-!
# AES-CFB8 on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), AES-CBC's state satisfying the precondition, and the shared
contracts of `Spec/Cfb8/Contract.lean` (with no
stack: the calls keep the return address in `x30`, which each function
saves in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.Impl.AesCfb8.AArch64
open VG.Impl.AesCbc.AArch64 (whole)
open VG.Proof.AesCbc.AArch64 (sat)
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.enc).allInstrs keepsV = true := by
  simp only [decrypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8AArch64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8AArch64 true).post s s' :=
  WP.withPreservedV (whole_wp (encBody_ok v) hs) (encrypt_keepsV v)

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (cfb8AArch64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (cfb8AArch64 false).post s s' :=
  WP.withPreservedV (whole_wp (decBody_ok v) hs) (decrypt_keepsV v)

theorem encrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (encrypt v.enc) (Proof.AesCfb8.encryptRoundsContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (whole_ct (encBody_ok v) (encBody_ct v)) (by
    sig_implies [Proof.AesCfb8.encryptRoundsContract, Spec.Cfb8.aesSig, cfb8AArch64, cfb8, cts, inK,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem decrypt_verified (v : BlocksImpl) :
    Verified AArch64.target (decrypt v.enc) (Proof.AesCfb8.decryptRoundsContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v) (whole_ct (decBody_ok v) (decBody_ct v)) (by
    sig_implies [Proof.AesCfb8.decryptRoundsContract, Spec.Cfb8.aesSig, cfb8AArch64, cfb8, cts, inK,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

/-! ## The functions, as emitted

`vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt` with their cleanup
(`Impl.AesCfb8.AArch64.Fn`), around an implementation `v` of the block
functions: each meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds.
What the cleanup needs of the code (`ScrubAll.scrubSide`) is proved of each
function's own instructions here, once, with code that does nothing in the
place of the block function, and of each implementation where it is defined
(`BlocksImpl.encScrub`). -/

private theorem encrypt_all {p : AArch64.Instr → Bool} (b : Impl.Aes.AArch64.Blocks)
    (h0 : AArch64.ScrubAll.sideAll p (Impl.AesCfb8.AArch64.encrypt ⟨"", .block []⟩) = true)
    (hc : AArch64.ScrubAll.sideAll p b.code = true) :
    AArch64.ScrubAll.sideAll p (Impl.AesCfb8.AArch64.encrypt b) = true := by
  simp only [Impl.AesCfb8.AArch64.encrypt, Impl.AesCfb8.AArch64.body, Impl.AesCbc.AArch64.whole, AArch64.ScrubAll.sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem encrypt_own :
    AArch64.ScrubAll.calleeSide (Impl.AesCfb8.AArch64.encrypt ⟨"", .block []⟩) Impl.AesCfb8.AArch64.Fn.own = true := by
  kernel_rfl

theorem encrypt_side (v : Proof.Aes.AArch64.BlocksImpl) :
    AArch64.ScrubAll.scrubSide (Impl.AesCfb8.AArch64.encrypt v.enc) 0 0 (Impl.AesCfb8.AArch64.Fn.own.union v.encClear) [] = true := by
  refine AArch64.ScrubAll.scrubSide_union0 ?_ (by decide)
    (encrypt_all v.enc (AArch64.ScrubAll.sideAll_union_left encrypt_own)
      (AArch64.ScrubAll.sideAll_union_right v.encScrub)) (by decide)
  simp only [Impl.AesCfb8.AArch64.encrypt, Impl.AesCfb8.AArch64.body, Impl.AesCbc.AArch64.whole, Code.aarch64Depth, Proof.Aes.AArch64.depth_of_noFrames v.encNoFrames]
  decide

/-- `vg_aes_cfb8_encrypt` as emitted, cleanup included. -/
theorem encrypt_scrubbed (v : Proof.Aes.AArch64.BlocksImpl) :
    VerifiedScrubbed AArch64.target (Impl.AesCfb8.AArch64.Fn.encrypt v.encClear v.enc)
      (Spec.Cfb8.aesEncryptContract AArch64.abi 0) 0 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Cfb8.aesEncryptApi)
    { code := Impl.AesCfb8.AArch64.encrypt v.enc, verified := Proof.AesCfb8.encrypt_keyed (encrypt_verified v) } _
    Proof.Aes.AArch64.ModesScrub.cfb8EncryptOk (encrypt_side v)

private theorem decrypt_all {p : AArch64.Instr → Bool} (b : Impl.Aes.AArch64.Blocks)
    (h0 : AArch64.ScrubAll.sideAll p (Impl.AesCfb8.AArch64.decrypt ⟨"", .block []⟩) = true)
    (hc : AArch64.ScrubAll.sideAll p b.code = true) :
    AArch64.ScrubAll.sideAll p (Impl.AesCfb8.AArch64.decrypt b) = true := by
  simp only [Impl.AesCfb8.AArch64.decrypt, Impl.AesCfb8.AArch64.body, Impl.AesCbc.AArch64.whole, AArch64.ScrubAll.sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem decrypt_own :
    AArch64.ScrubAll.calleeSide (Impl.AesCfb8.AArch64.decrypt ⟨"", .block []⟩) Impl.AesCfb8.AArch64.Fn.own = true := by
  kernel_rfl

theorem decrypt_side (v : Proof.Aes.AArch64.BlocksImpl) :
    AArch64.ScrubAll.scrubSide (Impl.AesCfb8.AArch64.decrypt v.enc) 0 0 (Impl.AesCfb8.AArch64.Fn.own.union v.encClear) [] = true := by
  refine AArch64.ScrubAll.scrubSide_union0 ?_ (by decide)
    (decrypt_all v.enc (AArch64.ScrubAll.sideAll_union_left decrypt_own)
      (AArch64.ScrubAll.sideAll_union_right v.encScrub)) (by decide)
  simp only [Impl.AesCfb8.AArch64.decrypt, Impl.AesCfb8.AArch64.body, Impl.AesCbc.AArch64.whole, Code.aarch64Depth, Proof.Aes.AArch64.depth_of_noFrames v.encNoFrames]
  decide

/-- `vg_aes_cfb8_decrypt` as emitted, cleanup included. -/
theorem decrypt_scrubbed (v : Proof.Aes.AArch64.BlocksImpl) :
    VerifiedScrubbed AArch64.target (Impl.AesCfb8.AArch64.Fn.decrypt v.encClear v.enc)
      (Spec.Cfb8.aesDecryptContract AArch64.abi 0) 0 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.Cfb8.aesDecryptApi)
    { code := Impl.AesCfb8.AArch64.decrypt v.enc, verified := Proof.AesCfb8.decrypt_keyed (decrypt_verified v) } _
    Proof.Aes.AArch64.ModesScrub.cfb8DecryptOk (decrypt_side v)

end VG.Proof.AesCfb8.AArch64
