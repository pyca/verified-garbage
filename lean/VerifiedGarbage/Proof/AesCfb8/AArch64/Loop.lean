import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Impl.AesCfb8.AArch64

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
  Offset.sub_base _ (by omega)

theorem UPre.byt_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
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
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega), hl, Nat.sub_self,
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
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine ⟨s', run, ?_, ?_, keep, sp', mem', rd', wr'⟩
  · rw [x22', h22, Offset.add_add_eq _ (c := k + 1) (by omega)]
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
  have ev := eval_x23 (x := N s₀ - (k + 1)) (by omega) h'.x23
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv enc s₀ 0) := by
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x24₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
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
    Proof.Cmac.bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega)
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
    exact loop_ok hb hp (by omega) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩], (⟨S s₀ + BitVec.ofNat 64 2064, 56⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

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
      exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
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
