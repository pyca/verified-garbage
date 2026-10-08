import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
import VerifiedGarbage.Impl.AesCfb8.X86_64

/-!
# AES-CFB8 on x86-64: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8X86_64 enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/X86_64/Loop.lean`), whose stride-free lemmas this reuses.

The invariant after `k` bytes (`LInv`): the registers hold the arguments
(`r13` the next byte, `r14` the bytes left), only the input block, the
data, the first 2064 bytes of the scratch buffer and the stack below the
return address have changed since the registers were saved, the first `k`
bytes are CFB8's of the first `k` bytes on entry and the rest are
unchanged, and the input block is the one after them.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

namespace VG.Proof.AesCfb8.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Proof.AesCbc.X86_64 (wK W R Iv Dp N S schR ivR scrR stkR iv0 savedMem in_rw savedMem_frame
  saved_bound slot_contains prologue_ok rsi_ofNat r8_ofNat beq_zero)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, len = r8, scratch = r9)`. -/
def cfb8X86_64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧ ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .rdx) 16
    let xs := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .rdx) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

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
  ret_iv : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (ivR s₀)
  ret_data : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (dataR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_iv : (stkR s₀).Disjoint (ivR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8X86_64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = byt s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
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
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine AesCbc.X86_64.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-- The bytes after a step that changed only byte `k`, the input block, the
first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] m m') :
    bytesAt m' (Dp s₀) (N s₀) = (bytesAt m (Dp s₀) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := AesCbc.X86_64.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hj)

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
    ∃ s', runBlock isa Impl.AesCfb8.X86_64.advance s = some s' ∧
      s'.gpr .r13 = s.gpr .r13 + BitVec.ofNat 64 1 ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some ((s.gpr .r14 - 1) == 0) ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, Impl.AesCfb8.X86_64.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, gpr_setReg,
      gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What `advance` leaves after byte `k`: the registers of byte `k + 1`, and
ZF set if it was the last. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State}
    (h13 : s.gpr .r13 = byt s₀ k) (h14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa Impl.AesCfb8.X86_64.advance s = some s' ∧ s'.gpr .r13 = byt s₀ (k + 1) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + 1)) ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, r13', r14', zf', keep, mem', rd', wr'⟩ := advance_ok s
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine ⟨s', run, ?_, ?_, ?_, keep, mem', rd', wr'⟩
  · rw [r13', h13, Offset.add_add_eq _ (c := k + 1) (by omega)]
  · rw [r14', h14, dec]
  · rw [zf', h14, dec, beq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN)]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
ZF if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv enc s₀ 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] → ∀ r' ∈ [⟨s₀.gpr .r9 + BitVec.ofNat 64 2064, 48⟩],
      r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    AesCbc.X86_64.bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : bytesAt (savedMem s₀) (Dp s₀) (N s₀) = bs s₀ :=
    AesCbc.X86_64.bytesAt_frame f₀ (disj _ (by simp)) (by simp only [N]; omega)
  have dat : outK s₀ enc 0 ++ (bs s₀).drop 0 = bs s₀ := by
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  have ivv : inKk s₀ enc 0 = iv0 s₀ := by
    simp only [inKk, List.take_zero, inK_nil]
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            data := by rw [mem₁, dataS, dat]
            iv := by rw [mem₁, ivS, ivv] }
  · rw [zf₁, r8_ofNat, beq_zero hN]

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀], (⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 8 ≤ 2112) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ (cfb8X86_64 enc).post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr saved := fun p hp' => by
    have := saved_bound p hp'
    rw [h₂.r15, slot_read hp h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_, ?_⟩
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  · rw [mem₃]
    refine (UPre.big_of h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show bytesAt s₃.mem (Dp s₀) (N s₀) = _
    rw [mem₃, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [mem₃, h₂.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8X86_64 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => gprPreserved s₀ s' ∧ (cfb8X86_64 enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.X86_64
