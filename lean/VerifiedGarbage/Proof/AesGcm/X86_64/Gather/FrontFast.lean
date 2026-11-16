module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitPath
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCT
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCall
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-! ### `AesGcm.X86_64.Gather.Front`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the test of a TLS record's text

Untrusted: everything here is checked by Lean. What `frontTest long`
computes from the public arguments of the entry state (`frontGo`), in one
run (`frontTest_wp`) and in two runs with the same public arguments
(`frontTest_rel`, which take the same path: `Pub.eFront`), leaving the
entry state but for `rax`, `r10`, `r11` and the flags (`Same`). The test
only chooses between paths that are correct for any text, so `frontGo` is
what the code computes, not a statement of it; what the path it chooses
needs follows from it (`front_facts`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.AesGcm.X86_64 (rel_block_split)

/-- A `cmov`'s state, with the write folded into the register's value. -/
theorem ite_setReg (c : Prop) [Decidable c] (s : State) (r : Reg) (v : BitVec 64) :
    (if c then s.setReg r v else s) = s.setReg r (if c then v else s.gpr r) := by
  by_cases h : c <;> simp [h, setReg_self]

/-! ## What the test computes -/

/-- `r11` after `frontArgs`, from the nonce's length `n`, the additional
data's `al` and the slices' `c`. -/
def fA (n al c : BitVec 64) : BitVec 64 :=
  if (!decide ((c - 1#64).toNat < (2#64).toNat)) = true then c - 1#64
  else if (!decide (al.toNat < (17#64).toNat)) = true then al else n - 12#64

/-- `r11` after `frontSlice long`, from `r11` before it (`acc`), the
first slice's length `a` and the text's `len`. -/
def fB (long : Bool) (acc a len : BitVec 64) : BitVec 64 :=
  let x := a >>> 4 <<< 4 + 16#64
  let b₁ := acc ||| if (!decide (x.toNat < len.toNat)) = true then acc else x
  b₁ ||| if (!decide (a.toNat < (256#64).toNat)) = true then b₁
    else (if long = true then len ||| BitVec.signExtend 64 (BitVec.ofNat 32 256) else len) >>> 8

/-- `r11` after the tests of `frontCore`. -/
def fR11 (long : Bool) (s : State) : BitVec 64 :=
  if (stackArg s 1 - 1#64).toNat < (2#64).toNat then
    fB long (fA (s.gpr .rcx) (AL s) (stackArg s 1)) (BitVec.ofNat 64 (fl s)) (stackArg s 3)
  else fA (s.gpr .rcx) (AL s) (stackArg s 1)

/-- Whether `frontTest long` takes the path of a TLS record's text. -/
def frontGo (long : Bool) (s : State) : Bool :=
  if long = true ∧ (stackArg s 3).toNat < (256#64).toNat then false
  else (fR11 long s &&& fR11 long s) == 0

theorem Pub.eFront {s₀ s₀' : State} (pb : Pub s₀ s₀') (long : Bool) :
    frontGo long s₀' = frontGo long s₀ := by
  simp only [frontGo, fR11, AL, pb.rcx, pb.r9, pb.a 1 (by decide), pb.a 3 (by decide), pb.eFl]

/-! ## In one run -/

/-- `Same` through code that writes only `rax`, `r10`, `r11` and the flags. -/
theorem Same.step {s st st' : State} (hs : Same s st)
    (g : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → st'.gpr r = st.gpr r) (hm : st'.mem = st.mem)
    (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) (hmx : st'.mxcsr = st.mxcsr := by rfl) : Same s st' :=
  ⟨fun r a b c => (g r a b c).trans (hs.gpr r a b c), hm.trans hs.mem, hrd.trans hs.rd, hwr.trans hs.wr,
    hmx.trans hs.mx⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

omit hp in
theorem same_rsp {st : State} (hs : Same s st) : st.gpr .rsp = s.gpr .rsp := hs.gpr _ (by decide) (by decide) (by decide)

/-- Stack argument `i`, from a state `Same` as the entry. -/
theorem same_a {st : State} (hs : Same s st) {i : Nat} (hi : i < 6) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := by
  rw [hs.rd, hs.wr, hs.mem, same_rsp hs]; exact ⟨a_in hp hi, rfl⟩

/-- The text's length: `CF` if it is shorter than 256 bytes. -/
theorem fLen_ok {st : State} (hs : Same s st) :
    WP isa (.block (frontLen 256)) st fun st' => Same s st' ∧
      st'.cf = some (decide ((stackArg s 3).toNat < (256#64).toNat)) ∧
      st'.zf = some (stackArg s 3 - 256#64 == 0) := by
  obtain ⟨a₃, e₃⟩ := same_a hp hs (i := 3) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [frontLen]; xrun [a₃, e₃], ?_, ?_, ?_⟩
  · exact hs.step (fun r a _ _ => by simp [gpr_setReg, gpr_arithFlags, a]) (by simp [mem_arithFlags, mem_setReg])
      (by simp [rd_arithFlags, rd_setReg]) (by simp [wr_arithFlags, wr_setReg])
  · simp only [cf_arithFlags]
  · simp only [zf_arithFlags]

/-- The nonce's and the additional data's lengths and the slices. -/
theorem fArgs_ok {st : State} (hs : Same s st) :
    WP isa (.block frontArgs) st fun st' => Same s st' ∧
      st'.cf = some (decide ((stackArg s 1 - 1#64).toNat < (2#64).toNat)) ∧
      st'.gpr .r11 = fA (s.gpr .rcx) (AL s) (stackArg s 1) := by
  obtain ⟨a₁, e₁⟩ := same_a hp hs (i := 1) (by decide)
  have gcx : st.gpr .rcx = s.gpr .rcx := hs.gpr _ (by decide) (by decide) (by decide)
  have g9 : st.gpr .r9 = s.gpr .r9 := hs.gpr _ (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [frontArgs]; xrun [a₁, e₁, gcx, g9, execCmov, eval, Option.map_some, ite_setReg], ?_, ?_, ?_⟩
  · exact hs.step (fun r a _ c => by simp [gpr_setReg, gpr_arithFlags, a, c])
      (by simp [mem_arithFlags, mem_setReg]) (by simp [rd_arithFlags, rd_setReg]) (by simp [wr_arithFlags, wr_setReg])
  · simp only [cf_arithFlags, cf_setReg]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, ite_true]; rfl

/-- The first slice's length, with one or two slices. -/
theorem fSlice_ok (long : Bool) (hc : Cnt s ≠ 0) {st : State} (hs : Same s st) :
    WP isa (.block (frontSlice long)) st fun st' => Same s st' ∧
      st'.gpr .r11 = fB long (st.gpr .r11) (BitVec.ofNat 64 (fl s)) (stackArg s 3) := by
  obtain ⟨a₀, e₀⟩ := same_a hp hs (i := 0) (by decide)
  obtain ⟨a₃, e₃⟩ := same_a hp hs (i := 3) (by decide)
  have d₈ : InRegions (st.rd ++ st.wr) (Src s + BitVec.ofNat 64 8) 8 := by
    rw [hs.rd, hs.wr, hp.rd]
    exact ⟨dsR s, by simp, Offset.contains_base _ (by omega_arith) (by have := hp.w_ds; omega_arith)⟩
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp (m := st.mem) (by rw [hs.mem]; exact Frame.refl _ _) (i := 0) (by omega_arith)
    rw [show Src s + BitVec.ofNat 64 (16 * 0) = Src s by simp] at this
    rw [this, fl_eq]; simp [hc]
  cases long <;>
  · apply WP.of_runBlock
    refine ⟨_, by
      simp only [frontSlice, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
      xrun [a₀, e₀, a₃, e₃, d₈, v₈, execCmov, eval, Option.map_some, ite_setReg], ?_, ?_⟩
    · exact hs.step (fun r a b c => by simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c])
        (by simp [mem_arithFlags, mem_setReg, mem_setFlags]) (by simp [rd_arithFlags, rd_setReg, rd_setFlags])
        (by simp [wr_arithFlags, wr_setReg, wr_setFlags])
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ↓reduceIte, ite_true]; rfl

omit hp in
/-- `ZF` if `r11` is 0. -/
theorem fZero_ok {st : State} (hs : Same s st) :
    WP isa (.block [.alu .test .r11 (.reg .r11)]) st fun st' => Same s st' ∧
      st'.zf = some ((st.gpr .r11 &&& st.gpr .r11) == 0) := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_, ?_⟩
  · exact hs.step (fun r _ _ _ => by simp [gpr_setFlags, gpr_arithFlags]) (by simp [mem_arithFlags, mem_setFlags])
      (by simp [rd_arithFlags, rd_setFlags]) (by simp [wr_arithFlags, wr_setFlags])
  · simp [zf_arithFlags]

omit hp in
/-- With one or two slices, there is a first. -/
theorem cnt_ne_of {s : State} (h : (stackArg s 1 - 1#64).toNat < (2#64).toNat) : Cnt s ≠ 0 := by
  intro hc
  have : stackArg s 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hc)
  rw [this] at h; simp at h

/-- The nonce's and the additional data's lengths and the slices, then the
first slice if there are one or two: `r11`. -/
theorem fMid_wp (long : Bool) {st : State} (hs : Same s st) (hc : st.cf = some (decide ((stackArg s 1 - 1#64).toNat < (2#64).toNat)))
    (h11 : st.gpr .r11 = fA (s.gpr .rcx) (AL s) (stackArg s 1)) :
    WP isa (.ite .ae (.block []) (.block (frontSlice long))) st fun t => Same s t ∧
      t.gpr .r11 = fR11 long s := by
  refine WP.ite (!decide ((stackArg s 1 - 1#64).toNat < (2#64).toNat)) (by simp only [eval, hc, Option.map_some])
    (fun e => WP.block_nil ⟨hs, ?_⟩) (fun e => ?_)
  · have hc : ¬(stackArg s 1 - 1#64).toNat < (2#64).toNat := by simpa using e
    rw [h11]; simp only [fR11, hc, ↓reduceIte]
  · have hc : (stackArg s 1 - 1#64).toNat < (2#64).toNat := by simpa using e
    refine WP.mono (fSlice_ok hp long (cnt_ne_of hc) hs) fun t ⟨S, r11⟩ => ⟨S, ?_⟩
    rw [r11, h11]; simp only [fR11, hc, ↓reduceIte]

/-- The tests of `frontCore`, from a state `Same` as the entry. -/
theorem frontCore_wp (long : Bool) {st : State} (hs : Same s st) :
    WP isa (frontCore long) st fun st' => Same s st' ∧
      st'.zf = some ((fR11 long s &&& fR11 long s) == 0) := by
  unfold frontCore
  exact WP.seq (WP.mono (fArgs_ok hp hs) fun s₂ ⟨S₂, cf₂, r11₂⟩ =>
    WP.seq (WP.mono (fMid_wp hp long S₂ cf₂ r11₂)
      fun s₃ ⟨S₃, r11₃⟩ => WP.mono (fZero_ok S₃) fun s₄ ⟨S₄, zf₄⟩ => ⟨S₄, by rw [zf₄, r11₃]⟩))

/-- The test of a TLS record's text, from the entry. -/
theorem frontTest_wp (long : Bool) :
    WP isa (frontTest long) s fun st' => Same s st' ∧ st'.zf = some (frontGo long s) := by
  cases long
  · simp only [frontTest, Bool.false_eq_true, ↓reduceIte]
    exact WP.mono (frontCore_wp hp false (Same.refl s)) fun st ⟨S, zf⟩ => ⟨S, by simpa [frontGo] using zf⟩
  simp only [frontTest, ↓reduceIte]
  refine WP.seq (WP.mono (fLen_ok hp (Same.refl s)) fun s₁ ⟨S₁, cf₁, zf₁⟩ => ?_)
  refine WP.ite (decide ((stackArg s 3).toNat < (256#64).toNat))
    (by simp only [eval, cf₁]) (fun e => WP.block_nil ⟨S₁, ?_⟩) (fun e => ?_)
  · have hl : (stackArg s 3).toNat < (256#64).toNat := by simpa using e
    rw [zf₁]
    simp only [frontGo, hl, and_self, ↓reduceIte, Option.some.injEq, beq_eq_false_iff_ne, ne_eq]
    generalize (256#64 : BitVec 64) = y at hl ⊢
    intro h0
    bv_omega
  have hl : ¬(stackArg s 3).toNat < (256#64).toNat := by simpa using e
  exact WP.mono (frontCore_wp hp true S₁) fun st ⟨S, zf⟩ => ⟨S, by rw [zf]; simp only [frontGo, hl, and_false, ↓reduceIte]⟩

/-- What the path of a TLS record's text needs: a 12-byte nonce, one or two
slices, and at most 16 bytes of text after the first. -/
theorem front_facts {long : Bool} (h : frontGo long s = true) :
    s.gpr .rcx = 12#64 ∧ (Cnt s = 1 ∨ Cnt s = 2) ∧ L s - fl s ≤ 16 := by
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have z : ∀ x : BitVec 64, ((x &&& x) == 0) = true → x = 0#64 := fun x hx => by simpa using hx
  unfold frontGo at h
  split at h
  · exact absurd h (by decide)
  have h0 := z _ h
  unfold fR11 at h0
  split at h0
  · next hc =>
    have hc0 := cnt_ne_of hc
    unfold fB at h0
    simp only [BitVec.or_eq_zero_iff] at h0
    obtain ⟨⟨hA, hx⟩, -⟩ := h0
    unfold fA at hA
    simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hA
    split at hA
    · next ha => simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt] at ha
                 rw [hA] at ha; simp at ha
    have hn : s.gpr .rcx = 12#64 := by bv_omega
    have hcnt : Cnt s = 1 ∨ Cnt s = 2 := by
      have : (stackArg s 1).toNat ≠ 0 := hc0
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)] at hc
      simp at hc
      show (stackArg s 1).toNat = 1 ∨ (stackArg s 1).toNat = 2
      omega_arith
    refine ⟨hn, hcnt, ?_⟩
    rw [round16 (by omega_arith)] at hx
    have hx16 : (BitVec.ofNat 64 (16 * (fl s / 16)) + 16#64).toNat = (16 * (fl s / 16) + 16) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (fl s / 16)) (by omega_arith)]; rfl
    have hL3 : (stackArg s 3).toNat = L s := rfl
    split at hx
    · next hn' =>
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt, hx16, hL3] at hn'
      by_cases hw : 16 * (fl s / 16) + 16 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hw] at hn'; omega_arith
      · omega_arith
    · have := congrArg BitVec.toNat hx
      rw [hx16] at this
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      omega_arith
  · next hc =>
    unfold fA at h0
    simp only [hc, decide_false, Bool.not_false, ↓reduceIte] at h0
    rw [h0] at hc; simp at hc

end

end VG.Proof.AesGcm.X86_64.Gather

end

end


/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: a TLS record's text from the entry

Untrusted: everything here is checked by Lean. The path `frontFast` of a
text `frontTest` passes (a 12-byte nonce, one or two slices, at most 16
bytes after the first: `front_facts`), from a state `Same` as the entry:
`ctx` and `rounds` kept in `work` (`fastEntry_ok`), the second slice, if
any, copied to the output after the first, one byte at a time
(`fastCopy_wp`), and the call of `vg_aes_gcm_seal_split` from the first
slice where it is (`frontFast_wp`), by the proofs of `copySplit`'s
(`splitCall_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64 (length_bytesAt bytesAt_frame sub_beq imm_eq)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (ofNat_beq_zero)

/-- The fast path's state between its blocks: the stack, the callee-saved
registers, the regions and the arguments of `vg_aes_gcm_seal_split` in
registers as on entry, the memory as on entry but where the code writes, and
`ctx` and `rounds` in `work`. -/
structure FBase (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctx : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s
  rounds : st.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  rdx : st.gpr .rdx = Nn s
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s
  mx : st.mxcsr = s.mxcsr

/-- `FBase` through code that changes no memory and writes none of its
registers. -/
theorem FBase.regs {s st st' : State} (h : FBase s st) (hm : st'.mem = st.mem)
    (g : ∀ r, r ∈ calleeSaved ∨ r = .rdx ∨ r = .r8 ∨ r = .r9 → st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd)
    (hwr : st'.wr = st.wr) (hmx : st'.mxcsr = st.mxcsr := by rfl) : FBase s st' :=
  ⟨by rw [g _ (Or.inl (by decide)), h.rsp], fun r hr => by rw [g r (Or.inl hr), h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, hm ▸ h.frame, hm ▸ h.ctx, hm ▸ h.rounds, by rw [g _ (by simp), h.rdx],
    by rw [g _ (by simp), h.r8], by rw [g _ (by simp), h.r9], hmx.trans h.mx⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- `ctx` and `rounds` kept, the first descriptor in `r10`, and `ZF` if there
is one slice. -/
theorem fastEntry_ok {st : State} (hs : Same s st) :
    WP isa (.block fastEntry) st fun s₁ => FBase s s₁ ∧ s₁.gpr .r10 = Src s ∧
      s₁.zf = some (decide (Cnt s = 1)) := by
  have sp := same_rsp hs
  obtain ⟨a₀, e₀⟩ := same_a hp hs (i := 0) (by decide)
  obtain ⟨a₁, e₁⟩ := same_a hp hs (i := 1) (by decide)
  obtain ⟨a₅, e₅⟩ := same_a hp hs (i := 5) (by decide)
  have w : ∀ d, d + 8 ≤ 104 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => by
    rw [hs.wr]; exact w_in hp (by omega_arith)
  have gdi : st.gpr .rdi = K s := hs.gpr _ (by decide) (by decide) (by decide)
  have gsi : st.gpr .rsi = s.gpr .rsi := hs.gpr _ (by decide) (by decide) (by decide)
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hz : ((stackArg s 1 - BitVec.ofNat 64 1) == 0) = decide (Cnt s = 1) := by
    rw [← ofNat_toNat (stackArg s 1)]
    exact sub_beq (by omega_arith) (by decide)
  have i1 := imm_eq (n := 1) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [fastEntry, gCtx, gRounds]
    xrun [a₀, e₀, a₁, e₁, a₅, e₅, w 0 (by decide), w 8 (by decide), gdi, gsi, i1], ?_, ?_, ?_⟩
  · refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.mx⟩
    · simp [gpr_setReg, gpr_arithFlags, sp]
    · have a : r ≠ .rax := by intro e; subst e; simp [calleeSaved] at hr
      have b : r ≠ .r10 := by intro e; subst e; simp [calleeSaved] at hr
      have c : r ≠ .r11 := by intro e; subst e; simp [calleeSaved] at hr
      simp [gpr_setReg, gpr_arithFlags, a, b, c]; exact hs.gpr r a b c
    · simp [rd_setReg, rd_arithFlags, hs.rd]
    · simp [wr_setReg, wr_arithFlags, hs.wr]
    · have c : ∀ d, d + 8 ≤ 104 → (kpR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
        fun d h₂ => Offset.contains_base _ h₂ (by omega_arith)
      simp only [mem_setReg, mem_arithFlags]
      rw [← hs.mem]
      exact frame_kpR (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (c 8 (by decide)))
    all_goals simp (disch := decide) only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, reduceCtorEq,
      ↓reduceIte, Mem.readW_writeW_self64, readW_writeW_off]
    · exact hs.gpr _ (by decide) (by decide) (by decide)
    · exact hs.gpr _ (by decide) (by decide) (by decide)
    · exact hs.gpr _ (by decide) (by decide) (by decide)
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags]
    rw [hz]

/-- The descriptors' bytes from `j` to `j + 8`, in a state of the path. -/
theorem desc_in' {st : State} (h : FBase s st) {j : Nat} (hj : j + 8 ≤ Cnt s * 16) :
    InRegions (st.rd ++ st.wr) (Src s + BitVec.ofNat 64 j) 8 := by
  rw [h.rd, h.wr, hp.rd]
  exact ⟨dsR s, by simp, Offset.contains_base _ hj (by have := hp.w_ds; omega_arith)⟩

/-- Stack argument `i`, in a state of the path. -/
theorem fa_in {st : State} (h : FBase s st) {i : Nat} (hi : i < 6) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := by
  rw [h.rd, h.wr, h.rsp]; exact ⟨a_in hp hi, keep_a hp h.frame hi⟩

/-- The second slice's length into `rcx`, `ZF` if it is empty. -/
theorem fastLen2_ok (hc : Cnt s = 2) {st : State} (h : FBase s st) (h10 : st.gpr .r10 = Src s) :
    WP isa (.block fastLen2) st fun s₂ => FBase s s₂ ∧ s₂.gpr .r10 = Src s ∧
      s₂.gpr .rcx = BitVec.ofNat 64 (sl s 1) ∧ s₂.zf = some (decide (sl s 1 = 0)) := by
  have d₂₄ := desc_in' hp h (j := 24) (by omega_arith)
  have v₂₄ : st.mem.readW (Src s + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (sl s 1) := by
    rw [← sl_eq hp h.frame (i := 1) (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]
  have hl : sl s 1 < 2 ^ 64 := BitVec.isLt _
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastLen2]; xrun [h10, d₂₄, v₂₄], ?_, ?_, ?_, ?_⟩
  · exact h.regs (by simp [mem_setReg, mem_arithFlags]) (fun r hr => by
      have : r ≠ .rcx := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      simp [gpr_setReg, gpr_arithFlags, this]) (by simp [rd_setReg, rd_arithFlags]) (by simp [wr_setReg, wr_arithFlags])
  · simp [gpr_setReg, gpr_arithFlags, h10]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ↓reduceIte, BitVec.and_self]
    rw [ofNat_beq_zero hl]

/-- The copy's registers: the second slice, the output after the first, and
an index of 0. -/
theorem fastCopy_ok (hc : Cnt s = 2) (hlt : sl s 1 < 2 ^ 63) {st : State} (h : FBase s st)
    (h10 : st.gpr .r10 = Src s) (hcx : st.gpr .rcx = BitVec.ofNat 64 (sl s 1)) :
    WP isa (.block fastCopy) st fun s₃ => FBase s s₃ ∧
      CopyPre s₃ (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) (sl s 1) ∧ s₃.gpr .r10 = BitVec.ofNat 64 0 := by
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain ⟨a₂, e₂⟩ := fa_in hp h (i := 2) (by decide)
  have d₁₆ := desc_in' hp h (j := 16) (by omega_arith)
  have d₈ := desc_in' hp h (j := 8) (by omega_arith)
  have v₁₆ : st.mem.readW (Src s + BitVec.ofNat 64 16) 64 = sb s 1 := sb_eq hp h.frame (i := 1) (by omega_arith)
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp h.frame (i := 0) (by omega_arith)
    rw [show Src s + BitVec.ofNat 64 (16 * 0) = Src s by simp] at this
    rw [this, fl_eq]; simp [hc]
  have hgl : fl s + sl s 1 = L s := by
    have := hp.glen
    rw [hc, show (2 : Nat) = 0 + 1 + 1 from rfl, gl_succ, gl_succ, gl_zero] at this
    rw [fl_eq]; simp [hc]; omega_arith
  have hsl : (⟨sb s 1, sl s 1⟩ : Region) ∈ lsR s := slice_mem s (i := 1) (by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastCopy]; xrun [h10, a₂, e₂, d₁₆, v₁₆, d₈, v₈], ?_, ?_, ?_⟩
  · exact h.regs (by simp [mem_setReg, mem_arithFlags]) (fun r hr => by
      have a : r ≠ .rsi := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      have b : r ≠ .rdi := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      have c : r ≠ .r10 := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      simp [gpr_setReg, gpr_arithFlags, a, b, c]) (by simp [rd_setReg, rd_arithFlags]) (by simp [wr_setReg, wr_arithFlags])
  · refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags],
      by simp [gpr_setReg, gpr_arithFlags, hcx], hlt, ?_, ?_, ?_⟩
    · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, h.rd, h.wr]
      exact Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hp.rd]; simp [hsl])
    · simp only [wr_setReg, wr_arithFlags, h.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨dR s, by simp, fl s, rfl, by simp only; omega_arith⟩
    · have := (hp.ls _ hsl).1
      exact this.sub_right (by have := dK_sub hp (s := s); rw [← hgl, Nat.add_sub_cancel_left] at this; exact this)
  · simp [gpr_setReg, gpr_arithFlags]

end

/-- The slices after the first, in the output after it. -/
def FOut (s st : State) : Prop :=
  bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- With two slices, the text is the first and the second. -/
theorem gl_two (hc : Cnt s = 2) : fl s + sl s 1 = L s := by
  have := hp.glen
  rw [hc, show (2 : Nat) = 0 + 1 + 1 from rfl, gl_succ, gl_succ, gl_zero] at this
  rw [fl_eq]; simp [hc]; omega_arith

omit hp in
/-- With two slices, those after the first are the second. -/
theorem gathered_two (hc : Cnt s = 2) :
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) = bytesAt s.mem (sb s 1) (sl s 1) := by
  have hk : k0 s = 1 := by simp [k0, hc]
  rw [hk, hc, show 2 - 1 = 0 + 1 from rfl, gathered_zero]
  simp [gathered, Sig.listed, sb, sl]

/-- The second slice copied to the output after the first, one byte at a time. -/
theorem fastLoop_wp (hc : Cnt s = 2) (hn : sl s 1 ≠ 0) {st : State} (h : FBase s st)
    (hcp : CopyPre st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) (sl s 1)) (h10 : st.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa (.loop (.block copy1Body) .ne) st fun t => FBase s t ∧ FOut s t := by
  have hgl := gl_two hp hc
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hsl : (⟨sb s 1, sl s 1⟩ : Region) ∈ lsR s := slice_mem s (i := 1) (by omega_arith)
  have c0 : CInv st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) 0 st :=
    ⟨h10, by simp [bytesAt]; rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.mono_mx (by decide) (chunks_wp (P := fun j t => CInv st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) j t ∧
      t.gpr .r8 = st.gpr .r8)
    (fun j t ⟨c, r8⟩ hj => let ⟨t', e, c', z, r8'⟩ := copy1Step_ok8 hcp c hj; ⟨t', e, ⟨c', r8'.trans r8⟩, z⟩)
    (by decide) (⟨c0, rfl⟩ : _ ∧ _) (by omega_arith) (Nat.mod_one _)) fun t ⟨c, r8⟩ tm => ?_
  have hsub : Region.Sub ⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩ (dR s) := by
    have := dK_sub hp (s := s); rw [← hgl, Nat.add_sub_cancel_left] at this; exact this
  have hlen : (bytesAt st.mem (sb s 1) (sl s 1)).length = sl s 1 := length_bytesAt _ _ _
  have fD : Frame [⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩] st.mem t.mem :=
    ChaCha20Poly1305.X86_64.Gather.frame_of c.mem (by rw [hlen])
  have kd : ∀ r ∈ [(⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩ : Region)], (kpR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.d_w.symm.sub_left kpR_sub).sub_right hsub
  have k : ∀ d, d + 8 ≤ 104 → t.mem.readW (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => fD.readW (Offset.contains_base _ hd' (by omega_arith)) kd (by decide)
  have keep : ∀ r, r ∈ calleeSaved ∨ r = .rdx ∨ r = .r8 ∨ r = .r9 → t.gpr r = st.gpr r := fun r hr => by
    rcases hr with hr | rfl | rfl | rfl
    · exact c.keep r (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
        (by intro e; subst e; simp [calleeSaved] at hr)
    · exact c.keep _ (by decide) (by decide) (by decide)
    · exact r8
    · exact c.keep _ (by decide) (by decide) (by decide)
  refine ⟨⟨by rw [keep _ (Or.inl (by decide)), h.rsp], fun r hr => by rw [keep r (Or.inl hr), h.saved r hr],
    c.rd.trans h.rd, c.wr.trans h.wr, h.frame.trans (fD.sub fun r hr => ?_), by rw [k 0 (by decide)]; exact h.ctx,
    by rw [k 8 (by decide)]; exact h.rounds, by rw [keep _ (by simp), h.rdx], by rw [keep _ (by simp), h.r8],
    by rw [keep _ (by simp), h.r9], tm.trans h.mx⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, hsub⟩
  · unfold FOut
    have e := bytesAt_writeBytes_self st.mem (Dst s + BitVec.ofNat 64 (fl s)) (bytesAt st.mem (sb s 1) (sl s 1))
      (by rw [hlen]; omega_arith)
    rw [hlen] at e
    rw [gathered_two hc, show L s - fl s = sl s 1 by omega_arith, c.mem, e]
    exact bytesAt_frame h.frame (ls_apart hp hsl) (by have := hp.w_ls _ hsl; simp at this; omega_arith)

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- With one slice, or an empty second one, nothing follows the first. -/
theorem fout_nil {st : State} (h : Cnt s = 1 ∨ (Cnt s = 2 ∧ sl s 1 = 0)) : FOut s st := by
  have hfl := fl_le hp
  have hk : k0 s = 1 := by rcases h with h | ⟨h, -⟩ <;> simp [k0, h]
  unfold FOut
  rcases h with h | ⟨h, h0⟩
  · have hL : L s = fl s := by
      have := hp.glen
      rw [h, show (1 : Nat) = 0 + 1 from rfl, gl_succ, gl_zero] at this
      rw [fl_eq]; simp [h]; omega_arith
    rw [hL, Nat.sub_self, hk, h]
    simp [bytesAt, gathered, Sig.listed]
  · rw [show L s - fl s = 0 by have := gl_two hp h; omega_arith, gathered_two h, h0]
    simp [bytesAt]

/-- The second slice, if there is one, copied to the output after the first. -/
theorem fastTail_wp (hcnt : Cnt s = 1 ∨ Cnt s = 2) (hsub : L s - fl s ≤ 16) {st : State} (h : FBase s st)
    (h10 : st.gpr .r10 = Src s) (hz : st.zf = some (decide (Cnt s = 1))) :
    WP isa (.ite .e (.block [])
        (.seq (.block fastLen2) (.ite .e (.block []) (.seq (.block fastCopy) (.loop (.block copy1Body) .ne))))) st
      fun t => FBase s t ∧ FOut s t := by
  refine WP.ite (decide (Cnt s = 1)) (by simp only [eval, hz]) (fun e => WP.block_nil ⟨h, fout_nil hp (Or.inl (by simpa using e))⟩)
    (fun e => ?_)
  have hc : Cnt s = 2 := by have : Cnt s ≠ 1 := by simpa using e
                            omega_arith
  have hgl := gl_two hp hc
  refine WP.seq (WP.mono (fastLen2_ok hp hc h h10) fun s₂ ⟨F₂, r10₂, cx₂, zf₂⟩ => ?_)
  refine WP.ite (decide (sl s 1 = 0)) (by simp only [eval, zf₂]) (fun e => WP.block_nil ⟨F₂, fout_nil hp (Or.inr ⟨hc, by simpa using e⟩)⟩)
    (fun e => ?_)
  have hn : sl s 1 ≠ 0 := by simpa using e
  exact WP.seq (WP.mono (fastCopy_ok hp hc (by omega_arith) F₂ r10₂ cx₂) fun s₃ ⟨F₃, P₃, r10₃⟩ =>
    fastLoop_wp hp hc hn F₃ P₃ r10₃)

/-- The arguments of `vg_aes_gcm_seal_split` from the first slice. -/
theorem fastArgs_ok (hn : s.gpr .rcx = 12#64) (hc : Cnt s ≠ 0) {st : State} (h : FBase s st) (o : FOut s st) :
    WP isa (.block fastArgs) st fun t => SCBase s t ∧ SplitRegs s t := by
  obtain ⟨a₀, e₀⟩ := fa_in hp h (i := 0) (by decide)
  obtain ⟨a₂, e₂⟩ := fa_in hp h (i := 2) (by decide)
  obtain ⟨a₃, e₃⟩ := fa_in hp h (i := 3) (by decide)
  obtain ⟨a₄, e₄⟩ := fa_in hp h (i := 4) (by decide)
  have d₀ := desc_in' hp h (j := 0) (by omega_arith)
  have d₈ := desc_in' hp h (j := 8) (by omega_arith)
  have v₀ : st.mem.readW (Src s + BitVec.ofNat 64 0) 64 = fb s := by
    have := sb_eq hp h.frame (i := 0) (by omega_arith)
    rw [show (16 * 0 : Nat) = 0 from rfl] at this
    rw [this]; simp [fb, hc]
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp h.frame (i := 0) (by omega_arith)
    rw [show Src s + BitVec.ofNat 64 (16 * 0) = Src s by simp] at this
    rw [this, fl_eq]; simp [hc]
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastArgs]; xrun [a₀, e₀, a₂, e₂, a₃, e₃, a₄, e₄, d₀, v₀, d₈, v₈], ?_, ?_⟩
  · have g : ∀ r, r ∈ calleeSaved → _ := fun r (hr : r ∈ calleeSaved) => by
      have : r ≠ .rcx ∧ r ≠ .r10 ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .rax ∧ r ≠ .r11 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp [calleeSaved] at hr)
      exact this
    refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.mx⟩
    · simp [gpr_setReg, h.rsp]
    · obtain ⟨a, b, c, d, e, f⟩ := g r hr
      simp [gpr_setReg, a, b, c, d, e, f, h.saved r hr]
    · simp [rd_setReg, h.rd]
    · simp [wr_setReg, h.wr]
    · simp only [mem_setReg]; exact h.frame
    · simp only [mem_setReg]; exact h.ctx
    · simp only [mem_setReg]; exact h.rounds
    · simp only [FOut] at o; simp only [mem_setReg]; exact o
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.rdx]
    · simp [gpr_setReg, hn]
    · simp [gpr_setReg, h.r8]
    · simp [gpr_setReg, h.r9]
    all_goals simp [gpr_setReg]

/-- The path of a TLS record's text, from a state `Same` as the entry. -/
theorem frontFast_wp (S : SplitFn M) {long : Bool} (hg : frontGo long s = true) {st : State}
    (hs : Same s st) : WP isa (frontFast S.fn) st (Done s) := by
  obtain ⟨hn, hcnt, hsub⟩ := front_facts hp hg
  have hc0 : Cnt s ≠ 0 := by omega_arith
  unfold frontFast
  refine WP.seq (WP.mono (fastEntry_ok hp hs) fun s₁ ⟨F₁, r10₁, zf₁⟩ => ?_)
  refine WP.seq (WP.mono (fastTail_wp hp hcnt hsub F₁ r10₁ zf₁) fun s₂ ⟨F₂, O₂⟩ => ?_)
  exact WP.seq (WP.mono (fastArgs_ok hp hn hc0 F₂ O₂) fun s₃ ⟨B₃, G₃⟩ => splitCall_ok hp S B₃ G₃)

end

end VG.Proof.AesGcm.X86_64.Gather
