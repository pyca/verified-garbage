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
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

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
    (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Same s st' :=
  ⟨fun r a b c => (g r a b c).trans (hs.gpr r a b c), hm.trans hs.mem, hrd.trans hs.rd, hwr.trans hs.wr⟩

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
    exact ⟨dsR s, by simp, Offset.contains_base _ (by omega) (by have := hp.w_ds; omega)⟩
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp (m := st.mem) (by rw [hs.mem]; exact Frame.refl _ _) (i := 0) (by omega)
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
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)] at hc
      simp at hc
      show (stackArg s 1).toNat = 1 ∨ (stackArg s 1).toNat = 2
      omega
    refine ⟨hn, hcnt, ?_⟩
    rw [round16 (by omega)] at hx
    have hx16 : (BitVec.ofNat 64 (16 * (fl s / 16)) + 16#64).toNat = (16 * (fl s / 16) + 16) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (fl s / 16)) (by omega)]; rfl
    have hL3 : (stackArg s 3).toNat = L s := rfl
    split at hx
    · next hn' =>
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt, hx16, hL3] at hn'
      by_cases hw : 16 * (fl s / 16) + 16 < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hw] at hn'; omega
      · omega
    · have := congrArg BitVec.toNat hx
      rw [hx16] at this
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      omega
  · next hc =>
    unfold fA at h0
    simp only [hc, decide_false, Bool.not_false, ↓reduceIte] at h0
    rw [h0] at hc; simp at hc

end

end VG.Proof.AesGcm.X86_64.Gather
