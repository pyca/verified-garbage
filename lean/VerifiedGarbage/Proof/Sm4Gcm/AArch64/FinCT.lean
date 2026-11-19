module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Tag
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Save
meta import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Flush
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Spec.Gcm

/-! ### `Sm4Gcm.AArch64.StreamVerify`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.Cmp`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: checking a received tag (`tagLenOk`, `cmpSeg`, `verRet`), moving tags

Untrusted: everything here is checked by Lean. `tagLenOk` leaves 1 in `x9`
iff `tagLenOk` allows a tag of `x28` bytes, 0 if not (`tagLenOk_ok`);
`cmpSeg` pads the `x28` bytes of the received tag at `W` and of the computed
one at `W + 112` with zeros, and leaves 0 in `x10` if they are equal, 1 if
not (`cmpSeg_ok`); `verRet` returns 1 or 0 (`verRet_ok`). `tagIn` copies the
received tag into `W` (`tagIn_ok`), and `tagOut` the computed one out of it
(`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64 VG.WriteBytes
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## The length -/

/-- The carry from subtracting 13 after subtracting 4 rejects both ends. -/
theorem tagLenOk_carry {t : Nat} (ht : t < 2 ^ 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 t - 4#64).toNat + (~~~(13 : BitVec 64)).toNat + 1) =
      !Spec.Gcm.tagLenOk t := by
  apply Bool.eq_iff_iff.mpr
  simp [Spec.Gcm.tagLenOk, BitVec.toNat_sub, Nat.mod_eq_of_lt ht]
  omega_arith

/-- `tagLenOk`: `x9` is 1 iff the tag length is allowed. -/
theorem tagLenOk_ok (s : State) {t : Nat} (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0) ∧
      Regs [.x9, .x10] s s' := by
  refine WP.of_runBlock ⟨_, by arun [gpr_addWithCarry, c_addWithCarry], ?_, ?_⟩
  · simp only [gpr_write, gpr_addWithCarry, c_write, c_addWithCarry, State.read,
      BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Size.bits, h28]
    simp only [show BitVec.setWidth 64 (13#16) <<< 0 = (13 : BitVec 64) from rfl,
      show true.toNat = 1 from rfl]
    rw [tagLenOk_carry ht]
    cases Spec.Gcm.tagLenOk t <;> rfl
  · refine ⟨?_, rfl, rfl, rfl, rfl⟩
    intro r hr
    obtain h9 : r ≠ .x9 := fun e => hr (by simp [e])
    obtain h10 : r ≠ .x10 := fun e => hr (by simp [e])
    simp [gpr_write, gpr_addWithCarry, h9, h10]

/-! ## Padded tags -/

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega_arith), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega_arith, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega_arith] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    obtain h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    obtain h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega_arith, bytesAt_add] at hz
  obtain e := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega_arith, zeros, List.drop_replicate]
  rfl

/-- The carry of adding all ones: whether a word is not 0. -/
theorem carry_ne (d : BitVec 64) :
    decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + (false : Bool).toNat) = !decide (d = 0) := by
  have : (0 - 1 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
  rw [this]
  by_cases h : d = 0
  · subst h; decide
  · have : d.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [h, decide_false, Bool.not_false, Bool.toNat_false, Nat.add_zero, decide_eq_true_iff]
    omega_arith

theorem carry_val (d : BitVec 64) :
    (0 : BitVec 64) + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + false.toNat)).toNat =
      BitVec.ofNat 64 (if d = 0 then 0 else 1) := by
  rw [carry_ne]
  by_cases h : d = 0
  · subst h; rfl
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `cmpSeg`: 0 in `x10` iff the first `t` bytes of the tag at `W + 112` are
those at `W`. -/
theorem cmpSeg_ok {k : Reg → BitVec 64} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s) {t : Nat}
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) :
    WP isa cmpSeg s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t then 0 else 1) ∧
      Env Ctx St W SP s' ∧ Kept k s' ∧ s'.gpr .x28 = BitVec.ofNat 64 t ∧
      Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  have w (d : Nat) (h : d + 8 ≤ 768) := he.perm.wW h
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, og₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [imm .x9 0, .str .x .x9 .x19 vO,
      .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO, .str .x .x9 .x19 (rO + 8), ptr .x11 .x19 rO, mov .x12 .x19,
      mov .x13 .x28] s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 264)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 280)
          (0 : BitVec 64) ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 272 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x9, .x11, .x12, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [he.x19, w 256 (by decide), w 264 (by decide), w 272 (by decide), w 280 (by decide)], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, he.x19]
    · simp [gpr_write, he.x19, BitVec.add_zero]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq ?_
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  obtain dW : (⟨W, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 272, 16⟩ := by
    simpa using L.w_w (a := 0) (n := t) (d := 272) (k := 16) (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain lp : LoopPre s₁ W (W + BitVec.ofNat 64 272) t :=
    ⟨by omega_arith, covers_left (by simpa using he₁.perm.wC (d := 0) (n := t) (by omega_arith)),
      he₁.perm.wC (by omega_arith), dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyB_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  obtain he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => og₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  obtain x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 t := by
    rw [og₂ _ (by decide), og₁ _ (by decide), h28]
  refine WP.seq ?_
  obtain ⟨s₃, run₃, hm₃, x11₃, x12₃, x13₃, og₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [ptr .x11 .x19 vO,
      ptr .x12 .x19 uO, mov .x13 .x28] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x11 = W + BitVec.ofNat 64 256 ∧ s₃.gpr .x12 = W + BitVec.ofNat 64 112 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x11, .x12, .x13] s₂ s₃ ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by arun [he₂.x19], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, x28₂]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  obtain dU : (⟨W + BitVec.ofNat 64 112, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩ :=
    L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain lp₃ : LoopPre s₃ (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 256) t :=
    ⟨by omega_arith, covers_left (he₃.perm.wC (by omega_arith)), he₃.perm.wC (by omega_arith), dU.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyB_ok s₃ x12₃ x11₃ x13₃ lp₃) fun s₄ ⟨hm₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
  obtain he₄ : Env Ctx St W SP s₄ := he₃.keep (fun r hr => og₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  have r (d : Nat) (h : d + 8 ≤ 768) := he₄.perm.wR h
  obtain ⟨s₅, run₅, x10₅, og₅, sp₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO,
      .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1,
      .adds .x .x9 .x9 .x12, .adcs .x .x10 .x11 .x11] s₄ = some s₅ ∧
      s₅.gpr .x10 = BitVec.ofNat 64 (if (s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 272) 64) ||| (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0 then 0 else 1) ∧
      Others [.x9, .x10, .x11, .x12] s₄ s₅ ∧ s₅.sp = s₄.sp ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by arun [he₄.x19, r 256 (by decide), r 264 (by decide), r 272 (by decide), r 280 (by decide),
      gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry,
      c_write], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
        show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
      exact carry_val _
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_addWithCarry, hr]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e8 (a : Nat) : W + BitVec.ofNat 64 (a + 8) = W + BitVec.ofNat 64 a + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc W a 8).symm
  obtain hm₁' : s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [hm₁, ← e8, ← e8]
  obtain fa := Proof.Cmac.frame_store2 (m := s.mem) (W + BitVec.ofNat 64 256) 0 0
  obtain fb := Proof.Cmac.frame_store2 (m := (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) (W + BitVec.ofNat 64 272) 0 0
  have sR (d n : Nat) (h₁ : 256 ≤ d) (h₂ : d + n ≤ 288) :
      ∃ r' ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r' :=
    ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  obtain f₁ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₁.mem := by
    rw [hm₁']
    refine (fa.sub fun r hr => ?_).trans (fb.sub fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr)
    · exact sR 256 16 (by decide) (by decide)
    · exact sR 272 16 (by decide) (by decide)
  obtain z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 272) 16 = zeros 16 := by
    rw [hm₁', Proof.Cmac.bytesAt_store2]; rfl
  obtain z₀ : bytesAt s₁.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [hm₁', bytesAt_frame fb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Proof.Cmac.bytesAt_store2]; rfl
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 272, t⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain f₄ : Frame [⟨W + BitVec.ofNat 64 256, t⟩] s₂.mem s₄.mem := by
    rw [hm₄, hm₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain f₁₂ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 272 t (by decide) (by omega_arith))
  obtain f₁₄ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₄.mem :=
    f₁₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 256 t (by decide) (by omega_arith))
  obtain hA : bytesAt s₁.mem W t = bytesAt s.mem W t :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := t) (d := 256) (k := 32) (.inl (by omega_arith)) (by omega_arith) (by decide)) (by omega_arith)
  obtain hB : bytesAt s₂.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem (W + BitVec.ofNat 64 112) t :=
    bytesAt_frame f₁₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)) (by omega_arith)
  obtain p₁ : bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s.mem W t ++ zeros (16 - t) := by
    rw [hm₂, pad_bytes z₁ _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hA]
  obtain z₀' : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by omega_arith))
      (by decide), z₀]
  obtain p₀ : bytesAt s₄.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem (W + BitVec.ofNat 64 112) t ++ zeros (16 - t) := by
    rw [hm₄, hm₃, pad_bytes z₀' _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hB]
  obtain q₁ : bytesAt s₄.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega_arith)) (by decide) (by omega_arith))
      (by decide)
  obtain key : ((s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 272) 64) |||
      (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0) ↔
      bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t := by
    rw [show (264 : Nat) = 256 + 8 from rfl, show (280 : Nat) = 272 + 8 from rfl, e8 256, e8 272, words_eq, p₀, q₁, p₁]
    exact ⟨List.append_cancel_right, fun h => by rw [h]⟩
  obtain og : Others [.x9, .x11, .x12, .x13, .x14, .x15, .x10] s s₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h13, h14, h15, h10⟩ := hr
    obtain hl : r ∉ loopRegs := by simp [loopRegs, h11, h12, h13, h14, h15]
    rw [og₅ r (by simp [h9, h10, h11, h12]), og₄ r hl, og₃ r (by simp [h11, h12, h13]), og₂ r hl,
      og₁ r (by simp [h9, h11, h12, h13])]
  refine ⟨by rw [x10₅]; simp only [key], he₄.keep (fun r hr => og₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₅ rd₅ wr₅, hk.of_others og, by rw [og _ (by decide), h28], ?_⟩
  rw [m₅]; exact f₁₄

end

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `cmp`: `cmpSeg`, or for 16-byte tags `cmp16`, which compares them where they are. -/
theorem cmp_ok {k : Reg → BitVec 64} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s) {t : Nat}
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) :
    WP isa cmp s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t then 0 else 1) ∧
      Env Ctx St W SP s' ∧ Kept k s' ∧ s'.gpr .x28 = BitVec.ofNat 64 t ∧
      Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  obtain ⟨s₀, run₀, x9₀, og₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [.lsr .x .x9 .x28 4] s = some s₀ ∧
      s₀.gpr .x9 = BitVec.ofNat 64 (t / 2 ^ 4) ∧ Others [.x9] s s₀ ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧
      s₀.rd = s.rd ∧ s₀.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h28, lsr_ofNat t 4 (by omega_arith)], by others_tac, rfl, rfl, rfl, rfl⟩
  obtain he₀ : Env Ctx St W SP s₀ := he.keep (fun r hr => og₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₀ rd₀ wr₀
  obtain hk₀ : Kept k s₀ := hk.of_others og₀
  obtain x28₀ : s₀.gpr .x28 = BitVec.ofNat 64 t := by rw [og₀ _ (by decide), h28]
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  refine WP.ite (decide (t / 2 ^ 4 = 0)) (eval_zero x9₀ (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (cmpSeg_ok L he₀ hk₀ x28₀ h16) fun s' ⟨x10, e, k', x28', f⟩ =>
      ⟨by rw [x10, m₀], e, k', x28', by rw [← m₀]; exact f⟩
  · have e : t = 16 := by have := of_decide_eq_false hf; omega_arith
    subst e
    have r (d : Nat) (h : d + 8 ≤ 768) := he₀.perm.wR h
    obtain ⟨s₁, run₁, x10₁, og₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa cmp16 s₀ = some s₁ ∧
        s₁.gpr .x10 = BitVec.ofNat 64 (if (s₀.mem.readW (W + BitVec.ofNat 64 112) 64 ^^^
          s₀.mem.readW (W + BitVec.ofNat 64 0) 64) ||| (s₀.mem.readW (W + BitVec.ofNat 64 120) 64 ^^^
          s₀.mem.readW (W + BitVec.ofNat 64 8) 64) = 0 then 0 else 1) ∧
        Others [.x9, .x10, .x11, .x12] s₀ s₁ ∧ s₁.sp = s₀.sp ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧
        s₁.wr = s₀.wr := by
      obtain q₀ := r 112 (by decide)
      obtain q₁ := r 0 (by decide)
      obtain q₂ := r 120 (by decide)
      obtain q₃ := r 8 (by decide)
      refine ⟨_, by arun [cmp16, he₀.x19, q₀, q₁, q₂, q₃, gpr_addWithCarry, c_addWithCarry, mem_addWithCarry,
        rd_addWithCarry, wr_addWithCarry, sp_addWithCarry, c_write], ?_⟩
      refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
          show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
        exact carry_val _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, gpr_addWithCarry, hr]
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    obtain key : ((s₀.mem.readW (W + BitVec.ofNat 64 112) 64 ^^^ s₀.mem.readW (W + BitVec.ofNat 64 0) 64) |||
        (s₀.mem.readW (W + BitVec.ofNat 64 120) 64 ^^^ s₀.mem.readW (W + BitVec.ofNat 64 8) 64) = 0) ↔
        bytesAt s.mem (W + BitVec.ofNat 64 112) 16 = bytesAt s.mem W 16 := by
      rw [show (120 : Nat) = 112 + 8 from rfl, ← add_ofNat_assoc W 112 8, BitVec.add_zero,
        show W + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 by rw [BitVec.add_zero],
        BitVec.add_zero, words_eq, m₀]
    obtain og : Others [.x9, .x10, .x11, .x12] s s₁ := fun r hr => by
      rw [og₁ r hr, og₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)]
    refine ⟨by rw [x10₁]; simp only [key], he₀.keep (fun r hr => og₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁, hk.of_others og, by rw [og _ (by decide), h28], ?_⟩
    rw [m₁, m₀]; exact Frame.refl _ _

end

/-- `verRet`: 1 if the tags are equal (`x10` is 0), 0 if not. -/
theorem verRet_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block verRet) s fun s' => s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Regs [.x0] s s' := by
  refine WP.run ⟨_, by simp only [verRet]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `tagIn` one byte at a time: the received tag, the `t` bytes at `Tg`, copied to `W`. -/
theorem tagInB_ok {s : State} {W Tg : Addr} {t : Nat} (h19 : s.gpr .x19 = W) (h12 : s.gpr .x12 = Tg)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) (hr : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨W, 768⟩] s.wr) (hd : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa (.seq (.block [mov .x11 .x19, mov .x13 .x28]) copyB) s fun s' => bytesAt s'.mem W t = bytesAt s.mem Tg t ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      Others loopRegs s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, og₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x11 .x19, mov .x13 .x28] s =
      some s₁ ∧ s₁.gpr .x11 = W ∧ s₁.gpr .x12 = Tg ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x11, .x13] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h19]
    · simp [gpr_write, h12]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain lp : LoopPre s₁ Tg W t :=
    ⟨by omega_arith, by rw [rd₁, wr₁]; exact hr, covers_prefix (by rw [wr₁]; exact hw) (by omega_arith),
      hd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyB_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ⟨?_, ?_, ?_, by rw [sp₂, sp₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · have := bytesAt_writeBytes_self s₁.mem W (bytesAt s₁.mem Tg t) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [hm₂, this, m₁]
  · rw [hm₂, ← m₁]
    exact (writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · intro r hr
    rw [og₂ r hr, og₁ r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl <;> simp)]

theorem exec_ldrq' {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.load, hin,
    Option.map_some]

theorem exec_strq' {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.store, hout]

/-- `tagIn`: the received tag, the `t` bytes at `Tg`, copied to `W`. -/
theorem tagIn_ok {s : State} {W Tg : Addr} {t : Nat} (h19 : s.gpr .x19 = W) (h12 : s.gpr .x12 = Tg)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) (hr : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨W, 768⟩] s.wr) (hd : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa tagIn s fun s' => bytesAt s'.mem W t = bytesAt s.mem Tg t ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      Others loopRegs s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x13₀, og₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [.lsr .x .x13 .x28 4] s = some s₀ ∧
      s₀.gpr .x13 = BitVec.ofNat 64 (t / 2 ^ 4) ∧ Others [.x13] s s₀ ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧
      s₀.rd = s.rd ∧ s₀.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h28, lsr_ofNat t 4 (by omega_arith)], by others_tac, rfl, rfl, rfl, rfl⟩
  obtain og₀' : Others loopRegs s s₀ := fun r hr => og₀ r (by
    simp only [List.mem_singleton]; rintro rfl; exact hr (by decide))
  unfold tagIn
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  refine WP.ite (decide (t / 2 ^ 4 = 0)) (eval_zero x13₀ (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (tagInB_ok (by rw [og₀ _ (by decide), h19]) (by rw [og₀ _ (by decide), h12])
      (by rw [og₀ _ (by decide), h28]) h16 (by rw [rd₀, wr₀]; exact hr) (by rw [wr₀]; exact hw) hd)
      fun s' ⟨b, f, o, sp, rd, wr⟩ => ⟨by rw [b, m₀], by rw [← m₀]; exact f,
        fun r hr => by rw [o r hr, og₀' r hr], by rw [sp, sp₀], by rw [rd, rd₀], by rw [wr, wr₀]⟩
  · have e : t = 16 := by have := of_decide_eq_false hf; omega_arith
    subst e
    obtain i₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x12 + BitVec.ofNat 64 0) 16 := by
      rw [og₀ _ (by decide), h12, rd₀, wr₀, BitVec.add_zero]
      exact hr Tg 16 ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    obtain i₂ : InRegions (s₀.setV .v0 (s₀.mem.read (s₀.gpr .x12 + BitVec.ofNat 64 0) 16)).wr
        ((s₀.setV .v0 (s₀.mem.read (s₀.gpr .x12 + BitVec.ofNat 64 0) 16)).gpr .x19 + BitVec.ofNat 64 0) 16 := by
      show InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 0) 16
      rw [og₀ _ (by decide), h19, wr₀, BitVec.add_zero]
      exact covers_prefix (n := 16) hw (by decide) W 16 ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq' (by decide) (by decide) i₁, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq' (by decide) (by decide) i₂, WP.block_nil ?_⟩
    obtain hx12 : s₀.gpr .x12 = Tg := by rw [og₀ _ (by decide), h12]
    obtain hx19 : s₀.gpr .x19 = W := by rw [og₀ _ (by decide), h19]
    simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.v_setV_self, hx12, hx19, BitVec.add_zero]
    refine ⟨?_, ?_, fun r hr => og₀' r hr, sp₀, rd₀, wr₀⟩
    · have := bytesAt_writeBytes_self s₀.mem W (bytesAt s₀.mem Tg 16) (by rw [length_bytesAt]; decide)
      rw [length_bytesAt] at this
      rw [write_read_bytes, this, m₀]
    · rw [write_read_bytes, ← m₀]
      exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `tagOut`: the tag at `W` copied to the 16 bytes at `Tg`. -/
theorem tagOut_ok {s : State} {W Tg : Addr} (h19 : s.gpr .x19 = W) (h28 : s.gpr .x28 = Tg)
    (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) (hw : Covers [⟨Tg, 16⟩] s.wr)
    (hd : (⟨Tg, 16⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa (.block tagOut) s fun s' => bytesAt s'.mem Tg 16 = bytesAt s.mem W 16 ∧
      Frame [⟨Tg, 16⟩] s.mem s'.mem ∧ Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain r₁ := in_off hr (show 0 + 8 ≤ 768 by decide) (by decide)
  obtain r₂ := in_off hr (show 8 + 8 ≤ 768 by decide) (by decide)
  obtain w₁ := in_off hw (show 0 + 8 ≤ 16 by decide) (by decide)
  obtain w₂ := in_off hw (show 8 + 8 ≤ 16 by decide) (by decide)
  obtain hd' : (⟨Tg, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 8, 8⟩ :=
    hd.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Offset.sub_base _ (by decide))
  obtain ⟨s', run, hm, og, sp', rd', wr'⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = (s.mem.writeW Tg (s.mem.readW W 64)).writeW (Tg + BitVec.ofNat 64 8)
        ((s.mem.writeW Tg (s.mem.readW W 64)).readW (W + BitVec.ofNat 64 8) 64) ∧
      Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [tagOut]; arun [h19, h28, r₁, r₂, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, Mem.writeW, Mem.readW, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceAdd, gpr_write, ite_true, ite_false, reduceCtorEq, h19, h28]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, og, sp', rd', wr'⟩
  · rw [hm, bytesAt_copy2 _ hd']
  · rw [hm]; exact Proof.Cmac.frame_store2 _ _ _

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.StreamFinish`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers, keeps the lengths in `x26` and `x27` (`finEntry_ok`) and `tag`
in `x28` (`finishEntry_ok`); `finBody 0` writes the tag to `W`, for any
message of those lengths (`WP.forall_det`), and `tagOut` copies it to
`tag`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- After the entry, with `work` in `w`: the lengths. -/
theorem finEntry_ok {s : State} {Ctx St W : Addr} {w : Reg} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr w = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry w)) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = s.gpr .x3 ∧
      s'.gpr .x4 = s.gpr .x4 ∧ s'.gpr .x5 = s.gpr .x5 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s w hW hperm.w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x26₂, x27₂, x5₂, x6₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 w, mov .x20 .x1, mov .x21 .x0, mov .x26 .x2, mov .x27 .x3] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = St ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x26 = s.gpr .x2 ∧ s₂.gpr .x27 = s.gpr .x3 ∧
      s₂.gpr .x4 = s.gpr .x4 ∧ s₂.gpr .x5 = s.gpr .x5 ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> simp [gpr_write, g₁, hW, hSt, hCtx]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  exact ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁], hperm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩,
    fun _ _ => rfl, x26₂, x27₂, x5₂, x6₂, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- The entry of `finish`: `tag` in `x28`. -/
theorem finishEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr .x5 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x5 ++ [mov .x28 .x4])) s fun s' => Env Ctx St W s.sp s' ∧ Kept s'.gpr s' ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = s.gpr .x3 ∧
      s'.gpr .x28 = s.gpr .x4 ∧ s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x26₁, x27₁, x5₁, _, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  have r : Regs [.x28] s₁ (s₁.write .x .x28 (s₁.gpr .x4 + BitVec.ofNat 64 0)) :=
    ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  exact ⟨he₁.of_regs r, fun _ _ => rfl,
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by simp [gpr_write, x5₁],
    by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `finPre` gives. -/
theorem lay_of_fin {s : State} (hs : finPre s) :
    Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s.sp ∧ Perm (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s ∧
      Covers [⟨s.gpr .x4, 16⟩] s.wr ∧
      (⟨s.gpr .x4, 16⟩ : Region).Disjoint ⟨s.gpr .x5, 768⟩ := by
  simp only [finPre] at hs
  obtain ⟨hsp, hrd, hwr, dcs, -, dcw, -, dsw, dtw, sC, sS, -, sW', wc, ws, -, ww⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw hsp sC sS sW',
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩,
    covers_of_mem (by rw [hwr]; simp), dtw⟩

/-- What writes to the parts `rs` of `W` keep, outside the state. -/
theorem fin_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩) {m₀ m : Mem} (hf : Frame rs m₀ m)
    {x : List Byte} :
    ciphOf m Ctx = ciphOf m₀ Ctx ∧ blockAt m St = blockAt m₀ St ∧
      blockAt m (Ctx + BitVec.ofNat 64 240) = ctxH m₀ Ctx ∧
      (Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x →
        Absorbed m (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) (ctxH m₀ Ctx) x) :=
  ⟨ciph_frame hf (fun r hr => L.cw'.sub_right (hrs r hr).2),
    blockAt_frame hf (fun r hr => (hrs r hr).1.sub_left (Region.sub_prefix (by decide))),
    blockAt_frame hf (fun r hr => (L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right (hrs r hr).2),
    fun ha => Absorbed.frame hf (fun r hr => (hrs r hr).1.sub_left (Lay.stSub (by decide))) ha⟩

/-- The saved registers' slots are parts of `W` outside the state. -/
theorem savedR_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) :
    ∀ r ∈ [savedR W], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩ := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.sb.sub_right (Lay.bSub (by decide) (by decide)), Lay.wSub (by decide)⟩

/-- One run of `stream_finish`, for a message `a`, `c` of those lengths. -/
theorem fin_run (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x2 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x3 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        bytesAt s'.mem (s.gpr .x4) 16 =
          toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1)))) := by
  have hs' : finPre s := hs
  obtain ⟨L, perm, tW, dtw⟩ := lay_of_fin hs'
  refine WP.seq (WP.mono (finishEntry_ok rfl rfl rfl perm)
    fun s₁ ⟨he₁, hk₁, x26₁, x27₁, x28₁, m₁, rd₁, wr₁⟩ => ?_)
  have fsv : Frame [savedR (s.gpr .x5)] s.mem s₁.mem := by rw [m₁]; exact savedMem_frame _ _ _
  obtain ⟨hc₁, hj₁, hH₁, hA₁⟩ := fin_inv L (savedR_inv L) fsv (x := ghashInput a c)
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := a) (c := c) he₁ hk₁
    (by rw [x26₁, h3]) (by rw [x27₁, h4]) hc hH₁)) fun s₂ ⟨⟨he₂, hk₂, f₂, out₂⟩, _, wr₂⟩ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .x5) s := by
    have := savedAt_save s.mem (s.gpr .x5) s
    rw [← m₁] at this
    exact this.frame f₂ (saved_finFrame L (.inl rfl))
  have x28₂ : s₂.gpr .x28 = s.gpr .x4 := by rw [hk₂ .x28 (by decide), x28₁]
  refine WP.seq (WP.mono (tagOut_ok he₂.x19 x28₂ (covers_left he₂.perm.w) (by rw [wr₂, wr₁]; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₃ ⟨out₃, f₃, og₃, sp₃, rd₃, wr₃⟩ => ?_)
  have he₃ : Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x5) s.sp s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have hsv₃ : SavedAt s₃.mem (s.gpr .x5) s := hsv.frame f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₃.x19 he₃.sp (covers_left he₃.perm.w) hsv₃) fun s' ⟨ga, hm, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hm, out₃, ← hc₁, ← hj₁]
  have := out₂ (hA₁ ha)
  rw [add_ofNat_zero] at this
  exact this

theorem streamFinish_wp (v : GcmImpl) {s : State} (hs : streamFinishAArch64.pre s) :
    WP isa (streamFinish v.callees) s fun s' => GprAbi s s' ∧ streamFinishAArch64.post s s' := by
  have h3 : s.gpr .x2 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x2).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x3).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' => bytesAt s'.mem (s.gpr .x4) 16 = Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2)
    (fin_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x3).toNat = c.length := hc
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x3 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (fin_run v hs hl h4c (hc ▸ (s.gpr .x3).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  show _ = Spec.Gcm.fullTag ciph h iv a c
  rw [hout habs, Proof.Gcm.fullTag_eq, hj]
  rfl

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. After the entry, `tagLenOk`
checks the tag length (a public value); if `tagLenOk` does not allow it, 0 is
returned; otherwise `tagIn` copies the received tag to `W`, `finBody 112`
writes the tag at `W + 112`, `cmpSeg` compares its first `tag_len` bytes with
the received ones without a branch, and `verRet` returns 1 or 0
(`ver_run`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks ghashInput StreamRepr ofBytes toBytes zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem tagLenOk_le {t : Nat} (h : Spec.Gcm.tagLenOk t = true) : t ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at h
  omega_using [h]

/-- The entry of `verify`: `tag_len` in `x28` and `tag` in `x12`. -/
theorem verEntry_ok {s : State} {Ctx St W : Addr} (hCtx : s.gpr .x0 = Ctx) (hSt : s.gpr .x1 = St)
    (hW : s.gpr .x6 = W) (hperm : Perm Ctx St W s) :
    WP isa (.block (finEntry .x6 ++ [mov .x28 .x5, mov .x12 .x4])) s fun s' => Env Ctx St W s.sp s' ∧
      Kept s'.gpr s' ∧ s'.gpr .x26 = s.gpr .x2 ∧
      s'.gpr .x27 = s.gpr .x3 ∧ s'.gpr .x28 = s.gpr .x5 ∧ s'.gpr .x12 = s.gpr .x4 ∧
      s'.mem = savedMem s.mem W s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.block_append (WP.mono (finEntry_ok hCtx hSt hW hperm)
    fun s₁ ⟨he₁, _, x26₁, x27₁, x5₁, x6₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  have r : Regs [.x28, .x12] s₁ s' := by subst hs'; exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩
  have x28' : s'.gpr .x28 = s₁.gpr .x5 := by subst hs'; simp [gpr_write]
  have x12' : s'.gpr .x12 = s₁.gpr .x4 := by subst hs'; simp [gpr_write]
  exact ⟨he₁.of_regs r, fun _ _ => rfl,
    by rw [r.others _ (by decide), x26₁], by rw [r.others _ (by decide), x27₁], by rw [x28', x6₁],
    by rw [x12', x5₁], by rw [r.mem, m₁], by rw [r.rd, rd₁], by rw [r.wr, wr₁]⟩

/-- What `verPre` gives. -/
theorem lay_of_ver {s : State} (hs : verPre s) :
    Lay (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp ∧ Perm (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s ∧
      Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr) ∧
      (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 768⟩ := by
  simp only [verPre] at hs
  obtain ⟨hsp, hrd, hwr, dcs, dcw, -, dsw, dtw, sC, sS, -, sW', wc, ws, -, ww⟩ := hs
  exact ⟨Lay.of wc ws ww dcs dcw dsw hsp sC sS sW',
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩,
    covers_mem (by rw [hrd, hwr]; simp), dtw⟩

/-- The parts of `W` that the entry and `tagIn` write. -/
theorem tag16_inv {Ctx St W SP : Addr} (L : Lay Ctx St W SP) :
    ∀ r ∈ [savedR W, ⟨W, 16⟩], (⟨St, 80⟩ : Region).Disjoint r ∧ Region.Sub r ⟨W, 768⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact savedR_inv L _ (List.mem_singleton_self _)
  · exact ⟨L.sa, Region.sub_prefix (by decide)⟩

/-- One run of `stream_verify`, for a message `a`, `c` of those lengths. -/
theorem ver_run (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) {a c : List Byte}
    (h3 : s.gpr .x2 = BitVec.ofNat 64 a.length) (h4 : s.gpr .x3 = BitVec.ofNat 64 c.length)
    (hc : c.length < 2 ^ 64) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        let T := toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
            [ofBytes (lensBlock a.length c.length)] ^^^
            ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1)))
        if Spec.Gcm.tagLenOk (s.gpr .x5).toNat ∧ T.take (s.gpr .x5).toNat =
            bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat then (s'.gpr .x0).setWidth 32 = 1
        else (s'.gpr .x0).setWidth 32 = 0) := by
  have hs' : verPre s := hs
  obtain ⟨L, perm, tR, dtw⟩ := lay_of_ver hs'
  generalize hT : toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
      [ofBytes (lensBlock a.length c.length)] ^^^
      ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1))) = T
  generalize htl : (s.gpr .x5).toNat = tl at tR dtw ⊢
  have htl' : tl < 2 ^ 64 := htl ▸ (s.gpr .x5).isLt
  -- The entry.
  refine WP.seq (WP.mono (verEntry_ok rfl rfl rfl perm)
    fun s₂ ⟨he₂, hk₂, x26₂, x27₂, x28₂, x12₂, m₂, rd₂, wr₂⟩ => ?_)
  have x28₂' : s₂.gpr .x28 = BitVec.ofNat 64 tl := by rw [x28₂, ← htl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have fsv : Frame [savedR (s.gpr .x6)] s.mem s₂.mem := by rw [m₂]; exact savedMem_frame _ _ _
  refine WP.seq (WP.mono (tagLenOk_ok s₂ x28₂' htl') fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have he₃ := he₂.of_regs r₃
  have hk₃ := hk₂.of_others r₃.others
  have m₃ : s₃.mem = s₂.mem := r₃.mem
  have sv₃ : SavedAt s₃.mem (s.gpr .x6) s := by
    have := savedAt_save s.mem (s.gpr .x6) s
    rwa [← m₂, ← m₃] at this
  have ev : isa.eval (.zero .x .x9) s₃ =
      some (decide ((if Spec.Gcm.tagLenOk tl then 1 else 0) = 0)) :=
    eval_zero x9₃ (by split <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp s₄ ∧
      SavedAt s₄.mem (s.gpr .x6) s ∧
      (Absorbed s.mem (s.gpr .x1 + BitVec.ofNat 64 16) (s.gpr .x1 + BitVec.ofNat 64 32)
          (ctxH s.mem (s.gpr .x0)) (ghashInput a c) →
        if Spec.Gcm.tagLenOk tl ∧ T.take tl = bytesAt s.mem (s.gpr .x4) tl then (s₄.gpr .x0).setWidth 32 = 1
        else (s₄.gpr .x0).setWidth 32 = 0))
    (WP.ite _ ev (fun ht => ?_) (fun hf => ?_)) fun s₄ ⟨he₄, sv₄, post₄⟩ => ?_)
  · have hok : Spec.Gcm.tagLenOk tl = false := by
      revert ht; cases Spec.Gcm.tagLenOk tl <;> simp
    refine WP.run ⟨_, by arun [], rfl⟩ fun s₄ hs₄ => ?_
    subst hs₄
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl, sv₃, fun _ => ?_⟩
    rw [ite_eq_right (by simp [hok])]
    simp [gpr_write]
  · have hok : Spec.Gcm.tagLenOk tl = true := by
      revert hf; cases Spec.Gcm.tagLenOk tl <;> simp
    have hle := tagLenOk_le hok
    have x12₃ : s₃.gpr .x12 = s.gpr .x4 := by rw [r₃.others _ (by decide), x12₂]
    have x28₃ : s₃.gpr .x28 = BitVec.ofNat 64 tl := by rw [r₃.others _ (by decide), x28₂']
    refine WP.seq (WP.mono (tagIn_ok he₃.x19 x12₃ x28₃ hle (by rw [r₃.rd, r₃.wr, rd₂, wr₂]; exact tR)
      he₃.perm.w (dtw.sub_right (Region.sub_prefix (by decide))))
      fun s₄ ⟨in₄, f₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
    have he₄ : Env (s.gpr .x0) (s.gpr .x1) (s.gpr .x6) s.sp s₄ := he₃.keep (fun r hr => og₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
    have hk₄ : Kept s₃.gpr s₄ := Kept.of_others (fun _ _ => rfl) og₄
    have F₄ : Frame [savedR (s.gpr .x6), ⟨s.gpr .x6, 16⟩] s.mem s₄.mem :=
      (fsv.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).trans
        (by rw [← m₃]; exact f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp,
          fun _ h => h⟩)
    obtain ⟨hc₄, hj₄, hH₄, hA₄⟩ := fin_inv L (tag16_inv L) F₄ (x := ghashInput a c)
    have x26₄ : s₄.gpr .x26 = BitVec.ofNat 64 a.length := by
      rw [hk₄ .x26 (by decide), r₃.others _ (by decide), x26₂, h3]
    have x27₄ : s₄.gpr .x27 = BitVec.ofNat 64 c.length := by
      rw [hk₄ .x27 (by decide), r₃.others _ (by decide), x27₂, h4]
    refine WP.seq (WP.mono (finBody_ok L v (.inr rfl) (a := a) (c := c) (H := ctxH s.mem (s.gpr .x0)) he₄ hk₄
      x26₄ x27₄ hc hH₄) fun s₅ ⟨he₅, hk₅, f₅, out₅⟩ => ?_)
    have x28₅ : s₅.gpr .x28 = BitVec.ofNat 64 tl := by rw [hk₅ .x28 (by decide), x28₃]
    refine WP.seq (WP.mono (cmp_ok L he₅ hk₅ x28₅ hle) fun s₆ ⟨x10₆, he₆, _, _, f₆⟩ => ?_)
    refine WP.mono (verRet_ok
      (b := decide (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl))
      (by rw [x10₆]; by_cases hp : bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl =
            bytesAt s₅.mem (s.gpr .x6) tl <;> simp [hp]))
      fun s₇ ⟨x0₇, r₇⟩ =>
        ⟨he₆.of_regs r₇, by
          rw [r₇.mem]
          exact (((sv₃.frame f₄ (saved_tag16 L)).frame f₅ (saved_finFrame L (.inr rfl))).frame f₆ (saved_cmp L)),
          fun ha => ?_⟩
    have hT₅ : bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) 16 = T := by
      rw [out₅ (hA₄ ha), hc₄, hj₄, ← hT]
    have hW₅ : bytesAt s₅.mem (s.gpr .x6) tl = bytesAt s.mem (s.gpr .x4) tl := by
      have dW : ∀ r ∈ finFrame (s.gpr .x1) (s.gpr .x6) s.sp 112, (⟨s.gpr .x6, tl⟩ : Region).Disjoint r := by
        intro r hr
        refine Region.Disjoint.sub_left ?_ (Region.sub_prefix hle)
        have ww : ∀ e j, 16 ≤ e → e + j ≤ 768 →
            (⟨s.gpr .x6, 16⟩ : Region).Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 e, j⟩ := fun e j h₁ h₂ => by
          simpa using L.w_w (a := 0) (n := 16) (d := e) (k := j) (.inl h₁) (by decide) h₂
        rcases List.mem_append.mp hr with hr | hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (L.sa.sub_left (Lay.stSub (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · exact (L.sa.sub_left (Region.sub_prefix (by decide))).symm
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · exact ww _ _ (by decide) (by decide)
          · simpa using (L.stk_w (a := 0) (n := 16) (by decide)).symm
      rw [bytesAt_frame f₅ dW (by omega_using [htl]), in₄, m₃]
      refine bytesAt_frame fsv (fun r hr => ?_) (by omega_using [htl])
      simp only [List.mem_singleton] at hr; subst hr
      exact dtw.sub_right (Lay.wSub (by decide))
    have hb : (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl) ↔
        T.take tl = bytesAt s.mem (s.gpr .x4) tl := by
      rw [← bytesAt_take _ _ hle, hT₅, hW₅]
    by_cases hp : T.take tl = bytesAt s.mem (s.gpr .x4) tl
    · rw [ite_eq_left ⟨hok, hp⟩]
      have hb' := hb.mpr hp
      simp only [hb', decide_true, ite_true] at x0₇
      rw [x0₇]; rfl
    · rw [ite_eq_right (fun h => hp h.2)]
      have hb' : ¬ (bytesAt s₅.mem (s.gpr .x6 + BitVec.ofNat 64 112) tl = bytesAt s₅.mem (s.gpr .x6) tl) :=
        fun h => hp (hb.mp h)
      simp only [hb', decide_false, Bool.false_eq_true, ite_false] at x0₇
      rw [x0₇]; rfl
  refine WP.mono (exit_ok he₄.x19 he₄.sp (covers_left he₄.perm.w) sv₄) fun s' ⟨ga, _, hx0, _⟩ =>
    ⟨ga, fun ha => ?_⟩
  rw [hx0]
  exact post₄ ha

theorem streamVerify_wp (v : GcmImpl) {s : State} (hs : streamVerifyAArch64.pre s) :
    WP isa (streamVerify v.callees) s fun s' => GprAbi s s' ∧ streamVerifyAArch64.post s s' := by
  have h3 : s.gpr .x2 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x2).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4 : s.gpr .x3 = BitVec.ofNat 64 (Spec.Gcm.zeros (s.gpr .x3).toNat).length := by
    rw [Proof.Gcm.length_zeros, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h4' : (Spec.Gcm.zeros (s.gpr .x3).toNat).length < 2 ^ 64 := by
    rw [Proof.Gcm.length_zeros]; exact (s.gpr .x3).isLt
  let ciph := ctxCiph s.mem (s.gpr .x0)
  let h := ctxH s.mem (s.gpr .x0)
  let tl := (s.gpr .x5).toNat
  refine WP.mono (WP.forall_det (P := fun (i : List Byte × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .x1) ciph h i.1 i.2.1 i.2.2 ∧
        s.gpr .x2 = BitVec.ofNat 64 i.2.1.length ∧ (s.gpr .x3).toNat = i.2.2.length)
    (Q := fun i s' =>
      if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h i.1 i.2.1 i.2.2).take tl = bytesAt s.mem (s.gpr .x4) tl then
        (s'.gpr .x0).setWidth 32 = 1
      else (s'.gpr .x0).setWidth 32 = 0)
    (ver_run v hs h3 h4 h4') fun ⟨iv, a, c⟩ ⟨hr, hl, hc⟩ => ?_) fun s' ⟨r₀, hq⟩ =>
      ⟨r₀.1, fun iv a c hr hl hc => hq ⟨iv, a, c⟩ ⟨hr, hl, hc⟩⟩
  have hc : (s.gpr .x3).toNat = c.length := hc
  have hl : s.gpr .x2 = BitVec.ofNat 64 a.length := hl
  have h4c : s.gpr .x3 = BitVec.ofNat 64 c.length := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (ver_run v hs hl h4c (hc ▸ (s.gpr .x3).isLt)) fun s' ⟨_, hout⟩ => ?_
  obtain ⟨hj, habs, _⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have ht : Spec.Gcm.fullTag ciph h iv a c =
      toBytes (ghashFrom (ctxH s.mem (s.gpr .x0)) (ghash (ctxH s.mem (s.gpr .x0)) (blocks (padded a c)))
        [ofBytes (lensBlock a.length c.length)] ^^^
        ciphOf s.mem (s.gpr .x0) (blockAt s.mem (s.gpr .x1))) := by
    rw [Proof.Gcm.fullTag_eq, hj]; rfl
  show if Spec.Gcm.tagLenOk tl ∧ (Spec.Gcm.fullTag ciph h iv a c).take tl = _ then _ else _
  rw [ht]
  exact hout habs

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.BodyCT`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.AArch64.Rel`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs relate
two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as AES-GCM's
(`Proof/AesGcm/AArch64/RelBase.lean`), each call by its callee's proof
(`rel_ctr`, `rel_key`, and AES-GCM's `rel_gh`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT GhashImpl GhCall gh_rel)

theorem rel_gh (g : GhashImpl) {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call g.fn.name g.fn.code) TT :=
  gh_rel g fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr (c : CtrImpl) {σ₁ σ₂ : State} {K C D : Addr} {n : Nat} (h₁ : CtrCall σ₁ K C D n)
    (h₂ : CtrCall σ₂ K C D n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call c.fn.name c.fn.code) TT :=
  ctr_rel c fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, n, h₁, h₂, hsp⟩

theorem rel_key (c : KeyImpl) {σ₁ σ₂ : State} {K C : Addr} (h₁ : KeyCall σ₁ K C) (h₂ : KeyCall σ₂ K C)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call c.fn.name c.fn.code) TT :=
  key_rel c fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, h₁, h₂, hsp⟩

end VG.Proof.Sm4Gcm.AArch64

end

end

/-! ### `Sm4Gcm.AArch64.PieceCT`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on AArch64: the pieces are constant time

Untrusted: everything here is checked by Lean. Each piece run from two states
that its correctness proof describes with the same public values (the
addresses, lengths and offsets) leaks the same: its code between calls by the
taint analysis, from the registers those proofs pin, and its calls by their
callees' proofs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ofBytes)
open VG.Proof.Gcm (lensBlock)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem absorb_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {x₁ x₂ : List Byte} {D : Addr} {n o : Nat} {σ₁ σ₂ : State}
    (h₁ : AbsIn Ctx St W SP k₁ H₁ x₁ D n o σ₁) (h₂ : AbsIn Ctx St W SP k₂ H₂ x₂ D n o σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (absorb v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24, .x25]) (absSeg1 yo) h).isSome = true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24]) (.block (absSeg2 yo)) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24, h₁.x25, h₂.x25]) t₁)
    (absSeg1_ok L hyo h₁) (absSeg1_ok L hyo h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (absCall1_ok L hyo v a₁ h₁.ho h₁.hH) (absCall1_ok L hyo v a₂ h₂.ho h₂.hH) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24]) t₂)
    (absSeg2_ok L hyo b₁) (absSeg2_ok L hyo b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (absCall2_ok L hyo v c₁) (absCall2_ok L hyo v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.1.env.sp, d₂.1.env.sp])
    (by agree_tac [d₁.1.env.x20, d₂.1.env.x20, d₁.1.x23, d₂.1.x23, d₁.1.x24, d₂.1.x24]) ⟨_, by taint_decide⟩

/-- `absorbAl yo`: `absorb yo` with nothing buffered. -/
theorem absorbAl_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block}
    {x₁ x₂ : List Byte} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : AbsIn Ctx St W SP k₁ H₁ x₁ D n 0 σ₁) (h₂ : AbsIn Ctx St W SP k₂ H₂ x₂ D n 0 σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbAl v.callees yo) TT := by
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x23, .x24]) (.block (absSeg2 yo)) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have b₁ := h₁.mid (yo := yo)
  have b₂ := h₂.mid (yo := yo)
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x24, b₂.x24]) t₂)
    (absSeg2_ok L hyo b₁) (absSeg2_ok L hyo b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (absCall2_ok L hyo v c₁) (absCall2_ok L hyo v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.1.env.sp, d₂.1.env.sp])
    (by agree_tac [d₁.1.env.x20, d₂.1.env.x20, d₁.1.x23, d₂.1.x23, d₁.1.x24, d₂.1.x24]) ⟨_, by taint_decide⟩

/-- `flush yo` of `o` bytes. -/
theorem flush_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k₁ k₂ : Reg → BitVec 64} {o : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o) (ho : o < 16) :
    RelCT isa (Eq2 σ₁ σ₂) (flush v.callees yo) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x25]) (padSeg yo [ptr .x12 .x20 32]) h).isSome =
      true := by
    rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pad : ∀ {k : Reg → BitVec 64} {σ : State}, Env Ctx St W SP σ → Kept k σ → σ.gpr .x25 = BitVec.ofNat 64 o →
      WP isa (padSeg yo [ptr .x12 .x20 32]) σ (Pad1 Ctx St W SP k yo o (St + BitVec.ofNat 64 32) σ.mem) :=
    fun he hk h25 => padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 ho
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      (covers_left (he.perm.stC (by omega_using [ho]))) (L.st_w (by omega_using [ho]) (.inr ⟨by decide, by decide⟩))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x25] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21, h25₁, h25₂]) t₁)
    (pad he₁ hk₁ h25₁) (pad he₂ hk₂ h25₂) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `lens yo ra rb`. -/
theorem lens_rel (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k₁ k₂ : Reg → BitVec 64} {o₁ o₂ : Nat} {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂)
    (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂)
    (ht : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (lensSeg yo ra rb)) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (lens v.callees yo ra rb) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [he₁.x19, he₂.x19, he₁.x20, he₂.x20, he₁.x21, he₂.x21]) ht)
    (lensSeg_ok L hyo he₁ hk₁ h25₁ hrb) (lensSeg_ok L hyo he₂ hk₂ h25₂ hrb) fun τ₁ τ₂ a₁ a₂ => ?_
  exact rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp])

/-- `crypt`. -/
theorem crypt_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ P D n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k P D n σ) {m' : Mem},
      Frame (crFrame St SP D n) σ.mem m' → ciphOf m' Ctx = ciphOf σ.mem Ctx :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data)
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23, h₁.x24, h₂.x24, h₁.x25, h₂.x25]) ⟨_, by taint_decide⟩)
    (crSeg1_ok L (icb := 0) h₁) (crSeg1_ok L (icb := 0) h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2_ok L b₁.1 b₁.2) (crSeg2_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24]) ⟨_, by taint_decide⟩

/-- `cryptAl`: `crypt` from the start of a keystream block. -/
theorem cryptAl_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {P : Nat} {D : Addr} {n : Nat} {σ₁ σ₂ : State}
    (h₁ : CrIn Ctx St W SP k₁ P D n σ₁) (h₂ : CrIn Ctx St W SP k₂ P D n σ₂) (hP : P % 16 = 0) :
    RelCT isa (Eq2 σ₁ σ₂) (cryptAl v.callees) TT := by
  have hc : ∀ {σ : State} {k : Reg → BitVec 64} (h : CrIn Ctx St W SP k P D n σ) {m' : Mem},
      Frame (crFrame St SP D n) σ.mem m' → ciphOf m' Ctx = ciphOf σ.mem Ctx :=
    fun h _ hf => ciph_frame hf (ctx_crFrame L h.data)
  have m₁ := h₁.mid (icb := 0) hP
  have m₂ := h₂.mid (icb := 0) hP
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23, h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (crArgs_ok L m₁) (crArgs_ok L m₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_ctr v.ctr a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (ctrCall1_ok L v a₁ (hc h₁ a₁.frame)) (ctrCall1_ok L v a₂ (hc h₂ a₂.frame)) fun τ₁ τ₂ b₁ b₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24, .x25] (by rw [b₁.1.env.sp, b₂.1.env.sp])
      (by agree_tac [b₁.1.env.x19, b₂.1.env.x19, b₁.1.env.x20, b₂.1.env.x20, b₁.1.env.x21, b₂.1.env.x21,
        b₁.1.x23, b₂.1.x23, b₁.1.x24, b₂.1.x24, b₁.1.x25, b₂.1.x25]) ⟨_, by taint_decide⟩)
    (crSeg2_ok L b₁.1 b₁.2) (crSeg2_ok L b₂.1 b₂.2) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_ctr v.ctr c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (ctrCall2_ok L v c₁ (hc h₁ c₁.frame)) (ctrCall2_ok L v c₂ (hc h₂ c₂.frame)) fun τ₁ τ₂ d₁ d₂ => ?_
  exact rel_taint [.x20, .x23, .x24] (by rw [d₁.env.sp, d₂.env.sp])
    (by agree_tac [d₁.env.x20, d₂.env.x20, d₁.x23, d₂.x23, d₁.x24, d₂.x24]) ⟨_, by taint_decide⟩

/-- `lens yo ra rb`, run. -/
theorem lens_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {ra rb : Reg} (hrb : rb ≠ .x9)
    {k : Reg → BitVec 64} {o : Nat} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s)
    (h25 : s.gpr .x25 = BitVec.ofNat 64 o) :
    WP isa (lens v.callees yo ra rb) s (TOut Ctx St W SP k yo o
      (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (St + BitVec.ofNat 64 yo))
        [ofBytes (lensBlock (s.gpr ra).toNat (s.gpr rb).toNat)]) s.mem) :=
  WP.seq (WP.mono (lensSeg_ok L hyo he hk h25 hrb) fun _ h₁ => lensCall_ok L hyo v h₁)

/-- `tag o`. -/
theorem tag_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {o₁ o₂ : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 o₁) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 o₂) :
    RelCT isa (Eq2 σ₁ σ₂) (tag v.callees o) TT := by
  have t₁ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block (tagSeg o)) h).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (lens_rel L v (.inr rfl) (by decide) he₁ he₂ hk₁ hk₂ h25₁ h25₂ ⟨_, by taint_decide⟩)
    (lens_ok L v (.inr rfl) (by decide) he₁ hk₁ h25₁) (lens_ok L v (.inr rfl) (by decide) he₂ hk₂ h25₂)
    fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_taint [.x19, .x20, .x21] (by rw [a₁.env.sp, a₂.env.sp])
      (by agree_tac [a₁.env.x19, a₂.env.x19, a₁.env.x20, a₂.env.x20, a₁.env.x21, a₂.env.x21]) t₁)
    (tagSeg_ok L ho a₁.env a₁.kept)
    (tagSeg_ok L ho a₂.env a₂.kept) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_ctr v.ctr b₁.call b₂.call (by rw [b₁.env.sp, b₂.env.sp])

/-- `j0hash`. -/
theorem j0hash_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0hash v.callees) TT := by
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x24] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.env.x19, h₂.env.x19, h₁.env.x20, h₂.env.x20, h₁.env.x21, h₂.env.x21, h₁.x23, h₂.x23,
        h₁.x24, h₂.x24]) ⟨_, by taint_decide⟩)
    (j0Seg_ok L h₁) (j0Seg_ok L h₂) fun τ₁ τ₂ a₁ a₂ => ?_
  refine rel_seq (rel_gh v.gh a₁.call a₂.call (by rw [a₁.env.sp, a₂.env.sp]))
    (j0Call1_ok L v a₁) (j0Call1_ok L v a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  have hlt := h₁.data.lt
  have pad : ∀ {k : Reg → BitVec 64} {H : Block} {m₀ : Mem} {σ : State}, J2 Ctx St W SP k H Np n m₀ σ →
      WP isa (padSeg 0 [mov .x12 .x23]) σ (Pad1 Ctx St W SP k 0 (n % 16) (Np + BitVec.ofNat 64 (16 * (n / 16)))
        σ.mem) := fun b => by
    have hdr := b.data.drop (k := 16 * (n / 16)) (by omega_using [])
    rw [show n - 16 * (n / 16) = n % 16 by omega_using []] at hdr
    exact padSeg_ok L (yo := 0) (.inl rfl) (P := Np + BitVec.ofNat 64 (16 * (n / 16)))
      b.env b.kept b.x25 (Nat.mod_lt _ (by decide))
      (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, b.x23], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
      hdr.rd (hdr.w.sub_right (Lay.wSub (by decide)))
  refine rel_seq (rel_taint [.x19, .x20, .x21, .x23, .x25] (by rw [b₁.env.sp, b₂.env.sp])
      (by agree_tac [b₁.env.x19, b₂.env.x19, b₁.env.x20, b₂.env.x20, b₁.env.x21, b₂.env.x21, b₁.x23, b₂.x23,
        b₁.x25, b₂.x25]) ⟨_, by taint_decide⟩)
    (pad b₁) (pad b₂) fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (rel_gh v.gh c₁.call c₂.call (by rw [c₁.env.sp, c₂.env.sp]))
    (padCall_ok L (.inl rfl) v c₁) (padCall_ok L (.inl rfl) v c₂) fun τ₁ τ₂ d₁ d₂ => ?_
  exact lens_rel L v (.inl rfl) (by decide) d₁.env d₂.env d₁.kept d₂.kept d₁.x25 d₂.x25 ⟨_, by taint_decide⟩

omit L in
/-- The test of the nonce's length. -/
theorem j0pre_ok {s : State} {n : Nat} (h24 : s.gpr .x24 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x9 .x24 12]) s fun s' =>
      s'.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12 ∧ Regs [.x9] s s' := by
  refine WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  exact ⟨by simp [gpr_write, h24], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩

omit L in
theorem J0In.of_regs {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s s' : State}
    (h : J0In Ctx St W SP k H Np n s) (r : Regs [.x9] s s') : J0In Ctx St W SP k H Np n s' :=
  ⟨h.env.of_regs r, h.kept.of_others r.others, by rw [r.others _ (by decide)]; exact h.x23,
    by rw [r.others _ (by decide)]; exact h.x24, by rw [r.others _ (by decide)]; exact h.x26,
    by rw [r.others _ (by decide)]; exact h.x27, h.data.of_eq r.rd r.wr, by rw [r.mem]; exact h.hH⟩

omit L in
theorem j0ev {s : State} {n : Nat} (hlt : n < 2 ^ 64) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    isa.eval (.zero .x .x9) s = some (decide (n = 12)) := by
  show some (s.read .x .x9 == 0) = _
  rw [State.read, h9, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq hlt (by decide)]

/-- The branch of `j0`, run. -/
theorem j0ite_ok (v : GcmImpl) {k : Reg → BitVec 64} {H : Block} {Np : Addr} {n : Nat} {s : State}
    (h : J0In Ctx St W SP k H Np n s) (h9 : s.gpr .x9 = BitVec.ofNat 64 n - BitVec.ofNat 64 12) :
    WP isa (.ite (.zero .x .x9) (.block j012) (j0hash v.callees)) s
      (J0Mid Ctx St W SP k H (bytesAt s.mem Np n) s.mem) := by
  refine WP.ite (decide (n = 12)) (j0ev h.data.lt h9) (fun ht => ?_) (fun hf => ?_)
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact j012_ok L h
  · exact j0hash_ok L v h (by simpa using hf)

/-- `j0`. -/
theorem j0_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {H₁ H₂ : Block} {Np : Addr} {n : Nat}
    {σ₁ σ₂ : State} (h₁ : J0In Ctx St W SP k₁ H₁ Np n σ₁) (h₂ : J0In Ctx St W SP k₂ H₂ Np n σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (j0 v.callees) TT := by
  refine rel_seq (rel_taint [.x24] (by rw [h₁.env.sp, h₂.env.sp]) (by agree_tac [h₁.x24, h₂.x24])
      ⟨_, by taint_decide⟩) (j0pre_ok h₁.x24) (j0pre_ok h₂.x24) fun τ₁ τ₂ ⟨a₁, r₁⟩ ⟨a₂, r₂⟩ => ?_
  have g₁ := h₁.of_regs r₁
  have g₂ := h₂.of_regs r₂
  refine rel_seq (rel_ite (j0ev h₁.data.lt a₁) (j0ev h₁.data.lt a₂) (fun ht => ?_) (fun _ => ?_))
    (j0ite_ok L v g₁ a₁) (j0ite_ok L v g₂ a₂) fun τ₁ τ₂ b₁ b₂ => ?_
  · have h12 : n = 12 := by simpa using ht
    exact rel_taint [.x20, .x23] (by rw [g₁.env.sp, g₂.env.sp])
      (by agree_tac [g₁.env.x20, g₂.env.x20, g₁.x23, g₂.x23]) ⟨_, by taint_decide⟩
  · exact j0hash_rel L v g₁ g₂
  · exact rel_taint [.x20] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x20, b₂.env.x20])
      ⟨_, by taint_decide⟩

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: the bodies are constant time

Untrusted: everything here is checked by Lean. Two runs of `encBody`,
`decAbs`, `decBody` or `finBody` from states with the same public values (the
lengths and the offset of the buffered additional data) leak the same.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem hz_mod (o : Nat) (ho : o < 16) : (Spec.Gcm.zeros o).length % 16 = o := by
  rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt ho

/-- `fo`, `flush` and `textArgs` in two runs, and what each leaves. -/
theorem padArgs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, CrIn Ctx St W SP k₁ P D n τ₁ → CrIn Ctx St W SP k₂ P D n τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq fo (.seq (flush v.callees 16) (.seq (.block textArgs) rest))) TT := by
  have hn := h₁.data.ok.lt
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k27₁ : k₁ .x27 = BitVec.ofNat 64 P := (h₁.kept .x27 (by decide)).symm.trans h₁.x27
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k27₂ : k₂ .x27 = BitVec.ofNat 64 P := (h₂.kept .x27 (by decide)).symm.trans h₂.x27
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine rel_seq (rel_taint [.x25, .x26, .x27] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.x25, h₂.x25, hq, h₁.x26, h₂.x26, h₁.x27, h₂.x27]) ⟨_, by taint_decide⟩)
    (fo_ok h₁.x25 h₁.x26 h₁.x27 hn h₁.hP) (fo_ok h₂.x25 h₂.x26 h₂.x27 hn h₂.hP)
    fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have he₁ := h₁.env.of_regs r₁
  have he₂ := h₂.env.of_regs r₂
  have hk₁ := h₁.kept.of_others r₁.others
  have hk₂ := h₂.kept.of_others r₂.others
  rw [← hq] at x25₂
  refine rel_seq (flush_rel L v (.inr rfl) he₁ he₂ hk₁ hk₂ x25₁ x25₂ (by split <;> omega_using []))
    (WP.with_rdwr (flushStep_ok L v (a := a₁) (c := c₁) (n := n) he₁ hk₁ (by rw [x25₁, h₁.hc]) rfl))
    (WP.with_rdwr (flushStep_ok L v (a := a₂) (c := c₂) (n := n) he₂ hk₂ (by rw [x25₂, h₂.hc, hq]) rfl))
    fun τ₁ τ₂ ⟨⟨fe₁, fk₁, _, _, _⟩, frd₁, fwr₁⟩ ⟨⟨fe₂, fk₂, _, _, _⟩, frd₂, fwr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x27, .x28] (by rw [fe₁.sp, fe₂.sp])
      (by agree_tac [fk₁ .x26 (by decide), fk₂ .x26 (by decide), fk₁ .x27 (by decide), fk₂ .x27 (by decide),
        fk₁ .x28 (by decide), fk₂ .x28 (by decide), k26₁, k26₂, k27₁, k27₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textArgs_ok fk₁ k26₁ k27₁ k28₁ h₁.hP) (textArgs_ok fk₂ k26₂ k27₂ k28₂ h₂.hP)
    fun τ₁ τ₂ ⟨a25₁, a23₁, a24₁, ra₁⟩ ⟨a25₂, a23₂, a24₂, ra₂⟩ => ?_
  have ge₁ := fe₁.of_regs ra₁
  have ge₂ := fe₂.of_regs ra₂
  have gk₁ := fk₁.of_others ra₁.others
  have gk₂ := fk₂.of_others ra₂.others
  exact hr τ₁ τ₂
    ⟨ge₁, gk₁, a23₁, a24₁, a25₁,
      h₁.data.of_eq (by rw [ra₁.rd, frd₁, r₁.rd]) (by rw [ra₁.wr, fwr₁, r₁.wr])⟩
    ⟨ge₂, gk₂, a23₂, a24₂, a25₂,
      h₂.data.of_eq (by rw [ra₂.rd, frd₂, r₂.rd]) (by rw [ra₂.wr, fwr₂, r₂.wr])⟩

/-- `textAbs` in two runs. -/
theorem textAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {σ₁ σ₂ : State}
    (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h23₁ : σ₁.gpr .x23 = D) (h23₂ : σ₂.gpr .x23 = D)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 n) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 n)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (P % 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (P % 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 n) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 n)
    (hd₁ : DataOk St W σ₁ D n) (hd₂ : DataOk St W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (textAbs v.callees) TT := by
  refine rel_ite (eval_zero h26₁ hd₁.lt) (eval_zero h26₂ hd₁.lt) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [he₁.sp, he₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact absorb_rel L v (.inr rfl)
      (⟨he₁, hk₁, h23₁, h24₁, h25₁, hz_mod _ (Nat.mod_lt _ (by decide)), hd₁, rfl⟩ :
        AbsIn Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₁)
      (⟨he₂, hk₂, h23₂, h24₂, h25₂, hz_mod _ (Nat.mod_lt _ (by decide)), hd₂, rfl⟩ :
        AbsIn Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₂)

/-- `encBody` in two runs. -/
theorem encBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (encBody v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (crypt_rel L v c₁ c₂) (WP.with_rdwr (crypt_ok L v (icb := 0) c₁))
    (WP.with_rdwr (crypt_ok L v (icb := 0) c₂)) fun τ₁' τ₂' ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [o₁.kept .x26 (by decide), o₂.kept .x26 (by decide), o₁.kept .x28 (by decide),
        o₂.kept .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok o₁.kept k26₁ k28₁) (textPiece_ok o₂.kept k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := o₁.kept.of_others rp₁.others
  have pk₂ := o₂.kept.of_others rp₂.others
  exact textAbs_rel L v (o₁.env.of_regs rp₁) (o₂.env.of_regs rp₂) pk₁ pk₂ p23₁ p23₂ p24₁ p24₂
    (by rw [rp₁.others _ (by decide), o₁.x25]) (by rw [rp₂.others _ (by decide), o₂.x25])
    ((pk₁ .x26 (by decide)).trans k26₁) ((pk₂ .x26 (by decide)).trans k26₂)
    (c₁.data.ok.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁]))
    (c₂.data.ok.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂]))

/-- `finBody o` in two runs. -/
theorem finBody_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {A P : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 A) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 A)
    (h27₁ : σ₁.gpr .x27 = BitVec.ofNat 64 P) (h27₂ : σ₂.gpr .x27 = BitVec.ofNat 64 P)
    (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (finBody v.callees o) TT := by
  have ho' : (if P = 0 then A % 16 else P % 16) < 16 := by split <;> exact Nat.mod_lt _ (by decide)
  refine rel_seq (rel_taint [.x26, .x27] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [h26₁, h26₂, h27₁, h27₂]) ⟨_, by taint_decide⟩)
    (finOff_ok h26₁ h27₁ hA hP) (finOff_ok h26₂ h27₂ hA hP) fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have fe₁ := he₁.of_regs r₁
  have fe₂ := he₂.of_regs r₂
  have fk₁ := hk₁.of_others r₁.others
  have fk₂ := hk₂.of_others r₂.others
  refine rel_seq (flush_rel L v (.inr rfl) fe₁ fe₂ fk₁ fk₂ x25₁ x25₂ ho')
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₁.mem (Ctx + BitVec.ofNat 64 240)) fe₁ fk₁
      x25₁ (hz_mod _ ho') rfl)
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₂.mem (Ctx + BitVec.ofNat 64 240)) fe₂ fk₂
      x25₂ (hz_mod _ ho') rfl) fun τ₁ τ₂ ⟨t₁, _, _⟩ ⟨t₂, _, _⟩ => ?_
  exact tag_rel L v ho t₁.env t₂.env t₁.kept t₂.kept t₁.x25 t₂.x25

end

end VG.Proof.Sm4Gcm.AArch64

end

end

/-!
# SM4-GCM on AArch64: `vg_sm4_gcm_stream_finish` and `_verify` are constant time

Untrusted: everything here is checked by Lean. The code around `finBody` by
the taint analysis (the tag length and the tags' addresses are public, and
`cmpSeg` compares without a branch); `finBody` by `finBody_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `finBody o`, run, from the state after the entry. -/
theorem finBody_env (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {o : Nat} (ho : o = 0 ∨ o = 112)
    {k : Reg → BitVec 64} {A P : Nat} {τ : State} (he : Env Ctx St W SP τ) (hk : Kept k τ)
    (h26 : τ.gpr .x26 = BitVec.ofNat 64 A) (h27 : τ.gpr .x27 = BitVec.ofNat 64 P) (hP : P < 2 ^ 64) :
    WP isa (finBody v.callees o) τ fun τ' => Env Ctx St W SP τ' ∧ Kept k τ' ∧
      Frame (finFrame St W SP o) τ.mem τ'.mem :=
  WP.mono (finBody_ok L v ho (a := Spec.Gcm.zeros A) (c := Spec.Gcm.zeros P)
    (H := blockAt τ.mem (Ctx + BitVec.ofNat 64 240)) he hk
    (by rw [Proof.Gcm.length_zeros]; exact h26) (by rw [Proof.Gcm.length_zeros]; exact h27)
    (by rw [Proof.Gcm.length_zeros]; exact hP) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa streamFinishAArch64.pre streamFinishAArch64.pub (streamFinish v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, qsp⟩ := hq
  have p₁ : finPre σ₁ := h₁
  have p₂ : finPre σ₂ := h₂
  obtain ⟨L, perm₁, -, -⟩ := lay_of_fin p₁
  obtain ⟨-, perm₂, -, -⟩ := lay_of_fin p₂
  rw [← q0, ← q1, ← q5] at perm₂
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5] qsp (by agree_tac [q0, q1, q2, q3, q4, q5])
      ⟨_, by taint_decide⟩)
    (finishEntry_ok rfl rfl rfl perm₁) (finishEntry_ok q0.symm q1.symm q5.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x26₁, x27₁, x28₁, _, _, _⟩ ⟨e₂, k₂, x26₂, x27₂, x28₂, _, _, _⟩ => ?_
  rw [← qsp] at e₂
  rw [← q2] at x26₂
  rw [← q3] at x27₂
  rw [← q4] at x28₂
  obtain a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x2).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x2).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ k₁ k₂ a26₁ a26₂ a27₁ a27₂
      (σ₁.gpr .x2).isLt (σ₁.gpr .x3).isLt)
    (finBody_env v L (.inl rfl) e₁ k₁ a26₁ a27₁ (σ₁.gpr .x3).isLt)
    (finBody_env v L (.inl rfl) e₂ k₂ a26₂ a27₂ (σ₁.gpr .x3).isLt) fun τ₁' τ₂' f₁ f₂ => ?_
  obtain c28₁ : τ₁'.gpr .x28 = σ₁.gpr .x4 := (f₁.2.1 .x28 (by decide)).trans x28₁
  obtain c28₂ : τ₂'.gpr .x28 = σ₁.gpr .x4 := (f₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [f₁.1.sp, f₂.1.sp])
    (by agree_tac [f₁.1.x19, f₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa streamVerifyAArch64.pre streamVerifyAArch64.pub (streamVerify v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, qsp⟩ := hq
  have p₁ : verPre σ₁ := h₁
  have p₂ : verPre σ₂ := h₂
  obtain ⟨L, perm₁, tR₁, dtw⟩ := lay_of_ver p₁
  obtain ⟨-, perm₂, tR₂, -⟩ := lay_of_ver p₂
  rw [← q0, ← q1, ← q6] at perm₂
  rw [← q4, ← q5] at tR₂
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6] qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6]) ⟨_, by taint_decide⟩)
    (verEntry_ok rfl rfl rfl perm₁) (verEntry_ok q0.symm q1.symm q6.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x26₁, x27₁, x28₁, x12₁, _, rd₁, wr₁⟩
      ⟨e₂, k₂, x26₂, x27₂, x28₂, x12₂, _, rd₂, wr₂⟩ => ?_
  rw [← qsp] at e₂
  rw [← q2] at x26₂
  rw [← q3] at x27₂
  rw [← q5] at x28₂
  rw [← q4] at x12₂
  rw [← rd₁, ← wr₁] at tR₁
  rw [← rd₂, ← wr₂] at tR₂
  obtain t28₁ : τ₁.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [x28₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain t28₂ : τ₂.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [x28₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x2).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x2).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain htl := (σ₁.gpr .x5).isLt
  refine rel_seq (rel_taint [.x28] (by rw [e₁.sp, e₂.sp]) (by agree_tac [t28₁, t28₂]) ⟨_, by taint_decide⟩)
    (tagLenOk_ok τ₁ t28₁ htl) (tagLenOk_ok τ₂ t28₂ htl) fun τ₁' τ₂' ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  obtain ge₁ := e₁.of_regs r₁
  obtain ge₂ := e₂.of_regs r₂
  obtain gk₁ := k₁.of_others r₁.others
  obtain gk₂ := k₂.of_others r₂.others
  -- The branch and its run.
  obtain ev : ∀ {τ : State}, τ.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat then 1 else 0) →
      isa.eval (.zero .x .x9) τ =
        some (decide ((if Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat then 1 else 0) = 0)) :=
    fun h => eval_zero h (by split <;> decide)
  obtain tIn : ∀ {τ' : State} (hok : Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat = true),
      Env (σ₁.gpr .x0) (σ₁.gpr .x1) (σ₁.gpr .x6) σ₁.sp τ' → τ'.gpr .x12 = σ₁.gpr .x4 →
      τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat →
      Covers [⟨σ₁.gpr .x4, (σ₁.gpr .x5).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa tagIn τ' fun τ'' => Env (σ₁.gpr .x0) (σ₁.gpr .x1) (σ₁.gpr .x6) σ₁.sp τ'' ∧ Kept τ'.gpr τ'' :=
    fun hok he h12 h28 hr => WP.mono (tagIn_ok he.x19 h12 h28 (tagLenOk_le hok) hr he.perm.w
      (dtw.sub_right (Region.sub_prefix (by decide)))) fun _ ⟨_, _, og, sp, rd, wr⟩ =>
        ⟨he.keep (fun r hr => og r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, Kept.of_others (fun _ _ => rfl) og⟩
  obtain run : ∀ {τ' : State} {k : Reg → BitVec 64}, Env (σ₁.gpr .x0) (σ₁.gpr .x1) (σ₁.gpr .x6) σ₁.sp τ' →
      Kept k τ' → τ'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat then 1 else 0) →
      τ'.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x2).toNat →
      τ'.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat → τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat →
      τ'.gpr .x12 = σ₁.gpr .x4 → Covers [⟨σ₁.gpr .x4, (σ₁.gpr .x5).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa (.ite (.zero .x .x9) (.block [imm .x0 0])
        (.seq tagIn (.seq (finBody v.callees uO) (.seq cmp (.block verRet))))) τ' fun τ'' =>
        Env (σ₁.gpr .x0) (σ₁.gpr .x1) (σ₁.gpr .x6) σ₁.sp τ'' := by
    intro τ' k he hk h9 h26 h27 h28 h12 hr
    refine WP.ite _ (ev h9) (fun _ => ?_) (fun hf => ?_)
    · exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'
        exact he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl
    · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat = true := by
        revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat <;> simp
      refine WP.seq (WP.mono (tIn hok he h12 h28 hr) fun τ₃ ⟨he₃, hk₃⟩ => ?_)
      refine WP.seq (WP.mono (finBody_env v L (.inr rfl) he₃ hk₃
        (by rw [hk₃ .x26 (by decide), h26]) (by rw [hk₃ .x27 (by decide), h27]) (σ₁.gpr .x3).isLt)
        fun τ₄ ⟨he₄, hk₄, _⟩ => ?_)
      refine WP.seq (WP.mono (cmp_ok L he₄ hk₄ (by rw [hk₄ .x28 (by decide), h28])
        (tagLenOk_le hok)) fun τ₅ ⟨x10₅, he₅, _, _, _⟩ => ?_)
      exact WP.mono (verRet_ok (b := decide (bytesAt τ₄.mem (σ₁.gpr .x6 + BitVec.ofNat 64 112)
        (σ₁.gpr .x5).toNat = bytesAt τ₄.mem (σ₁.gpr .x6) (σ₁.gpr .x5).toNat))
        (by rw [x10₅]; simp only [decide_eq_true_eq])) fun _ ⟨_, r⟩ => he₅.of_regs r
  have g9₁ : τ₁'.gpr .x9 = _ := x9₁
  have g9₂ : τ₂'.gpr .x9 = _ := x9₂
  obtain o26₁ : τ₁'.gpr .x26 = _ := (r₁.others .x26 (by decide)).trans a26₁
  obtain o26₂ : τ₂'.gpr .x26 = _ := (r₂.others .x26 (by decide)).trans a26₂
  obtain o27₁ : τ₁'.gpr .x27 = _ := (r₁.others .x27 (by decide)).trans a27₁
  obtain o27₂ : τ₂'.gpr .x27 = _ := (r₂.others .x27 (by decide)).trans a27₂
  obtain o28₁ : τ₁'.gpr .x28 = _ := (r₁.others .x28 (by decide)).trans t28₁
  obtain o28₂ : τ₂'.gpr .x28 = _ := (r₂.others .x28 (by decide)).trans t28₂
  obtain o12₁ : τ₁'.gpr .x12 = _ := (r₁.others .x12 (by decide)).trans x12₁
  obtain o12₂ : τ₂'.gpr .x12 = _ := (r₂.others .x12 (by decide)).trans x12₂
  obtain oR₁ : Covers [⟨σ₁.gpr .x4, (σ₁.gpr .x5).toNat⟩] (τ₁'.rd ++ τ₁'.wr) := by rw [r₁.rd, r₁.wr]; exact tR₁
  obtain oR₂ : Covers [⟨σ₁.gpr .x4, (σ₁.gpr .x5).toNat⟩] (τ₂'.rd ++ τ₂'.wr) := by rw [r₂.rd, r₂.wr]; exact tR₂
  refine rel_seq (rel_ite (ev g9₁) (ev g9₂) (fun _ => ?_) (fun hf => ?_))
    (run ge₁ gk₁ g9₁ o26₁ o27₁ o28₁ o12₁ oR₁) (run ge₂ gk₂ g9₂ o26₂ o27₂ o28₂ o12₂ oR₂)
    fun τ₁ τ₂ f₁ f₂ => ?_
  · exact rel_taint [] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat = true := by
      revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x5).toNat <;> simp
    refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [ge₁.sp, ge₂.sp])
        (by agree_tac [ge₁.x19, ge₂.x19, o28₁, o28₂, o12₁, o12₂]) ⟨_, by taint_decide⟩)
      (tIn hok ge₁ o12₁ o28₁ oR₁) (tIn hok ge₂ o12₂ o28₂ oR₂) fun τ₃ τ₃' ⟨he₃, hk₃⟩ ⟨he₃', hk₃'⟩ => ?_
    refine rel_seq (finBody_rel L v (.inr rfl) he₃ he₃' hk₃ hk₃'
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃' .x26 (by decide), o26₂])
        (by rw [hk₃ .x27 (by decide), o27₁]) (by rw [hk₃' .x27 (by decide), o27₂])
        (σ₁.gpr .x2).isLt (σ₁.gpr .x3).isLt)
      (finBody_env v L (.inr rfl) he₃ hk₃
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃ .x27 (by decide), o27₁]) (σ₁.gpr .x3).isLt)
      (finBody_env v L (.inr rfl) he₃' hk₃'
        (by rw [hk₃' .x26 (by decide), o26₂]) (by rw [hk₃' .x27 (by decide), o27₂]) (σ₁.gpr .x3).isLt)
      fun τ₄ τ₄' ⟨he₄, hk₄, _⟩ ⟨he₄', hk₄', _⟩ => ?_
    obtain c28₁ : τ₄.gpr .x28 = _ := (hk₄ .x28 (by decide)).trans o28₁
    obtain c28₂ : τ₄'.gpr .x28 = _ := (hk₄' .x28 (by decide)).trans o28₂
    refine rel_seq (rel_taint [.x19, .x28] (by rw [he₄.sp, he₄'.sp])
        (by agree_tac [he₄.x19, he₄'.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩)
      (cmp_ok L he₄ hk₄ c28₁ (tagLenOk_le hok)) (cmp_ok L he₄' hk₄' c28₂ (tagLenOk_le hok))
      fun τ₅ τ₅' ⟨_, he₅, _, _, _⟩ ⟨_, he₅', _, _, _⟩ => ?_
    exact rel_taint [] (by rw [he₅.sp, he₅'.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact rel_taint [.x19] (by rw [f₁.sp, f₂.sp]) (by agree_tac [f₁.x19, f₂.x19]) ⟨_, by taint_decide⟩

end VG.Proof.Sm4Gcm.AArch64
