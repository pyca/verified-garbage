module

public import VerifiedGarbage.Impl.AesOcb.AArch64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.AArch64.Words
public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
public import VerifiedGarbage.Proof.Ocb.Stretch
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesOcb.AArch64.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesOcb.AArch64.NonceBlock
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `AesOcb.AArch64.Nonce`, which the modules that import this one used -/

section

/-! ### `AesOcb.AArch64.Offset0`, which only this module used -/

section

/-!
# AES-OCB on AArch64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask shl3 toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_v {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& 1#64 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv]),
    show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  obtain h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega_using [h]

theorem sel_mask0 (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b = true then 1 else 0))) = if b then x' else x := sel_mask x x' b

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .x9 ++ s'.gpr .x10 ++ s'.gpr .x11 = shlIf (v.testBit k) a (s.gpr .x9 ++ s.gpr .x10 ++ s.gpr .x11) ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain c1 : 64 - a < 64 := by omega_using [ha]
  refine ⟨_, by orun [stage, h12, hk6, ha', c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h12, bit_v hv, BitVec.setWidth_eq]
    rw [sel_mask0, sel_mask0, sel_mask0]
    unfold shlIf
    split
    · exact shl3 _ _ _ ha ha'
    · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
  all_goals rfl

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega_using [], ↓reduceIte, show 64 + i - 64 = i by omega_using []]

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {K W : Addr} (L : Lay K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {v : Nat} (hv : v < 64) (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      Off0Post W ((stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  obtain rr : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_left (in_off hw h (by decide))
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, x12₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .x9 .x19 tmpO, .rev .x9 .x9, ld .x10 .x19 (tmpO + 8), .rev .x10 .x10,
       .lsl .x .x11 .x9 8, .lsr .x .x13 .x10 56, .logic .orr .x .x11 .x11 .x13,
       .logic .eor .x .x11 .x11 .x9, ld .x12 .x19 botO] s = some s₁ ∧
      s₁.gpr .x9 ++ s₁.gpr .x10 ++ s₁.gpr .x11 = stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .x12 = BitVec.ofNat 64 v ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13] → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    obtain r₀ := rr (d := 112) (by decide)
    obtain r₁ := rr (d := 120) (by decide)
    obtain r₂ := rr (d := 288) (by decide)
    refine ⟨_, by orun [h19, r₀, r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      obtain hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          rev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ rev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.AArch64.blockAt_rev s.mem (W + BitVec.ofNat 64 112)
        rw [BitVec.add_zero, Offset.add_add] at this
        exact this.symm
      rw [stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, hbot]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    all_goals rfl
  -- the six stages
  obtain keep : ∀ {t t' : State}, (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → t'.gpr r = t.gpr r) →
      t.gpr .x12 = BitVec.ofNat 64 v → t'.gpr .x12 = BitVec.ofNat 64 v := fun g h => by rw [g _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv x12₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (keep g₂ x12₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, sp₄, rd₄, wr₄⟩ := stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep g₃ (keep g₂ x12₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep g₄ (keep g₃ (keep g₂ x12₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, sp₆, rd₆, wr₆⟩ := stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁)))))
  obtain hw7 : s₇.gpr .x9 ++ s₇.gpr .x10 ++ s₇.gpr .x11 =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  obtain hO : s₇.gpr .x9 ++ s₇.gpr .x10 =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .x11), hw7, Proof.Ocb.offset_shl _ (by omega_using [hv])]
  obtain hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  obtain hsp₇ : s₇.sp = s.sp := by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]
  obtain hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  obtain hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  obtain g₁₇ : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain h' : r ∉ [Reg.x9, .x10, .x11, .x13, .x14, .x15] := by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  obtain h19₇ : s₇.gpr .x19 = W := by rw [g₁₇ _ (by decide), h19]
  obtain ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₇.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [hwr₇]; exact in_off hw h (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.rev .x9 .x9, .rev .x10 .x10, st .x19 ofsO .x9,
      st .x19 (ofsO + 8) .x10, st .x19 o0O .x9, st .x19 (o0O + 8) .x10] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 24)
        (rev64 (s₇.gpr .x10))).writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW
        (W + BitVec.ofNat 64 312) (rev64 (s₇.gpr .x10)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s₈.gpr r = s₇.gpr r) ∧ s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    obtain w₁₆ := ww (d := 16) (by decide)
    obtain w₂₄ := ww (d := 24) (by decide)
    obtain w₃₀₄ := ww (d := 304) (by decide)
    obtain w₃₁₂ := ww (d := 312) (by decide)
    refine ⟨_, by orun [h19₇, w₁₆, w₂₄, w₃₀₄, w₃₁₂], ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  obtain val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (rev64 (s₇.gpr .x9)) ++ Proof.Cmac.le8 (rev64 (s₇.gpr .x10))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  obtain run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  obtain f304 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 304, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 312)
        (rev64 (s₇.gpr .x10))) := fun M => by
    rw [← addr8 W 304]; exact Proof.Cmac.frame_store2 _ _ _
  refine ⟨s₈, run, ?_, ?_, ?_, fun r hr => ?_, by rw [sp₈, hsp₇], by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 304, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 304) (k := 16) (d := 312) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, Proof.Ocb.blockAtMem_frame (f304 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 304) (k := 16) (.inl (by decide)) (by decide) (by decide))]
    rw [show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 304) = _
    rw [m₈, show W + BitVec.ofNat 64 312 = W + BitVec.ofNat 64 304 + BitVec.ofNat 64 8 from (addr8 W 304).symm,
      blockAtMem_store2, val]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈ r hr.1 hr.2.1, g₁₇ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2])]

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]

theorem ctxLstar_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 160)` and `[288, 2560)` of `W`. -/
abbrev nonceR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 144⟩, wB W]

theorem nonceR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (nonceR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `nonce` leaves. -/
structure NonceOk (K W D : Addr) (R n : Nat) (SP : Addr) (o : Block) (s s' : State) : Prop where
  env : Env K W D R n SP s'
  frame : Frame (nonceR W) s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (W + BitVec.ofNat 64 d) = blockAtMem s.mem (W + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : Buf W s N nl) (hKD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa (nonce (callees v)) s
      (NonceOk K W D R n SP (Spec.Ocb.offset0 (ctxCiph s.mem K R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E.x19 E.perm.w hN hnl htl h1 h15 ht hB) fun s₁ P₁ => ?_)
  obtain E₁ : Env K W D R n SP s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  obtain F₁ : Frame (nonceR W) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNoFrames L E₁ hR
    (oneBlock_ok E₁.x19 tmpO (by decide)) (dstW L E₁.perm (d := tmpO) (n := 1) (by decide))) fun s₂ P₂ => ?_)
  obtain E₂ : Env K W D R n SP s₂ := E₁.of_saved P₂.saved P₂.sp P₂.rd P₂.wr
  obtain F₂ : Frame (nonceR W) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  obtain ktop : blockAtMem s₂.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD (nonceR_mut F₁) hR) _
  obtain hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  obtain bot₂ : s₂.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), P₁.bot]
  obtain ⟨s₃, run₃, P₃⟩ := offset0_ok L E₂.x19 E₂.perm.w hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega_arith) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega_using [h₂]) (by omega_using [h₂]) (by decide)
        · exact L.w_w (by omega_using [h₂]) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega_using [h₂]) (by omega_using [h₂]) (by decide))]

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `x25`), shifted right
once more each time (in `x11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `x11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt)

theorem and1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v &&& 1#64 = BitVec.ofNat 64 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_of_lt hv, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat_of_lt (by omega_using [])]

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by omega_using [hv]), Nat.shiftRight_eq_div_pow]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ∉ ntzRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `x12 ← x14 ∧ 1`, after `x14 ← v`. -/
theorem low1_ok (s : State) {v : Nat} (hv : v < 2 ^ 64) (h14 : s.gpr .x14 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa low1 s = some s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (v % 2) ∧ s'.gpr .x14 = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [low1], ?_, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h14, and1 hv]
  · simp [gpr_write, h14]
  · simp [gpr_write, h1]
  all_goals rfl

/-- Continue the public-index doubling loop from any already computed L_a. -/
theorem lNtzLoop_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i a : Nat} (hi' : i < 2^64)
    (hpos : 0 < i / 2^a) (he : i / 2^a % 2 = 0) (hntz : ntz i = a + ntz (i / 2^a))
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (i / 2^a))
    (hl : blockAtMem s.mem (W + BitVec.ofNat 64 lO) = lAt l a) :
    WP isa (.loop (.block (dbl .x19 lO lO ++ ([.lsr .x .x14 .x14 1] : List Instr) ++ low1)) (.zero .x .x12)) s
      (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ∉ ntzRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ a) _
    ⟨a, rfl, hpos, he, hntz, h14, Frame.refl _ _, hl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, x14, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h19t : t.gpr .x19 = W := by rw [g _ (by decide), h19]
  obtain ⟨t₁, runt₁, D₁⟩ := dbl_ok (s := t) (b := .x19) (a := lO) (d := lO) (by decide) (by decide) h19t h19t
    (by decide) (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [wr]; exact wW (by decide)) (by rw [wr]; exact wW (by decide))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt₂, x14₂', g₂', m₂', sp₂'', rd₂'', wr₂''⟩ : ∃ t₂, runBlock isa [.lsr .x .x14 .x14 1] t₁ = some t₂ ∧
      t₂.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ (∀ r, r ≠ .x14 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have x14₁ : t₁.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), x14]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x14₁, shr1 hv, e]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨t₃, runt₃, x12₃, x14₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := low1_ok t₂ (by omega_using [hv, e]) x14₂'
  refine WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, runt₁, Option.bind_some, runt₂,
    Option.bind_some, runt₃], ?_⟩
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [m₃, m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₃, m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ∉ ntzRegs → t₃.gpr r = s.gpr r := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r hr.2.2.2.1, g₂' r hr.2.2.2.2.2, D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [sp₃, sp₂'', D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [rd₃, rd₂'', D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [wr₃, wr₂'', D₁.wr, wr]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega_using []
  have hv' : i / 2 ^ (j + 1) < 2 ^ 64 := by omega_using [hv, e]
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_zero x12₃ (by omega_using [])).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega_using [hpos], j + 1, rfl,
      by rw [e]; omega_using [hpos, hev], hodd, hntz', x14₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_zero x12₃ (by omega_using [])).trans (by simp [hodd]), ⟨fr', ?_, g', sp', rd', wr'⟩⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega_using [hodd])]


theorem lNtz_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 64) (h25 : s.gpr .x25 = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := lO) (by decide) (by decide) h19
    (Proof.AesGcm.AArch64.in_left (wW (by decide))) (Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (wW (by decide)) (wW (by decide))
  obtain ⟨s₁', run₁', x14₁', g₁', m₁', sp₁', rd₁', wr₁'⟩ : ∃ s', runBlock isa [Impl.AesGcm.AArch64.mov .x14 .x25] s₁ =
      some s' ∧ s'.gpr .x14 = BitVec.ofNat 64 i ∧ (∀ r, r ≠ .x14 → s'.gpr r = s₁.gpr r) ∧ s'.mem = s₁.mem ∧
      s'.sp = s₁.sp ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
    have h25₁ : s₁.gpr .x25 = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), h25]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h25₁]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨s₂, run₂, x12₂, x14₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := low1_ok s₁' hi' x14₁'
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ∉ ntzRegs → t.gpr r = s₂.gpr r) → t.sp = s.sp →
      t.rd = s.rd → t.wr = s.wr → LNtzPost W l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        g₂ r hr.2.2.2.1, g₁' r hr.2.2.2.2.2, B₁.gpr r (by simp [hr.1, hr.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂, m₁']; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, m₁', B₁.val, hl0]
  have sp₂' : s₂.sp = s.sp := by rw [sp₂, sp₁', B₁.sp]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁', B₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁', B₁.wr]
  have h19₂ : s₂.gpr .x19 = W := by rw [g₂ _ (by decide), g₁' _ (by decide), B₁.gpr _ (by decide), h19]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₁',
    Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_zero x12₂ (by omega_using [])) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂' rd₂' wr₂'))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega_using [hb])]
  have he : i % 2 = 0 := of_decide_eq_true hb
  exact WP.mono (lNtzLoop_ok h19₂ (by rw [wr₂']; exact hw) hi' (a := 0)
    (by simpa using hi) (by simpa using he) (by simp) (by simpa using x14₂) v₂) fun t P =>
      post_of t (fr₂.trans P.frame) P.val P.gpr (P.sp.trans sp₂') (P.rd.trans rd₂') (P.wr.trans wr₂')

end VG.Proof.AesOcb.AArch64
