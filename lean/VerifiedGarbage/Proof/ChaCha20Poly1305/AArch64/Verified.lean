module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Main
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.ContractPost
public import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit

/-! ### `ChaCha20Poly1305.AArch64.OpenKey.Route`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on AArch64: the route to the one-time key from the stream

`routeKey`: `x10 = 0` iff the length is `keyLo` to 704 bytes (`OpenKey.openMain`,
`SealKey.sealMain`),
then `route`'s `x9`, writing only `x9` and `x10` (`Short.Agree`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_subImm wp_sub wp_lsr wp_movz eval_zero)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (Agree routeVal pad_ok)

/-- `(x - k) >> 63`, for a 64-bit `x`. -/
theorem shr63_sub {x k : Nat} (hx : x < 2 ^ 64) (hk : k ≤ 1024) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 k) >>> 63).toNat = if x < k then 1 else (x - k) / 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega_using [hk] : k < 2 ^ 64)]
  split
  · rw [Nat.mod_eq_of_lt (by omega_arith : 2 ^ 64 - k + x < 2 ^ 64)]
    exact Nat.div_eq_of_lt_le (by omega_using [hk]) (by omega_arith)
  · rw [show 2 ^ 64 - k + x = (x - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [hx] : x - k < 2 ^ 64)]

/-- The value `routeKey` leaves in `x10`. -/
abbrev keyVal (lo : Nat) (x : BitVec 64) : BitVec 64 :=
  (x - BitVec.ofNat 64 lo) >>> 63 - (x - BitVec.ofNat 64 705) >>> 63 + BitVec.ofNat 64 1

theorem keyVal_eq {lo x : Nat} (hlo : 1 ≤ lo) (hlo' : lo ≤ 705) (hx : x < 2 ^ 64) :
    (keyVal lo (BitVec.ofNat 64 x) == 0) = decide (lo ≤ x ∧ x ≤ 704) := by
  obtain b₂ := shr63_sub hx (k := lo) (by omega)
  obtain b₁ := shr63_sub hx (k := 705) (by decide)
  obtain q₂ : (x - lo) / 2 ^ 63 ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [hx]))
  obtain q₁ : (x - 705) / 2 ^ 63 ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [hx]))
  obtain hz : ∀ y : BitVec 64, (y == 0) = decide (y.toNat = 0) := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · have : y.toNat ≠ 0 := fun h' => hy (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (y == 0) = false from beq_eq_false_iff_ne.mpr hy]
      simp [this]
  rw [hz, keyVal, BitVec.toNat_add, BitVec.toNat_sub, b₁, b₂, BitVec.toNat_ofNat]
  congr 1
  apply propext
  by_cases h513 : x < lo
  · simp only [h513, show x < 705 by omega_using [hlo', h513], ite_true]; omega_using [h513]
  · by_cases h705 : x < 705
    · simp only [h513, h705, ite_true, ite_false]; omega_using [h513, h705]
    · simp only [h513, h705, ite_false]
      by_cases hb : x - 705 < 2 ^ 63
      · rw [Nat.div_eq_of_lt hb]; omega_using [hx, h705]
      · rw [Nat.div_eq_of_lt_le (k := 1) (by omega_using [hb]) (by omega_using [hx]),
          Nat.div_eq_of_lt_le (k := 1) (m := x - lo) (by omega_using [hlo', hb]) (by omega_using [hx])]
        omega_using [h705]

/-- `routeKey`: `x10` and then `route`'s `x9`. -/
theorem routeKey_ok (sve enc : Bool) (s₀ : State) :
    WP isa (.block (routeKey sve enc)) s₀ fun s₁ => Agree s₀ s₁ ∧
      s₁.gpr .x9 = routeVal sve enc (s₀.gpr .x5) ∧ s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) := by
  obtain hlo : wideLo sve enc < 4096 := by cases sve <;> cases enc <;> decide
  obtain hsh : wideSh sve enc < 64 := by cases sve <;> cases enc <;> decide
  obtain h : WP isa (.block (routeKey sve enc)) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = routeVal sve enc (s₀.gpr .x5) ∧ s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
    unfold routeKey
    refine WP.block_append (WP.block_append ((pad_ok 4 s₀).mono fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ => ?_))
    refine wp_subImm (by decide) fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ =>
      wp_subImm (by cases sve <;> cases enc <;> decide) fun s₇ u₇ => wp_lsr (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
      wp_addImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain x5 : s₄.gpr .x5 = s₀.gpr .x5 := g₄ _ (by decide)
    obtain x10₁₀ : s₁₀.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) := by
      rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), x5,
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, x5]
    show WP isa (.block (List.take 4 (route sve enc))) s₁₀ _
    rw [show (route sve enc).take 4 = [.lsl .x .x9 .x5 55, .lsr .x .x9 .x9 55,
        .subImm .x .x9 .x9 (wideLo sve enc), .lsr .x .x9 .x9 (wideSh sve enc)] by simp [route]]
    refine wp_lsl (by decide) fun t₁ v₁ => wp_lsr (by decide) fun t₂ v₂ =>
      wp_subImm hlo fun t₃ v₃ => wp_lsr hsh fun t₄ v₄ => WP.block_nil
        ⟨fun r h9 h10 => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v₄.other r h9, v₃.other r h9, v₂.other r h9, v₁.other r h9, u₁₀.other r h10, u₉.other r h10,
        u₈.other r h10, u₇.other r h10, u₆.other r h9, u₅.other r h9, g₄ r h10]
    · rw [v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), x5]
    · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        x10₁₀]
    · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
    · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄]
    · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]
  exact WP.mono (WP.preservedV (WP.withSp h) (by cases sve <;> cases enc <;> lit_decide))
    fun s₁ ⟨⟨⟨g, x9, x10, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9, x10⟩

/-- The branch: to `OpenKey.openMain` iff the length is 513 to 704 bytes. -/
theorem key_eval {sve enc : Bool} {s₀ s₁ : State} (h : s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5)) :
    isa.eval (.zero .x .x10) s₁ = some (decide (keyLo sve enc ≤ L s₀ ∧ L s₀ ≤ 704)) := by
  obtain e : isa.eval (.zero .x .x10) s₁ = some (s₁.gpr .x10 == 0) := eval_zero s₁ .x10
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀,
    keyVal_eq (by cases sve <;> cases enc <;> decide) (by cases sve <;> cases enc <;> decide) (s₀.gpr .x5).isLt]

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

end

end

/-! ### `ChaCha20Poly1305.AArch64.SealKey.Main`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on AArch64: `seal` from 513 to 704 bytes

`SealKey.sealMain`: the one-time key and the keystream of the data's first
448 bytes from the stream (`OpenKey.keyed_ok`); the additional data and the
lengths block; the first 448 bytes encrypted; the counter set to 8, and the
four blocks after the first eight computed into `ctx[128, 384)` while those
448 bytes are absorbed (`TailO.kernel_ok`, up to three blocks after each
double round); the rest encrypted and absorbed with its padding; the
lengths absorbed and `ctx[768, 1280)` zeroed again.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.SealKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.SealKey
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_mov wp_movz wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk)
open VG.Proof.ChaCha20Poly1305.AArch64.TailO (loadAt_ok out_ok kernel_ok)
open VG.Proof.ChaCha20Poly1305.AArch64.OpenKey (keyed_ok ks8 ks8_eq ks_hi set12_initState8 eight32)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (kpAt kp')
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- `pre`: the counter set to 8, the kernel's arguments, the length in `x2`,
and 448 in `x23`. -/
theorem pre_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv0 e s₀ s) :
    WP isa (.block SealKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9, .x23] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  obtain o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  obtain core : WP isa (.block SealKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9, .x23] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      wp_movz fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, eight32]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide)]
    · rw [u₆.gpr]; exact setWidth_ofNat16 (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h2, h3, h9, h23⟩ := hr
      rw [u₆.other _ h23, u₅.other _ h2, u₄.other _ h3, u₃.other _ h0, g₂.gpr, u₁.other _ h9]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) core)
    fun s' ⟨⟨hm, h0, h3, h2, h23, hg, hrd, hwr⟩, hv, hsp, _, _⟩ => ⟨hm, h0, h3, h2, h23, hg, hrd, hwr, hsp, hv⟩

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 513 ≤ L s₀) (hhi : L s₀ ≤ 704) : WP isa (SealKey.sealMain v.callee) s₀ (MainS s₀) := by
  obtain hLt : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hLt
  have wd := hp.wrap_d
  obtain oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  unfold SealKey.sealMain
  refine keyed_ok v hp fun s₁ ⟨h₁, ks₁, v₁⟩ => ?_
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  -- The additional data, and the lengths block.
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  obtain i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  obtain R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  obtain ks₃ : ∀ k < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    rw [k₃.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk,
      k₂.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk, ks₁ k hk]
  obtain d₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₃.frame (by rdisj_all) hk, data_frame k₂.frame (by rdisj_all) hk,
      data_frame h₁.fine (by rdisj_all) hk]
  -- The data's first 448 bytes encrypted with their keystream at `ctx + 832`.
  unfold OpenKey.xorFirst
  refine WP.seq (WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x14 = s₃.gpr .x23 ∧ u.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → u.gpr r = s₃.gpr r) ∧ u.mem = s₃.mem)
    (wp_mov fun t₁ u₁ => wp_movz fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; exact setWidth_ofNat16 (by decide),
        fun r h14 h23 => by rw [u₂.other _ h23, u₁.other _ h14], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₄ ⟨⟨x14₄, x23₄, g₄, m₄⟩, vv₄, sp₄, rd₄, wr₄⟩ => ?_))
  obtain x21₄ : s₄.gpr .x21 = cx s₀ := by rw [g₄ _ (by decide) (by decide), i₃.x21]
  obtain x22₄ : s₄.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by
    rw [g₄ _ (by decide) (by decide), i₃.x22, BitVec.add_zero]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromAt_ok hp (k := 832) (o := 0) (n := 448)
    (by omega_arith) (by omega_arith) x21₄ x22₄ x23₄ (by rw [rd₄, i₃.rd]) (by rw [wr₄, i₃.wr])) (by lit_decide))
    fun s₅ ⟨⟨k₅, e₅, f₅, g₅⟩, v₅⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x23 = s₅.gpr .x14 ∧ (∀ r, r ≠ .x23 → u.gpr r = s₅.gpr r) ∧ u.mem = s₅.mem)
    (wp_mov fun t₁ u₁ => WP.block_nil ⟨u₁.gpr, fun r h23 => u₁.other _ h23, u₁.mem⟩)).mono
    fun s₆ ⟨⟨x23₆, g₆, m₆⟩, vv₆, sp₆, rd₆, wr₆⟩ => ?_
  have g₅' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₅.gpr r = s₄.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₅ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  have to₃ (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x23) :
      s₆.gpr r = s₃.gpr r := by
    obtain ⟨h9, h10, h11, h12, h13, h14, h15, h23⟩ := h
    rw [g₆ r h23, g₅' r ⟨h9, h10, h11, h12, h13, h15⟩, g₄ r h14 h23]
  obtain x23₆' : s₆.gpr .x23 = BitVec.ofNat 64 (L s₀) := by
    rw [x23₆, g₅' _ (by decide), x14₄, i₃.x23, hL]
  obtain sp₆' : s₆.sp = s₀.sp := by rw [sp₆, k₅.sp, sp₄, i₃.sp]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₅.rd, rd₄, i₃.rd]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₅.wr, wr₄, i₃.wr]
  obtain i₆ : Inv0 true s₀ s₆ := by
    refine ⟨by rw [to₃ _ (by decide),
        i₃.x21], fun r hr => ?_, sp₆', rd₆', wr₆', ?_, ?_⟩
    · have hu : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x23 := by
        simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [to₃ r hu, i₃.un r hr]
    · rw [m₆]
      exact i₃.saved.frame (by rw [← m₄]; exact k₅.frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
    · rw [m₆]
      exact i₃.frame.trans ((by rw [← m₄]; exact k₅.frame : Frame [dR s₀] s₃.mem s₅.mem).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)
  -- The data at `s₆`: its first 448 bytes encrypted, the rest as it was.
  obtain ksA : ∀ i < 448, s₄.mem (kpAt s₀ 832 + BitVec.ofNat 64 i) = (KS1 s₀).getD i 0 := by
    intro i hi
    obtain e : kpAt s₀ 832 + BitVec.ofNat 64 i = off (cx s₀) 768 + BitVec.ofNat 64 (64 + i) := by
      simp only [kpAt]; rw [oo, oo]; congr 1; omega_arith
    rw [e, m₄, ks₃ _ (by omega_arith), ks8_eq s₀ (n := L s₀) (by omega_arith) hi]
  obtain c₆ : ∀ i < L s₀, s₆.mem (dp s₀ + BitVec.ofNat 64 i) =
      if i < 448 then s₀.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ (KS1 s₀).getD i 0
      else s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
    intro i hi
    rw [m₆]
    split
    · next h448 =>
      obtain x := e₅ i h448
      simp only [Nat.zero_add] at x
      rw [x, ksA i h448, m₄, d₃ i hi]
    · next h448 =>
      obtain nf : ¬ (⟨dp s₀ + BitVec.ofNat 64 0, 448⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
        split <;> omega_arith
      rw [f₅ _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact nf), m₄, d₃ i hi]
  obtain st₆ : stateAt s₆.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [m₆, stateAt_frame k₅.frame (by rdisj_all), m₄, st₃]
  obtain R₆ : Repr s₆.mem (off (cx s₀) 448) (otk s₀)
      ([] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))) := by
    rw [m₆]; exact Repr.frame k₅.frame (by rdisj_all) (by rw [m₄]; exact R₃)
  -- The counter set to 8, the kernel's arguments, and 448 bytes to absorb.
  refine WP.seq (WP.block_append (WP.mono (pre_ok hp i₆)
    fun s₇ ⟨m₇, x0₇, x3₇, x2₇, x23₇, g₇, rd₇, wr₇, sp₇, vv₇⟩ => ?_))
  obtain F₇ : Frame [sub s₀ 64 64] s₆.mem s₇.mem := by
    rw [m₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  obtain st₇ : stateAt s₇.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₇, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₆, set12_initState8]
  obtain R₇ := Repr.frame F₇ (by rdisj_all) R₆
  obtain x21₇ : s₇.gpr .x21 = cx s₀ := by rw [g₇ _ (by decide), i₆.x21]
  obtain rd₇' : s₇.rd = s₀.rd := by rw [rd₇, i₆.rd]
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, i₆.wr]
  -- The accumulator and the clamped key.
  refine (loadAt_ok hp (n := 448) (by omega_arith) x21₇ rd₇' wr₇' x0₇ x23₇ R₇).mono
    fun s₈ ⟨a₈, x20₈, x8₈, x7₈, x6₈, m₈, g₈, vv₈, sp₈, rd₈, wr₈⟩ => ?_
  obtain rd₈' : s₈.rd = s₀.rd := by rw [rd₈, rd₇']
  obtain wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇']
  obtain x0₈ : s₈.gpr .x0 = off (cx s₀) 64 := by rw [g₈ _ (by decide), x0₇]
  obtain x3₈ : s₈.gpr .x3 = off (cx s₀) 128 := by rw [g₈ _ (by decide), x3₇]
  obtain x22₇ : s₇.gpr .x22 = dp s₀ := by
    rw [g₇ _ (by decide), to₃ _ (by decide), i₃.x22]
  obtain hin : ∀ k : Fin 16, InRegions (s₈.rd ++ s₈.wr) (s₈.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₈, oo, rd₈', wr₈']; exact hp.in_ctx' (by omega_arith)
  obtain hw : ∀ d, d + 16 ≤ 256 → InRegions s₈.wr (s₈.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₈, oo, wr₈']; exact hp.in_ctx (by omega_arith)
  obtain hst : (⟨s₈.gpr .x0, 64⟩ : Region).Disjoint ⟨s₈.gpr .x3, 256⟩ := by
    rw [x0₈, x3₈]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain hrd : Readable (dp s₀) (16 * (448 / 16)) s₈ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₈', wr₈']
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [rd₈', wr₈', x0₈, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₈', wr₈', x0₈, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel: the keystream of counters 8 to 11, with the first 448 bytes absorbed.
  refine WP.seq ((WP.preservedV (kernel_ok v.callee.sve 3 (c := 448 / 16) (by omega_arith)
      (by rw [x20₈, x22₇]) x6₈ hin hw hst hrd a₈ (by omega_arith)) (by cases v.callee.sve <;> lit_decide)).mono
    fun s₉ ⟨⟨ks₉, f₉, hv₉, h2₉, x20₉, g₉, rd₉, wr₉, sp₉⟩, v₉⟩ => ?_)
  rw [x3₈, x0₈] at ks₉
  rw [x3₈] at f₉
  have g₉' (r : Reg) (h : r ≠ .x1 ∧ r ≠ .x4 ∧ r ≠ .x6 ∧ r ∉ Poly.regs) :
      s₉.gpr r = s₈.gpr r :=
    have ⟨h1, h4, h6, hp'⟩ := h
    g₉ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  obtain x0₉ : s₉.gpr .x0 = off (cx s₀) 64 := by
    rw [g₉' _ (by decide), x0₈]
  -- The accumulator stored, and `x22`, `x23` the rest.
  refine WP.seq ((out_ok hp x0₉ (by rw [rd₉, rd₈']) (by rw [wr₉, wr₈'])).mono
    fun s₁₀ ⟨acc₁₀, f₁₀, x21₁₀, x27₁₀, x28₁₀, x22₁₀, x23₁₀, x20₁₀, x24₁₀, x25₁₀, g₁₀, rd₁₀, wr₁₀, sp₁₀, vv₁₀⟩ => ?_)
  obtain x7₉ : s₉.gpr .x7 = dp s₀ := by rw [g₉' _ (by decide), x7₈, x22₇]
  obtain x2₉ : s₉.gpr .x2 = BitVec.ofNat 64 (L s₀) := by
    rw [g₉' _ (by decide), g₈ _ (by decide), x2₇, x23₆']
  obtain x22₁₀' : s₁₀.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by rw [x22₁₀, x20₉]
  obtain x23₁₀' : s₁₀.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [x23₁₀, x7₉, x2₉, x20₉, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega_arith)]
  -- Frames of the context from `s₆` to `s₁₀`.
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega_arith) (by lit_omega)⟩
  obtain Fp : Frame tgt s₆.mem s₇.mem := F₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 64 64 (by decide) (by decide)
  obtain Fm : Frame tgt s₇.mem s₈.mem := by
    rw [m₈]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  obtain Fk : Frame tgt s₈.mem s₉.mem := f₉.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  obtain Fo : Frame tgt s₉.mem s₁₀.mem := f₁₀.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  obtain F₁₀ : Frame tgt s₆.mem s₁₀.mem := Fp.trans (Fm.trans (Fk.trans Fo))
  obtain dctx : ∀ i < L s₀, s₁₀.mem (dp s₀ + BitVec.ofNat 64 i) = s₆.mem (dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => data_frame F₁₀ (fun r hr => by
      simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hi
  -- The Poly1305 state after `out`: the additional data and the first 448 bytes encrypted.
  let M := [] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))
  have hml : M.length % 16 = 0 := R₆.1
  -- Bytes of the data from memories that agree on it.
  obtain dat : ∀ {m m' : Mem}, (∀ k < L s₀, m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ L s₀ → bytesAt m' (dp s₀ + BitVec.ofNat 64 a) n = bytesAt m (dp s₀ + BitVec.ofNat 64 a) n := by
    intro m m' hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    obtain hi := List.mem_range.mp hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by omega_arith)
  obtain b₈ : bytesAt s₈.mem (dp s₀) (16 * (448 / 16)) = bytesAt s₆.mem (dp s₀) 448 := by
    have := dat (m := s₆.mem) (m' := s₈.mem) (fun k hk => data_frame (Fp.trans Fm) (fun r hr => by
      simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk) 0 448 (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain R₁₀ : Repr s₁₀.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₆.mem (dp s₀) 448) := by
    obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega_arith, ?_, ?_⟩
    · have e := R₆.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₁₀ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk (otk s₀)) M
      rw [acc₁₀ h2₉, show hacc s₉ = Poly.hval s₉ from rfl, hv₉,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₈]
      exact (Poly1305.accumulate_append hml).symm
  -- The rest encrypted with its keystream at `ctx + 128`.
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈']
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈']
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsAt_ok hp (o := 448) (n := L s₀ - 448) (by omega_arith)
    (by omega_arith) x21₁₀ x22₁₀' x23₁₀' rd₁₀' wr₁₀') (by lit_decide)) fun s₁₁ ⟨⟨k₁₁, e₁₁, f₁₁, g₁₁⟩, v₁₁⟩ => ?_)
  have g₁₁' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₁₁.gpr r = s₁₀.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₁₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  -- The invariant.
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₉.mem.readW (off (cx s₀) d) 64 = s₈.mem.readW (off (cx s₀) d) 64 :=
    f₉.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by decide)
  have to₁₀ (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₁₁.gpr r = s₁₀.gpr r := g₁₁' r h
  obtain un₁₁ : ∀ r ∈ untouched, s₁₁.gpr r = s₀.gpr r := by
    intro r hr
    obtain hu := i₆.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₁₀ _ (by decide), g₁₀ _ (by decide),
        g₉' _ (by decide), g₈ _ (by decide), g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide), x20₁₀,
        g₉' _ (by decide), x8₈, g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide), g₁₀ _ (by decide),
        g₉' _ (by decide), g₈ _ (by decide), g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide), x27₁₀, r32 32 (.inl rfl), m₈,
        memIn_800, g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide), x28₁₀, r32 40 (.inr rfl), m₈,
        memIn_808, g₇ _ (by decide), hu]
  let out := [sub s₀ 32 16, sub s₀ 64 408, dR s₀]
  obtain Fa : Frame out s₆.mem s₁₀.mem := F₁₀.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 408, by simp [out], fun _ h => h⟩
  obtain Fb : Frame out s₁₀.mem s₁₁.mem := k₁₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [out], fun _ h => h⟩
  obtain F : Frame out s₆.mem s₁₁.mem := Fa.trans Fb
  obtain i₁₁ : Inv0 true s₀ s₁₁ := ⟨by rw [to₁₀ _ (by decide), x21₁₀],
    un₁₁, by rw [k₁₁.sp, sp₁₀, sp₉, sp₈, sp₇, i₆.sp], by rw [k₁₁.rd, rd₁₀'], by rw [k₁₁.wr, wr₁₀'],
    i₆.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))),
    i₆.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)⟩
  -- The rest absorbed with its padding, the lengths, and `ctx[768, 1280)` zeroed again.
  obtain x22₁₁ : s₁₁.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by
    rw [to₁₀ _ (by decide), x22₁₀']
  obtain x23₁₁ : s₁₁.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [to₁₀ _ (by decide), x23₁₀']
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := 448) (by omega_arith)) i₁₁.x21 i₁₁.rd i₁₁.wr x22₁₁ x23₁₁) (by lit_decide))
    fun s₁₂ ⟨⟨k₁₂, r₁₂⟩, v₁₂⟩ => ?_)
  obtain i₁₂ := mac_inv0 i₁₁ k₁₂
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₂) (by lit_decide))
    fun s₁₃ ⟨⟨i₁₃, k₁₃, r₁₃⟩, v₁₃⟩ => ?_)
  refine WP.mono (Pad.zero_ok hp i₁₃.x21 i₁₃.wr) fun s₁₄ ⟨k₁₄, _, v₁₄⟩ => ?_
  obtain i₁₄ : Inv0 true s₀ s₁₄ := i₁₃.step k₁₄
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The data from `s₁₁` on.
  obtain fin : ∀ i < L s₀, s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) = s₁₁.mem (dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [data_frame k₁₄.frame (by rdisj_all) hi, data_frame k₁₃.frame (by rdisj_all) hi,
        data_frame k₁₂.frame (by rdisj_all) hi]
  -- The ciphertext.
  obtain st₈ : stateAt s₈.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₈, stateAt_frame (memIn_frame (s₀ := s₀) s₇.mem (s₇.gpr .x27) (s₇.gpr .x28)) (by rdisj_all), st₇]
  obtain ksB : ∀ j < L s₀ - 448, s₁₀.mem (kp' s₀ + BitVec.ofNat 64 j) = (KS1 s₀).getD (448 + j) 0 := by
    intro j hj
    obtain hj' : j < 256 := by omega_arith
    rw [f₁₀.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
      ks₉ j hj', st₈, ks_hi s₀ (by omega_arith)]
  obtain ct : ∀ i < L s₀, s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) =
      s₀.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ (KS1 s₀).getD i 0 := by
    intro i hi
    rw [fin i hi]
    by_cases h448 : i < 448
    · rw [f₁₁ _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_rest (P := 448) h448 (by omega_arith)),
        dctx i hi, c₆ i hi, ite_eq_left h448]
    · have x := e₁₁ (i - 448) (by omega_arith)
      rw [show 448 + (i - 448) = i by omega_arith] at x
      rw [x, ksB (i - 448) (by omega_arith), show 448 + (i - 448) = i by omega_arith, dctx i hi, c₆ i hi, ite_eq_right h448]
  obtain hct : bytesAt s₁₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      obtain hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      obtain hDl : (bytesAt s₀.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
      obtain e1 : (bytesAt s₁₄.mem (dp s₀) (L s₀))[i] = s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      obtain e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [D, bytesAt]
      obtain e3 : ∀ h : i < (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length).length,
          (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length)[i] = (KS1 s₀).getD i 0 :=
        fun h => by rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, D, hDl]
      rw [List.getElem_zipWith, e1, e2, e3, ct i hi]
  -- The Poly1305 state.
  obtain b₆ : bytesAt s₆.mem (dp s₀) 448 = bytesAt s₁₄.mem (dp s₀) 448 := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro k hk
    obtain hk := List.mem_range.mp hk
    rw [fin k (by omega_arith), f₁₁ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact not_rest (P := 448) hk (by omega_arith)),
      dctx k (by omega_arith)]
  obtain R₁₁ : Repr s₁₁.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₆.mem (dp s₀) 448) :=
    Repr.frame k₁₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.c_d.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))) R₁₀
  obtain R₁₂ := r₁₂ _ _ R₁₁
  rw [b₆, show bytesAt s₁₁.mem (dp s₀ + BitVec.ofNat 64 448) (L s₀ - 448) =
      bytesAt s₁₄.mem (dp s₀ + BitVec.ofNat 64 448) (L s₀ - 448) from (dat fin 448 _ (by omega_arith)).symm,
    List.append_assoc, split_pad (m := s₁₄.mem) (p := dp s₀) (a := 448) (by decide) (by omega_arith), hct] at R₁₂
  obtain L₁₂ : bytesAt s₁₂.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₂.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame F (by
        intro r hr; simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))) (by lit_omega), m₆,
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), m₄, len₃]
  obtain R₁₄ := Repr.frame k₁₄.frame (by rdisj_all) (r₁₃ _ _ R₁₂)
  rw [L₁₂] at R₁₄
  simp only [M, hA] at R₁₄
  refine ⟨i₁₄, fun r hr => ?_, ?_, hct⟩
  · have a₁ : (s₁₀.v r).extractLsb' 0 64 = (s₉.v r).extractLsb' 0 64 := by rw [vv₁₀]
    obtain a₂ : (s₉.v r).extractLsb' 0 64 = (s₇.v r).extractLsb' 0 64 := by rw [← vv₈]; exact v₉ r hr
    obtain a₃ : (s₇.v r).extractLsb' 0 64 = (s₅.v r).extractLsb' 0 64 := by rw [vv₇, vv₆]
    obtain a₄ : (s₄.v r).extractLsb' 0 64 = (s₃.v r).extractLsb' 0 64 := by rw [vv₄]
    exact (v₁₄ r hr).trans ((v₁₃ r hr).trans ((v₁₂ r hr).trans ((v₁₁ r hr).trans (a₁.trans (a₂.trans
      (a₃.trans ((v₅ r hr).trans (a₄.trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))))))))
  · refine (congrArg (Repr s₁₄.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₁₄
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

end VG.Proof.ChaCha20Poly1305.AArch64.SealKey

end

end

/-! ### `ChaCha20Poly1305.AArch64.Stitched.OpenPad`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.AArch64.Stitch.Pad`, which only this module used -/

section

/-!
# ChaCha20 and Poly1305 together (AArch64): the keystream while absorbing other data

`Stitch.bulkPad`: `Mixed8.enter`, one chunk of the kernel whose phases absorb
the 448 bytes from `x27` (`Stitch.chunkPad`, by `chunkWith_ok`: the phases
point `x20` at the bytes from `x27`, and set it back), and `Mixed8.leave`. The registers `enter` saves are restored, the chunk's data
(`x1`, 512 bytes) is XORed with the keystream of eight blocks from the
state's counter, and the accumulator has absorbed the 448 bytes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP ChunkedFrom source sr br dr scalarBuf)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

/-- What `bulkPad` needs: the kernel's regions (`CP` but for `x20`, which
`enter` sets), the working space 64 bytes after the state, and the 448 bytes
from `x27` readable and apart from the state and the working space. -/
structure PadPre (s : State) : Prop where
  read : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
  vectorRead : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
    (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16
  counter : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4
  buffer : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n
  data : ∀ d n, d + n ≤ 512 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) n
  st_b : (sr s).Disjoint (br s)
  st_d : (sr s).Disjoint (dr s)
  d_b : (dr s).Disjoint (br s)
  x3 : s.gpr .x3 = s.gpr .x0 + 64#64
  blk : ∀ d, d + 8 ≤ 448 → InRegions (s.rd ++ s.wr) (s.gpr .x27 + BitVec.ofNat 64 d) 8
  win : ∀ r ∈ [sr s, br s], (⟨s.gpr .x27, 448⟩ : Region).Disjoint r

/-- The registers `Mixed8.enter` saves, and where in the working space. -/
abbrev gpSlots : List (Reg × Nat) := [(.x20, 256), (.x19, 264), (.x26, 272)]

theorem enter_eq : VG.Impl.ChaCha20.AArch64.Mixed8.enter =
    Spill.saveCode .x3 gpSlots ++ (([.addImm .x .x20 .x3 0] : List Instr) ++
      VG.Proof.ChaCha20.AArch64.Mixed8.saveV) := rfl

theorem leave_eq : VG.Impl.ChaCha20.AArch64.Mixed8.leave =
    VG.Proof.ChaCha20.AArch64.Mixed8.restoreV ++ Spill.restoreCode .x3 gpSlots := rfl

/-- After `enter`. -/
structure Entered (s e : State) : Prop where
  x20 : e.gpr .x20 = s.gpr .x3
  gpr : ∀ r, r ≠ .x20 → e.gpr r = s.gpr r
  v : e.v = s.v
  rd : e.rd = s.rd
  wr : e.wr = s.wr
  sp : e.sp = s.sp
  frame : Frame (enterR s) s.mem e.mem
  saved : Spill.Saved (s.gpr .x3) s.gpr gpSlots e.mem
  v8 : e.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s.v .v8
  v9 : e.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s.v .v9

theorem enter_ok (s : State)
    (hb : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enter) s (Entered s) := by
  rw [enter_eq]
  refine Spill.save_ok (by decide) (fun p hp => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact hb _ 8 (by decide)
  let s₁ : State := { s with mem := Spill.saveMem s.mem (s.gpr .x3) s.gpr gpSlots }
  let a : State := s₁.write .x .x20 (s₁.gpr .x3 + BitVec.ofNat 64 0)
  apply WP.block_cons_iff.mpr
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := s₁) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  obtain ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a (by rw [haw, ha3]; exact hb 128 16 (by decide))
    (by rw [haw, ha3]; exact hb 144 16 (by decide))).mono
    fun u ⟨hg, hv, hr, hw, hsp, hf, h8, h9⟩ => ?_
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf h8 h9
  obtain f₁ : Frame [⟨s.gpr .x3 + BitVec.ofNat 64 256, 32⟩] s.mem a.mem :=
    Spill.saveMem_frame (lo := 256) (n := 32) (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide) (by decide) _ _ _
  obtain hsv : Spill.Saved (s.gpr .x3) s.gpr gpSlots u.mem :=
    (Spill.saveMem_saved (by decide) s.mem (s.gpr .x3) s.gpr).frame hf (fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by decide) (by decide) (by decide))
  refine ⟨?_, fun r hr => ?_, by rw [hv]; rfl, by rw [hr]; rfl, by rw [hw]; rfl, by rw [hsp]; rfl,
    ?_, hsv, h8, h9⟩
  · rw [hg, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · rw [hg, RegUpd.gpr_write_of_ne _ .x _ hr]
  · exact (f₁.mono (by simp [enterR])).trans (hf.mono (by simp [enterR]))

/-- What `bulkPad` leaves: the registers it saves restored, the chunk's data
XORed with the keystream, and the 448 bytes from `x27` absorbed. -/
structure Padded (R a : Nat) (s u : State) : Prop where
  x0 : u.gpr .x0 = s.gpr .x0
  x1 : u.gpr .x1 = s.gpr .x1
  x2 : u.gpr .x2 = s.gpr .x2
  x3 : u.gpr .x3 = s.gpr .x3
  cs : ∀ r ∈ preserved, r ∉ accRegs → u.gpr r = s.gpr r
  v8 : u.v .v8 = s.v .v8
  v9 : u.v .v9 = s.v .v9
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  cnt : source u = source s
  data : ∀ k < 512, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
    s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (VG.Spec.ChaCha20.serialize (VG.Spec.ChaCha20.block (ctr (source s) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s, br s, dr s] s.mem u.mem
  acc : Acc R (absorbAll R a (bytesAt s.mem (s.gpr .x27) 448)) u

/-- An offset of the working space, as an offset of the state. -/
theorem x3_off {s : State} (h : s.gpr .x3 = s.gpr .x0 + 64#64) (d : Nat) :
    s.gpr .x3 + BitVec.ofNat 64 d = s.gpr .x0 + BitVec.ofNat 64 (64 + d) := by
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bulkPad_ok {R a : Nat} (s : State) (hp : PadPre s) (ha : Acc R a s) :
    WP isa (bulkPad sve) s (Padded R a s) := by
  obtain hx3 := x3_off hp.x3
  -- Regions, as offsets of the state.
  obtain hbr : br s = ⟨s.gpr .x0 + BitVec.ofNat 64 64, 320⟩ := by
    simp only [br]; rw [← hx3 0, BitVec.add_zero]
  obtain hsb : (scalarBuf s).Sub (br s) := Region.sub_prefix (by decide)
  obtain hkb : (keyR s).Sub (br s) := by
    rw [hbr]; exact Offset.sub _ (by decide) (by decide)
  obtain henter : ∀ r ∈ enterR s, r.Sub (br s) := by
    intro r hr; simp only [enterR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)
  obtain hkey_st : (keyR s).Disjoint (sr s) := by
    simp only [keyR, sr]
    rw [show s.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  unfold bulkPad
  apply WP.seq
  refine (enter_ok s hp.buffer).mono fun e he => ?_
  obtain e0 : e.gpr .x0 = s.gpr .x0 := he.gpr _ (by decide)
  obtain e1 : e.gpr .x1 = s.gpr .x1 := he.gpr _ (by decide)
  obtain e2 : e.gpr .x2 = s.gpr .x2 := he.gpr _ (by decide)
  obtain e3 : e.gpr .x3 = s.gpr .x3 := he.gpr _ (by decide)
  obtain e27 : e.gpr .x27 = s.gpr .x27 := he.gpr _ (by decide)
  obtain esr : sr e = sr s := by simp only [sr, e0]
  obtain ebr : br e = br s := by simp only [br, e3]
  obtain edr : dr e = dr s := by simp only [dr, e1]
  obtain esb : scalarBuf e = scalarBuf s := by simp only [scalarBuf, e3]
  obtain ekey : keyR e = keyR s := by simp only [keyR, e0]
  obtain erw : e.rd ++ e.wr = s.rd ++ s.wr := by rw [he.rd, he.wr]
  -- The chunk's precondition.
  obtain hcp : CP e := by
    refine ⟨by rw [he.x20, e3], fun k => ?_, fun k => ?_, ?_, fun d n h => ?_, fun d n h => ?_,
      by rw [esr, ebr]; exact hp.st_b, by rw [esr, edr]; exact hp.st_d,
      by rw [edr, ebr]; exact hp.d_b⟩
    · rw [erw, e0]; exact hp.read k
    · rw [erw, e0]; exact hp.vectorRead k
    · rw [he.wr, e0]; exact hp.counter
    · rw [he.wr, e3]; exact hp.buffer d n h
    · rw [he.wr, e1]; exact hp.data d n h
  have hblk (d : Nat) (h : d + 8 ≤ 448) : InRegions (e.rd ++ e.wr) (s.gpr .x27 + BitVec.ofNat 64 d) 8 := by
    rw [erw]; exact hp.blk d h
  have hk (d : Nat) (hd : d = Poly.r0Off ∨ d = Poly.r1Off) :
      InRegions (e.rd ++ e.wr) (e.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := hp.buffer (160 + (d - 224)) 8 (by rcases hd with rfl | rfl <;> decide)
    refine ⟨r, by rw [erw]; exact List.mem_append_right _ hr, ?_⟩
    rw [e0, show s.gpr .x0 + BitVec.ofNat 64 d = s.gpr .x3 + BitVec.ofNat 64 (160 + (d - 224)) by
      rw [hx3]; rcases hd with rfl | rfl <;> rfl]
    exact hc
  have hwin (d n : Nat) (h : d + n ≤ 448) :
      ∀ r ∈ [sr e, scalarBuf e], (⟨s.gpr .x27 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain hs : (⟨s.gpr .x27 + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨s.gpr .x27, 448⟩ := Offset.sub_base _ h
    rcases hr with rfl | rfl
    · rw [esr]; exact (hp.win _ (by simp)).sub_left hs
    · rw [esb]; exact ((hp.win _ (by simp)).sub_left hs).sub_right hsb
  obtain pre : ChunkPreW (.addImm .x .x20 .x27 0) (.addImm .x .x20 .x27 256) (.subImm .x .x27 .x20 256)
      (.subImm .x .x27 .x20 448) .x1 (s.gpr .x27)
      (s.gpr .x27 + BitVec.ofNat 64 256) (16 * (1 + 5 * 3)) (16 * (2 + 5 * 2)) e := by
    refine ⟨hcp, by rw [he.x20, e0, hp.x3], fun u _ _ h27 => ?_, fun u _ _ h27 => ?_,
      fun w h20 _ => ?_, fun w h20 _ => ?_, hcp.src,
      fun d h => hblk d (by omega_using [h]), fun d h => ?_, hk _ (.inl rfl), hk _ (.inr rfl), ?_, ?_,
      by decide, by decide, ?_⟩
    · rw [exec_addImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h27, e27, BitVec.add_zero]
    · rw [exec_addImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h27, e27]
    · rw [exec_subImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h20, e27, show 16 * (1 + 5 * 3) = 256 from rfl,
        BitVec.add_sub_cancel]
    · rw [exec_subImm_x (by decide)]
      simp only [State.read, BitVec.setWidth_eq, h20, e27, show 16 * (2 + 5 * 2) = 192 from rfl]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_sub_cancel]
    · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hblk _ (by omega_using [h])
    · simpa only [BitVec.add_zero] using hwin 0 256 (by decide)
    · exact hwin 256 192 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [ekey]
      rcases hr with rfl | rfl | rfl
      · rw [esr]; exact hkey_st
      · rw [esb]
        simp only [keyR, scalarBuf]
        rw [hp.x3]
        exact Offset.disjoint _ (by decide) (by decide) (by decide)
      · rw [edr]; exact (hp.d_b.sub_right hkb).symm
  -- The accumulator, through `enter`.
  obtain hkey_enter : ∀ r ∈ enterR s, (keyR s).Disjoint r := by
    intro r hr
    simp only [enterR, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [keyR]
    rcases hr with rfl | rfl <;> rw [hx3] <;>
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
  obtain hea : Acc R a e :=
    ha.frame (fun r hr => he.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide))
      (fun d hd => rword_frame he.frame e0 hkey_enter d hd)
  -- The chunk.
  apply WP.seq
  refine (chunkWith_ok (sve := sve) e pre hea).mono fun g ⟨hg, hga⟩ => ?_
  obtain g0 : g.gpr .x0 = s.gpr .x0 := hg.x0.trans ((rebase_of (by decide)).trans e0)
  obtain g1 : g.gpr .x1 = s.gpr .x1 := hg.x1.trans ((rebase_of (by decide)).trans e1)
  obtain g2 : g.gpr .x2 = s.gpr .x2 := hg.x2.trans ((rebase_of (by decide)).trans e2)
  obtain g3 : g.gpr .x3 = s.gpr .x3 := hg.x3.trans ((rebase_of (by decide)).trans e3)
  obtain gfr : Frame [sr s, scalarBuf s, dr s] e.mem g.mem := by
    have f := hg.frame
    simp only [sr, scalarBuf, dr, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide),
      rebase_of (show Reg.x1 ∉ accRegs by decide), rebase_of (show Reg.x3 ∉ accRegs by decide),
      e0, e1, e3] at f
    exact f
  obtain grd : g.rd = s.rd := by rw [hg.rd, rebase_rd, he.rd]
  obtain gwr : g.wr = s.wr := by rw [hg.wr, rebase_wr, he.wr]
  -- What `enter` saved, kept by the chunk.
  obtain hsv : Spill.Saved (s.gpr .x3) s.gpr gpSlots g.mem :=
    he.saved.frame gfr fun p hp' r hr => by
      obtain hs : (⟨s.gpr .x3 + BitVec.ofNat 64 p.2, 8⟩ : Region).Sub (br s) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> exact Offset.sub_base _ (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_b.symm.sub_left hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.d_b.symm.sub_left hs
  have hvr (d : Nat) (hd : d = 128 ∨ d = 144) :
      g.mem.read (s.gpr .x3 + BitVec.ofNat 64 d) 16 = e.mem.read (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    obtain hs : (⟨s.gpr .x3 + BitVec.ofNat 64 d, 16⟩ : Region).Sub (br s) := by
      rcases hd with rfl | rfl <;> exact Offset.sub_base _ (by decide)
    refine gfr.read (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_b.symm.sub_left hs
    · rcases hd with rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
    · exact hp.d_b.symm.sub_left hs
  -- `leave`.
  rw [leave_eq]
  have hin (d n : Nat) (h : d + n ≤ 320) :
      InRegions (g.rd ++ g.wr) (g.gpr .x3 + BitVec.ofNat 64 d) n := by
    obtain ⟨r, hr, hc⟩ := hp.buffer d n h
    exact ⟨r, by rw [gwr]; exact List.mem_append_right _ hr, by rw [g3]; exact hc⟩
  refine WP.block_append_iff.mpr ((VG.Proof.ChaCha20.AArch64.Mixed8.restoreV_ok (s.v .v8) (s.v .v9)
    (hin 128 16 (by decide)) (hin 144 16 (by decide))
    (by rw [g3, hvr 128 (.inl rfl), he.v8]) (by rw [g3, hvr 144 (.inr rfl), he.v9])).mono
    fun w ⟨w8, w9, wg, wm, wrd, wwr, wsp⟩ => ?_)
  refine (Spill.restore_wp (b := .x3) (B := s.gpr .x3) (by rw [wg, g3]) (by decide) (by decide)
    (fun p hp' => ?_) (by rw [wm]; exact hsv)).mono fun u hu => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    have := hin
    rw [g3, ← wrd, ← wwr] at this
    rcases hp' with rfl | rfl | rfl <;> exact this _ 8 (by decide)
  have u_of (r : Reg) (h20 : r ≠ .x20) (h19 : r ≠ .x19) (h26 : r ≠ .x26) : u.gpr r = g.gpr r := by
    rw [hu.other r (by simp [h20, h19, h26]), wg]
  obtain um : u.mem = g.mem := by rw [hu.mem, wm]
  obtain hdis_enter : ∀ (R : Region), R.Disjoint (br s) → ∀ r ∈ enterR s, R.Disjoint r :=
    fun R hR r hr => hR.sub_right (henter r hr)
  obtain hsrc : source e = source s := by
    simp only [source, e0]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame he.frame (hdis_enter _ hp.st_b)
  obtain hsrcg : source (rebase e g) = source s := by
    simp only [source, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide)]
    exact hsrc
  refine ⟨by rw [u_of _ (by decide) (by decide) (by decide), g0],
    by rw [u_of _ (by decide) (by decide) (by decide), g1],
    by rw [u_of _ (by decide) (by decide) (by decide), g2],
    by rw [u_of _ (by decide) (by decide) (by decide), g3], fun r hr hna => ?_,
    by rw [hu.v, w8], by rw [hu.v, w9], by rw [hu.rd, wrd, grd], by rw [hu.wr, wwr, gwr],
    by rw [hu.sp, wsp, hg.sp, rebase_sp, he.sp], ?_, fun k hk => ?_, ?_, ?_⟩
  · by_cases h20 : r = .x20
    · subst h20; exact hu.gpr (.x20, 256) (by simp)
    by_cases h19 : r = .x19
    · subst h19; exact hu.gpr (.x19, 264) (by simp)
    by_cases h26 : r = .x26
    · subst h26; exact hu.gpr (.x26, 272) (by simp)
    rw [u_of r h20 h19 h26, hg.cs r hr h19 h26, rebase_of hna, he.gpr r h20]
  · simp only [source, um, u_of _ (show Reg.x0 ≠ .x20 by decide) (by decide) (by decide), g0]
    have hcn := hg.cnt
    simp only [source, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide), g0, e0] at hcn
    rw [hcn]
    simpa only [source, e0] using hsrc
  · have d := hg.data k hk
    simp only [rebase_mem, rebase_of (show Reg.x1 ∉ accRegs by decide), e1] at d
    rw [um, d, hsrcg, he.frame.bytes (R := dr s) (hdis_enter _ hp.d_b) (by show 512 ≤ 2 ^ 64; decide) hk]
  · rw [um]
    refine (he.frame.sub fun r hr => ⟨br s, by simp, henter r hr⟩).trans (gfr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sr s, by simp, fun _ h => h⟩
    · exact ⟨br s, by simp, hsb⟩
    · exact ⟨dr s, by simp, fun _ h => h⟩
  · have hwe (d n : Nat) (h : d + n ≤ 448) :
        bytesAt e.mem (s.gpr .x27 + BitVec.ofNat 64 d) n = bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 d) n :=
      bytesAt_frame he.frame (hdis_enter _ ((hp.win _ (by simp)).sub_left (Offset.sub_base _ h)))
        (by omega_using [h])
    obtain hwe0 := hwe 0 256 (by decide)
    rw [BitVec.add_zero] at hwe0
    rw [show 16 * (1 + 5 * 3) = 256 from rfl, show 16 * (2 + 5 * 2) = 192 from rfl, hwe0,
      hwe 256 192 (by decide), ← Poly1305.bytesAt_add] at hga
    refine hga.frame (fun r hr => ?_) (fun d _ => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact u_of _ (by decide) (by decide) (by decide)
    · simp only [Poly.rword, um, u_of _ (show Reg.x0 ≠ .x20 by decide) (by decide) (by decide)]

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

end


/-!
# ChaCha20-Poly1305 on AArch64: `open` from 449 to 511 bytes

`OpenPad.openMain`: after the prologue, the additional data and the lengths
block, `ctx[704, 1280)` is zeroed and the stream's arguments set (`args`), with
the keystream's buffer at `ctx + 256 + len` and the data's address in `x2`;
then `polyIn`, the chunk that computes the keystream of counters 1 to 8 into
the buffer while absorbing the data's first 448 bytes (`Stitch.bulkPad_ok`),
and `polyOut`; the data's address and its length are recovered from `x2`
and the buffer's address (`recover`); the rest of the data is absorbed with
its padding, then the lengths block; the data is XORed with the keystream
into the output (`xorKsWithDst_ok`), the buffer zeroed again, and the tag
computed.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenPad

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenPad
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_sub wp_mov wp_lsr wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ZeroedAt zeroAt_ok kpAt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)

variable {e : Bool}

/-- `OpenPad.zero`: `ctx[704, 1280)` zeroed. -/
theorem zero_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block zero) s fun s' => Kept [sub s₀ 704 576] s s' ∧
      ZeroedAt (cx s₀) 704 36 s.mem s'.mem ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain hv0 : ∀ r ∈ preservedV, r ≠ .v0 := by decide
  refine WP.mono (zeroAt_ok (b := 704) (J := 36) (by decide) (by decide) hx21 fun a ha => by
    rw [hwr]; exact hp.in_ctx (a := 704 + a) (by omega_arith)) fun s' ⟨g, rd, wr, sp, v, z⟩ =>
      ⟨Kept.of (fun r _ => by rw [g]) sp rd wr (z.frame (by decide)), z,
        fun r hr => by rw [v r (hv0 r hr)]⟩

/-- The stream's arguments, with the counter set to 1 and the buffer at
`ctx + 256 + len`. -/
theorem args_ok {s₀ s : State} (hp : APre e s₀) (h : Inv e s₀ s) :
    WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) (256 + L s₀) ∧ s'.gpr .x2 = dp s₀ ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ Kept [sub s₀ 64 64] s s' := by
  obtain o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  obtain core : WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) (256 + L s₀) ∧ s'.gpr .x2 = dp s₀ ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
      wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, one32]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.x21,
        h.x23, hL, off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x22]
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core rfl)
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The data's address and length, and the rest after 448 bytes, from
`polyOut false`'s `x22` (the buffer) and `x23` (the data). -/
theorem recover_ok {s₀ s : State} (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    (hx21 : s.gpr .x21 = cx s₀) (hx22 : s.gpr .x22 = off (cx s₀) (256 + L s₀))
    (hx23 : s.gpr .x23 = dp s₀) :
    WP isa (.block recover) s fun s' => s'.gpr .x22 = dp s₀ ∧
      s'.gpr .x23 = BitVec.ofNat 64 (L s₀) ∧ s'.gpr .x24 = dp s₀ + BitVec.ofNat 64 448 ∧
      s'.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448) ∧
      (∀ r, r ∉ [Reg.x22, .x23, .x24, .x25] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_sub fun s₁ u₁ => wp_subImm (by decide) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain x25₂ : s₂.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [u₂.gpr, u₁.gpr, hx22, hx21, off, Offset.add_sub_cancel_left, Offset.ofNat_sub_ofNat (by omega_arith),
      show 256 + L s₀ - 704 = L s₀ - 448 by omega_arith]
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hx23]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), x25₂, ← BitVec.ofNat_add,
      show L s₀ - 448 + 448 = L s₀ by omega_arith]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx23]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x25₂]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h22, h23, h24, h25⟩ := hr
    rw [u₅.other _ h23, u₄.other _ h24, u₃.other _ h22, u₂.other _ h25, u₁.other _ h25]

/-- `xorKs`'s setup: the data in `x9`, its destination (`Q`: the data itself,
or `x28` after it if `to`) in `x15`, the keystream at `ctx + 256 + len` in
`x10`, and `len / 16` in `x11`. -/
theorem xsetup_ok {s₀ s : State} (to : Bool) {Q : Addr} (hx21 : s.gpr .x21 = cx s₀)
    (hx22 : s.gpr .x22 = dp s₀) (hx23 : s.gpr .x23 = BitVec.ofNat 64 (L s₀))
    (hQ : cond to (dp s₀ + s.gpr .x28) (dp s₀) = Q) :
    WP isa (.block [mov .x9 .x22, Short.dstOf to, .add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256,
        .lsr .x .x11 .x23 4]) s
      fun s' => s'.gpr .x9 = dp s₀ + BitVec.ofNat 64 0 ∧ s'.gpr .x15 = Q + BitVec.ofNat 64 0 ∧
        s'.gpr .x10 = kpAt s₀ (256 + L s₀) ∧ s'.gpr .x11 = BitVec.ofNat 64 (L s₀ / 16) ∧
        Kept [] s s' ∧ ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x15 → s'.gpr r = s.gpr r := by
  obtain hn : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain h : WP isa (.block [mov .x9 .x22, Short.dstOf to, .add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256,
      .lsr .x .x11 .x23 4]) s fun s' =>
      s'.gpr .x9 = dp s₀ + BitVec.ofNat 64 0 ∧ s'.gpr .x15 = Q + BitVec.ofNat 64 0 ∧
      s'.gpr .x10 = kpAt s₀ (256 + L s₀) ∧ s'.gpr .x11 = BitVec.ofNat 64 (L s₀ / 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x15 → s'.gpr r = s.gpr r := by
    obtain tail : ∀ s₂ : State, s₂.gpr .x9 = dp s₀ → s₂.gpr .x15 = Q → s₂.gpr .x21 = cx s₀ →
        s₂.gpr .x23 = BitVec.ofNat 64 (L s₀) → s₂.rd = s.rd → s₂.wr = s.wr → s₂.mem = s.mem →
        (∀ r, r ≠ .x9 → r ≠ .x15 → s₂.gpr r = s.gpr r) →
        WP isa (.block [.add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256, .lsr .x .x11 .x23 4]) s₂ fun s' =>
          s'.gpr .x9 = dp s₀ + BitVec.ofNat 64 0 ∧ s'.gpr .x15 = Q + BitVec.ofNat 64 0 ∧
          s'.gpr .x10 = kpAt s₀ (256 + L s₀) ∧ s'.gpr .x11 = BitVec.ofNat 64 (L s₀ / 16) ∧
          s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
          ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x15 → s'.gpr r = s.gpr r :=
      fun s₂ x9₂ x15₂ x21₂ x23₂ rd₂ wr₂ m₂ g₂ => wp_add fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
        wp_lsr (by decide) fun s₅ u₅ => WP.block_nil
        ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x9₂, BitVec.add_zero],
          by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x15₂, BitVec.add_zero],
          by rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, x21₂, x23₂, kpAt, off, BitVec.add_assoc,
            ← BitVec.ofNat_add, Nat.add_comm],
          by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), x23₂, shr4_ofNat hn],
          by rw [u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂],
          by rw [u₅.mem, u₄.mem, u₃.mem, m₂],
          fun r h9 h10 h11 h15 => by rw [u₅.other _ h11, u₄.other _ h10, u₃.other _ h10, g₂ r h9 h15]⟩
    refine wp_mov fun s₁ u₁ => ?_
    cases to
    · refine wp_mov fun s₂ u₂ => tail s₂ (by rw [u₂.other _ (by decide), u₁.gpr, hx22])
        (by rw [u₂.gpr, u₁.gpr, hx22]; exact hQ) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx23]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr]) (by rw [u₂.mem, u₁.mem])
        fun r h9 h15 => by rw [u₂.other _ h15, u₁.other _ h9]
    · refine wp_add fun s₂ u₂ => tail s₂ (by rw [u₂.other _ (by decide), u₁.gpr, hx22])
        (by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hx22]; exact hQ)
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21])
        (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx23]) (by rw [u₂.rd, u₁.rd])
        (by rw [u₂.wr, u₁.wr]) (by rw [u₂.mem, u₁.mem])
        fun r h9 h15 => by rw [u₂.other _ h15, u₁.other _ h9]
  exact WP.mono (WP.kept h (by cases to <;> rfl)) fun s' ⟨⟨h9, h15, h10, h11, hrd, hwr, hm, hg'⟩, hg, hsp⟩ =>
    ⟨h9, h15, h10, h11, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hg'⟩

/-- `out`: the destination's distance from the data (`x2 - x27`) into `x15`
and then `x28`, the data (`x27`) back in `x2`, and `polyOut false`. -/
theorem out_ok {s₀ : State} (hp : APre e s₀) {s : State} (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block out) s fun u =>
      (((s.gpr .x23).toNat ≤ 4 → Poly1305.AArch64.Radix64.hval u = hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.gpr .x2 - s.gpr .x27 ∧ u.gpr .x22 = s.gpr .x1 ∧ u.gpr .x23 = s.gpr .x27 ∧
      (∀ r, r ∉ [Reg.x2, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x27,
        .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ∧ u.v = s.v ∧ u.sp = s.sp := by
  show WP isa (.block ([.sub .x .x15 .x2 .x27, mov .x2 .x27] ++ (polyOut false ++ [mov .x28 .x15]))) s _
  refine WP.block_append (wp_subS fun s₁ u₁ sp₁ v₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_movS
    fun s₂ u₂ sp₂ v₂ => WP.block_nil ?_)
  obtain g₂ : ∀ r, r ≠ .x2 → r ≠ .x15 → s₂.gpr r = s.gpr r := fun r h2 h15 => by
    rw [u₂.other r h2, u₁.other r h15]
  refine WP.block_append (WP.mono (polyOut_ok hp false (by rw [g₂ _ (by decide) (by decide), hx0])
    (by rw [u₂.rd, u₁.rd, hrd]) (by rw [u₂.wr, u₁.wr, hwr]))
    fun s₃ ⟨⟨hv, m, x21, x27, _, x22, x23, g, rd, wr⟩, vv, sp, _, _⟩ => ?_)
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun s₄ u₄ sp₄ v₄ => WP.block_nil ?_
  have o4 : ∀ r, r ≠ .x28 → s₄.gpr r = s₃.gpr r := u₄.other
  obtain ha : hacc s₂ = hacc s := by
    simp only [hacc, g₂ .x21 (by decide) (by decide), g₂ .x22 (by decide) (by decide),
      g₂ .x23 (by decide) (by decide)]
  refine ⟨⟨fun h => ?_, ?_, by rw [o4 _ (by decide), x21], by rw [o4 _ (by decide), x27, u₂.mem, u₁.mem], ?_,
    by rw [o4 _ (by decide), x22]; show s₂.gpr .x1 = _; rw [g₂ _ (by decide) (by decide)],
    by rw [o4 _ (by decide), x23]; show s₂.gpr .x2 = _; rw [u₂.gpr, u₁.other _ (by decide)], fun r hr => ?_,
    by rw [u₄.rd, rd, u₂.rd, u₁.rd], by rw [u₄.wr, wr, u₂.wr, u₁.wr]⟩, by rw [v₄, vv, v₂, v₁],
    by rw [sp₄, sp, sp₂, sp₁]⟩
  · rw [g₂ .x23 (by decide) (by decide)] at hv
    show (s₄.gpr .x4).toNat + 2 ^ 64 * (s₄.gpr .x5).toNat + 2 ^ 128 * (s₄.gpr .x6).toNat = _
    rw [o4 _ (by decide), o4 _ (by decide), o4 _ (by decide), ← ha]; exact hv h
  · rw [u₄.mem, m, u₂.mem, u₁.mem, o4 _ (by decide), o4 _ (by decide), o4 _ (by decide)]
  · rw [u₄.gpr, g .x15 (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [o4 r (fun h => hr (by subst h; simp)), g r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])),
      g₂ r (fun h => hr (by subst h; simp)) (fun h => hr (by subst h; simp))]

theorem bulkPad_otherV (sve : Bool) :
    (Stitch.bulkPad sve).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases sve
  · show Stitch.bulkPadNeon.allInstrs _ = true; lit_decide
  · show Stitch.bulkPadSve.allInstrs _ = true; lit_decide

/-- `bulkPad`'s precondition, after `args` and `polyIn`. -/
theorem padPre_of {s₀ s : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = off (cx s₀) (256 + L s₀))
    (hx27 : s.gpr .x27 = dp s₀) (hx3 : s.gpr .x3 = off (cx s₀) 128) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : Stitch.PadPre s := by
  obtain hsr : VG.Proof.ChaCha20.AArch64.Mixed8.sr s = sub s₀ 64 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, hx0]
  obtain hbr : VG.Proof.ChaCha20.AArch64.Mixed8.br s = sub s₀ 128 320 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.br, hx3]
  obtain hdr : VG.Proof.ChaCha20.AArch64.Mixed8.dr s = sub s₀ (256 + L s₀) 512 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.dr, hx1]
  obtain hw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  refine ⟨fun k => ?_, fun k => ?_, ?_, fun d n h => ?_, fun d n h => ?_, ?_, ?_, ?_, ?_,
    fun d h => ?_, fun r hr => ?_⟩
  · rw [hw, hx0, Short.off_add]; exact hp.in_ctx' (by have := k.isLt; omega_arith)
  · rw [hw, hx0, Short.off_add]; exact hp.in_ctx' (by have := Nat.mod_lt k.val (show 4 > 0 by decide); omega_arith)
  · rw [hwr, hx0, Short.off_add]; exact hp.in_ctx (by decide)
  · rw [hwr, hx3, Short.off_add]; exact hp.in_ctx (by omega_arith)
  · rw [hwr, hx1, Short.off_add]; exact hp.in_ctx (by omega_arith)
  · rw [hsr, hbr]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [hsr, hdr]; exact sub_disj s₀ (by omega_arith) (by lit_omega) (by omega_arith)
  · rw [hdr, hbr]; exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
  · rw [hx3, hx0]; exact (off_off _ 64 64).symm
  · rw [hx27, hw]
    exact ⟨dR s₀, hp.d_in, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [hx27]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain hs : (⟨dp s₀, 448⟩ : Region).Sub (dR s₀) := Region.sub_prefix (by omega_arith)
    rcases hr with rfl | rfl
    · rw [hsr]; exact (hp.c_d.symm.sub_left hs).sub_right (sub_ctx s₀ (by lit_omega))
    · rw [hbr]; exact (hp.c_d.symm.sub_left hs).sub_right (sub_ctx s₀ (by lit_omega))

/-- What `open` leaves after the chunk and `recover`, from `s` after the
lengths. -/
structure Crypted (s₀ s : State) (key msg : List Byte) (u : State) : Prop where
  inv : Inv0 false s₀ u
  x22 : u.gpr .x22 = dp s₀
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀)
  x24 : u.gpr .x24 = dp s₀ + BitVec.ofNat 64 448
  x25 : u.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448)
  frame : Frame [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576] s.mem u.mem
  ks : ∀ i < L s₀, u.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) =
    (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0
  mac : Repr u.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) 448)
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem crypt_ok (sve : Bool) {s₀ : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    {s : State} (h : Inv false s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg)
    {rest : Prog isa} {Q : State → Prop} (k : ∀ u, Crypted s₀ s key msg u → WP isa rest u Q) :
    WP isa (.seq (.block (zero ++ args ++ polyIn ++ [mov .x27 .x2, .add .x .x2 .x2 .x28])) (.seq (Stitch.bulkPad sve)
      (.seq (.block (out ++ recover)) rest))) s Q := by
  obtain hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt (s₀.gpr .x5).isLt
  refine WP.seq (WP.block_append (WP.block_append (WP.block_append (WP.mono (zero_ok hp h.x21 h.wr)
    fun s₄ ⟨k₄, z₄, v₄⟩ => ?_))))
  obtain i₄ : Inv false s₀ s₄ := h.step1 k₄ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (WP.preservedV (args_ok hp i₄) (by lit_decide))
    fun s₅ ⟨⟨m₅, x0₅, x1₅, x2₅, x3₅, k₅⟩, v₅⟩ => ?_
  obtain i₅ : Inv false s₀ s₅ := i₄.step1 k₅ (by omega_arith) (by omega_arith) (by omega_arith)
  refine (polyIn_ok hp i₅.x21 i₅.rd i₅.wr).mono
    fun t₆ ⟨⟨a21, a22, a23, mt, gt, rdt, wrt⟩, vt, spt, _, _⟩ =>
      VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun s₆' u₆' sp₆'' v₆'' => wp_addS fun s₆ u₆ sp₆' v₆' =>
        WP.block_nil ?_
  obtain g₆ : ∀ r, r ∉ [Reg.x2, .x21, .x22, .x23, .x24, .x25, .x27] → s₆.gpr r = s₅.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.1, u₆'.other r hr.2.2.2.2.2.2,
      gt r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1])]
  obtain m₆ : s₆.mem = memIn s₅.mem (cx s₀) (s₅.gpr .x27) (s₅.gpr .x28) := by rw [u₆.mem, u₆'.mem, mt]
  obtain rd₆ : s₆.rd = s₅.rd := by rw [u₆.rd, u₆'.rd, rdt]
  obtain wr₆ : s₆.wr = s₅.wr := by rw [u₆.wr, u₆'.wr, wrt]
  obtain v₆ : s₆.v = s₅.v := by rw [v₆', v₆'', vt]
  obtain sp₆ : s₆.sp = s₅.sp := by rw [sp₆', sp₆'', spt]
  obtain x0₆ : s₆.gpr .x0 = off (cx s₀) 64 := by rw [g₆ _ (by decide), x0₅]
  obtain x1₆ : s₆.gpr .x1 = off (cx s₀) (256 + L s₀) := by rw [g₆ _ (by decide), x1₅]
  obtain x28₅ : s₅.gpr .x28 = s₀.gpr .x28 := i₅.un .x28 (by decide)
  obtain x2₆ : s₆.gpr .x2 = dp s₀ + s₀.gpr .x28 := by
    rw [u₆.gpr, u₆'.other _ (by decide), u₆'.other _ (by decide), gt _ (by decide), gt _ (by decide), x2₅, x28₅]
  obtain x27₆ : s₆.gpr .x27 = dp s₀ := by rw [u₆.other _ (by decide), u₆'.gpr, gt _ (by decide), x2₅]
  obtain x3₆ : s₆.gpr .x3 = off (cx s₀) 128 := by rw [g₆ _ (by decide), x3₅]
  obtain hr₅ : Repr s₅.mem (off (cx s₀) 448) key msg :=
    Repr.frame k₅.frame (by rdisj_all) (Repr.frame k₄.frame (by rdisj_all) hr)
  obtain ha := acc_in hr₅ x0₆ (by rw [u₆.other _ (by decide), u₆'.other _ (by decide), a21])
    (by rw [u₆.other _ (by decide), u₆'.other _ (by decide), a22])
    (by rw [u₆.other _ (by decide), u₆'.other _ (by decide), a23]) m₆
  obtain pre : Stitch.PadPre s₆ := padPre_of hp h449 h511 x0₆ x1₆ x27₆ x3₆ (rd₆.trans i₅.rd)
    (wr₆.trans i₅.wr)
  -- The chunk.
  refine WP.seq ((WP.otherV (Stitch.bulkPad_ok (sve := sve) s₆ pre ha) (bulkPad_otherV sve)).mono
    fun s₇ ⟨hB, ov₇⟩ => ?_)
  -- `polyOut` and `recover`.
  obtain x27₇ : s₇.gpr .x27 = dp s₀ := by rw [hB.cs _ (by decide) (by decide), x27₆]
  refine WP.seq (WP.block_append ((out_ok hp (by rw [hB.x0, x0₆])
    (by rw [hB.rd, rd₆, i₅.rd]) (by rw [hB.wr, wr₆, i₅.wr])).mono
    fun s₈ ⟨⟨hv₈, m₈, x21₈, x27₈, x28₈, x22₈, x23₈, g₈, rd₈, wr₈⟩, vv₈, sp₈⟩ => ?_))
  refine (WP.preservedV (WP.withSp (recover_ok h449 h511 x21₈
    (by rw [x22₈, hB.x1, x1₆])
    (by rw [x23₈, x27₇]))) (by lit_decide)).mono
    fun s₉ ⟨⟨⟨x22₉, x23₉, x24₉, x25₉, g₉, m₉, rd₉, wr₉⟩, sp₉⟩, v₉⟩ => k s₉ ?_
  -- Memory.
  obtain hsr : VG.Proof.ChaCha20.AArch64.Mixed8.sr s₆ = sub s₀ 64 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, x0₆]
  obtain hbr : VG.Proof.ChaCha20.AArch64.Mixed8.br s₆ = sub s₀ 128 320 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.br, x3₆]
  obtain hdr : VG.Proof.ChaCha20.AArch64.Mixed8.dr s₆ = sub s₀ (256 + L s₀) 512 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.dr, x1₆]
  obtain f₅₆ : Frame (inR s₀) s₅.mem s₆.mem := by rw [m₆]; exact memIn_frame _ _ _
  obtain f₆₇ : Frame [sub s₀ 64 64, sub s₀ 128 320, sub s₀ (256 + L s₀) 512] s₆.mem s₇.mem := by
    obtain f := hB.frame; rw [hsr, hbr, hdr] at f; exact f
  obtain f₇₈ : Frame [sub s₀ 448 24] s₇.mem s₈.mem := by rw [m₈]; exact storeHm_frame _ _ _ _ _
  obtain hF : Frame [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576] s.mem s₉.mem := by
    have e (r : Region) (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
        ∃ r' ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576], Region.Sub r r' :=
      ⟨sub s₀ 64 408, by simp, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩
    rw [m₉]
    refine ((k₄.frame.sub ?_).trans (k₅.frame.sub ?_)).trans
      ((f₅₆.sub ?_).trans ((f₆₇.sub ?_).trans (f₇₈.sub ?_))) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · exact ⟨sub s₀ 704 576, by simp, hr ▸ fun _ h => h⟩
    · exact e r 64 64 (by decide) (by decide) hr
    · rcases hr with hr | hr
      · exact e r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 32 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact e r 64 64 (by decide) (by decide) hr
      · exact e r 128 320 (by decide) (by decide) hr
      · subst hr; exact ⟨sub s₀ 704 576, by simp, sub_sub s₀ (by omega_arith) (by omega_arith) (by lit_omega)⟩
    · exact e r 448 24 (by decide) (by decide) hr
  obtain hFd : ∀ r ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact data_ctx hp (by lit_omega)
  -- The callee-saved registers.
  have r₇ (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₇.mem.readW (off (cx s₀) d) 64 = s₆.mem.readW (off (cx s₀) d) 64 := by
    refine f₆₇.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      exact sub_disj s₀ (by omega_arith) (by lit_omega) (by omega_arith)
  obtain un₉ : ∀ r ∈ untouched, s₉.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h9 : r ∉ [Reg.x22, .x23, .x24, .x25])
        (h8 : r ∉ [Reg.x2, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x27,
          .x28])
        (h6 : r ∉ [Reg.x2, .x21, .x22, .x23, .x24, .x25, .x27]) (hu : r ∈ untouched) :
        s₉.gpr r = s₀.gpr r := by
      rw [g₉ r h9, g₈ r h8, hB.cs r hc hn, g₆ r h6, i₅.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 32 ∨ d = 40) (hu : r ∈ untouched)
        (hx : s₈.gpr r = s₇.mem.readW (off (cx s₀) d) 64)
        (hm : (memIn s₅.mem (cx s₀) (s₅.gpr .x27) (s₅.gpr .x28)).readW (off (cx s₀) d) 64 = s₅.gpr r) :
        s₉.gpr r = s₀.gpr r := by
      rw [g₉ r (by rcases hd with rfl | rfl <;> simp only [untouched, List.mem_cons,
        List.not_mem_nil, or_false] at hu <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide),
        hx, r₇ d hd, m₆, hm, i₅.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 32 (.inl rfl) (by decide) x27₈ (memIn_800 _ _ _ _)
    · rw [g₉ _ (by decide), x28₈, hB.x2, x27₇, x2₆, BitVec.add_comm (dp s₀), BitVec.add_sub_cancel]
  -- The keystream.
  obtain st₅ : stateAt s₅.mem (off (cx s₀) 64) = initState (K s₀) 1 (N s₀) := by
    rw [m₅, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      stateAt_frame k₄.frame (by rdisj_all), hst, set12_initState]
  obtain st₆ : VG.Proof.ChaCha20.AArch64.Mixed8.source s₆ = initState (K s₀) 1 (N s₀) := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.source, x0₆]
    rw [stateAt_frame f₅₆ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), st₅]
  obtain ks₉ : ∀ i < L s₀, s₉.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := by
    intro i hi
    obtain hR : ∀ r ∈ [sub s₀ 448 24], (sub s₀ (256 + L s₀) 512).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
    rw [m₉, f₇₈.bytes (R := sub s₀ (256 + L s₀) 512) hR (by show 512 ≤ 2 ^ 64; decide)
      (by show i < 512; omega_arith)]
    obtain d := hB.data i (by omega_arith)
    rw [x1₆, st₆] at d
    rw [d]
    -- The buffer was zero.
    obtain z : s₆.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) = 0 := by
      rw [f₅₆.bytes (R := sub s₀ (256 + L s₀) 512) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega))
          (by show 512 ≤ 2 ^ 64; decide) (by show i < 512; omega_arith),
        k₅.frame.bytes (R := sub s₀ (256 + L s₀) 512) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith),
        Short.off_add, show 256 + L s₀ + i = 704 + (L s₀ - 448 + i) by omega_arith]
      exact z₄.byte (k := L s₀ - 448 + i) (by omega_arith) (by decide)
    rw [z, VG.Proof.ChaCha20.keystream_getD _ hi]
    simp
  -- The accumulator.
  obtain hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have ac₇ := hB.acc
  obtain hX := hv₈ ac₇.h2
  rw [show hacc s₇ = Poly.hval s₇ from rfl, ac₇.h, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr.2.1
  rw [k24] at hr1
  refine ⟨⟨by rw [g₉ _ (by decide), x21₈], un₉, by rw [sp₉, sp₈, hB.sp, sp₆, i₅.sp],
      by rw [rd₉, rd₈, hB.rd, rd₆, i₅.rd], by rw [wr₉, wr₈, hB.wr, wr₆, i₅.wr],
      h.saved.frame hF ?_, h.frame.trans (hF.sub ?_)⟩, x22₉, x23₉, x24₉, x25₉, hF, ks₉, ⟨?_, ?_, ?_⟩,
    fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := hr.1; omega_arith
  · rw [k24, bytesAt_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
      (by lit_omega)]
    exact hr1
  · rw [m₉, m₈, Poly1305.AArch64.storeHm_acc]
    show Poly1305.AArch64.Radix64.hval s₈ = _
    rw [hX, Poly1305.accumulate_append hr.1]
    refine congrArg (VG.Proof.Poly1305.absorbAll _ _) ?_
    rw [x27₆, prefix_frame f₅₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) (by omega_arith),
      prefix_frame k₅.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) (by omega_arith),
      prefix_frame k₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) (by omega_arith)]
  · have e7 : s₇.v r = s₆.v r := by
      by_cases h8 : r = .v8
      · subst h8; exact hB.v8
      by_cases h9 : r = .v9
      · subst h9; exact hB.v9
      exact ov₇ r hr h8 h9
    rw [v₉ r hr, vv₈, e7, v₆]
    exact (v₅ r hr).trans (v₄ r hr)

theorem openMain_ok (sve : Bool) {s₀ : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀)
    (h511 : L s₀ ≤ 511) : WP isa (OpenPad.openMain sve) s₀ (MainO s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold OpenPad.openMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  obtain i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  obtain R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  -- The keystream with the first 448 bytes absorbed.
  refine crypt_ok sve hp h449 h511 i₃ st₃ R₃ fun s₉ hc => ?_
  -- The rest of the data.
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcAt hp (p := 448) (by omega_arith)) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x24 hc.x25) (by lit_decide))
    fun s₁₀ ⟨⟨k₁₀, r₁₀⟩, v₁₀⟩ => ?_)
  obtain i₁₀ := mac_inv0 hc.inv k₁₀
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₀) (by lit_decide))
    fun s₁₁ ⟨⟨i₁₁, k₁₁, r₁₁⟩, v₁₁⟩ => ?_)
  obtain x22₁₁ : s₁₁.gpr .x22 = dp s₀ := by
    rw [k₁₁.cs _ (pres .x22) (pres30 .x22), k₁₀.cs _ (pres .x22) (pres30 .x22), hc.x22]
  obtain x23₁₁ : s₁₁.gpr .x23 = BitVec.ofNat 64 (L s₀) := by
    rw [k₁₁.cs _ (pres .x23) (pres30 .x23), k₁₀.cs _ (pres .x23) (pres30 .x23), hc.x23]
  -- The data decrypted.
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsWithDst_ok hp hp.o (k := 256 + L s₀) (o := 0) (n := L s₀)
    (by omega_arith) (by omega_arith) x23₁₁ i₁₁.rd i₁₁.wr (xsetup_ok true i₁₁.x21 x22₁₁ x23₁₁
      (show dp s₀ + s₁₁.gpr .x28 = dp s₀ + s₀.gpr .x28 by rw [i₁₁.un .x28 (by decide)]))) (by lit_decide))
    fun s₁₂ ⟨⟨k₁₂, d₁₂, _, _⟩, v₁₂⟩ => ?_)
  obtain i₁₂ : Inv0 false s₀ s₁₂ := i₁₁.step k₁₂ (oR_inv hp).1 (oR_inv hp).2
  -- The keystream zeroed.
  refine WP.seq (WP.mono (zero_ok hp i₁₂.x21 i₁₂.wr) fun s₁₃ ⟨k₁₃, _, v₁₃⟩ => ?_)
  obtain i₁₃ : Inv0 false s₀ s₁₃ := i₁₂.step k₁₃
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₁₃ (out := 48) (by omega_arith)) (by lit_decide))
    fun s₁₄ ⟨⟨k₁₄, tag₁₄⟩, v₁₄⟩ => ?_
  -- The tag computed.
  obtain hR : ∀ r ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576],
      (⟨dp s₀ + BitVec.ofNat 64 448, L s₀ - 448⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hp.c_d.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (sub_ctx s₀ (by lit_omega))
  obtain R₁₀ := r₁₀ _ _ hc.mac
  rw [bytesAt_frame hc.frame hR (by omega_arith), List.append_assoc, split_pad (by decide) (by omega_arith),
    bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
    bytesAt_frame h₁.fine (by rdisj_all) hL'] at R₁₀
  obtain R₁₃ := Repr.frame k₁₃.frame (by rdisj_all) (Repr.frame k₁₂.frame (by rdisj_all) (r₁₁ _ _ R₁₀))
  obtain T₁₄ := tag₁₄ _ _ R₁₃
  obtain L₁₀ : bytesAt s₁₀.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₀.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₁₀, hA] at T₁₄
  refine ⟨i₁₃.step k₁₄ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₁₄ r hr).trans ((v₁₃ r hr).trans
      ((v₁₂ r hr).trans ((v₁₁ r hr).trans ((v₁₀ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₁₄]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  -- The data decrypted.
  · have hd₁₁ : ∀ i < L s₀, s₁₁.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [data_frame k₁₁.frame (by rdisj_all) hi, data_frame k₁₀.frame (by rdisj_all) hi,
          data_frame hc.frame (by rdisj_all) hi, data_frame k₃.frame (by rdisj_all) hi,
          data_frame k₂.frame (by rdisj_all) hi, data_frame h₁.fine (by rdisj_all) hi]
    obtain hk₁₁ : ∀ i < L s₀, s₁₁.mem (kpAt s₀ (256 + L s₀) + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun i hi => by
      obtain hR' : ∀ r ∈ macR s₀, (sub s₀ (256 + L s₀) 512).Disjoint r := by
        intro r hr; simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
      rw [k₁₁.frame.bytes (R := sub s₀ (256 + L s₀) 512) hR' (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith),
        k₁₀.frame.bytes (R := sub s₀ (256 + L s₀) 512) hR' (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith)]
      exact hc.ks i hi
    rw [bytesAt_frame k₁₄.frame (by rdisj_all) hL', bytesAt_frame k₁₃.frame (by rdisj_all) hL',
      encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      obtain hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      obtain hDl : (bytesAt s₀.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
      obtain e1 : (bytesAt s₁₂.mem (op false s₀) (L s₀))[i] = s₁₂.mem (op false s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      obtain e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [D, bytesAt]
      obtain e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length).length,
          (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length)[i] =
            (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
        rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, D, hDl]
      rw [List.getElem_zipWith, e1, e2, e3]
      obtain d := d₁₂ i hi
      simp only [Nat.zero_add] at d
      rw [d, hd₁₁ i hi, hk₁₁ i hi]

/-- `open` from `Short.lo` to 511 bytes: `ShortRest.lean`'s code up to
`Pad.threshold`, `OpenPad.openMain` from 449 bytes, and `Pad.openMain` between
them. -/
theorem openRoute_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 1 ≤ L s₀) (h511 : L s₀ ≤ 511) : WP isa (openRoute v.callee) s₀ (MainO s₀) := by
  unfold openRoute
  refine WP.seq (WP.mono (Pad.split_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  obtain hp₁ := Short.APre.agree ag hp
  obtain hL₁ : L s₁ = L s₀ := by rw [L, L, ag.gpr .x5 (by decide) (by decide)]
  refine WP.ite (decide (L s₀ ≤ Pad.threshold v.callee.sve)) (Pad.split_eval h511 x9) (fun _ => ?_)
    (fun hgt => ?_)
  · exact WP.mono (ShortRest.openMain_ok v hp₁ (by omega_arith)) fun _ h => Short.MainO.agree ag h
  obtain hgt' := of_decide_eq_false hgt
  cases hs : v.callee.sve
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hs] at hgt'
    exact WP.mono (openMain_ok false hp₁ (by simp only [Pad.threshold, Bool.false_eq_true, ↓reduceIte] at hgt'; omega_arith) (by omega_arith))
      fun _ h => Short.MainO.agree ag h
  · simp only [↓reduceIte]
    refine WP.seq (WP.mono (Pad.split_ok false s₁) fun s₂ ⟨ag₂, x92⟩ => ?_)
    obtain hp₂ := Short.APre.agree ag₂ hp₁
    obtain hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
    refine WP.ite (decide (L s₁ ≤ Pad.threshold false)) (Pad.split_eval (by omega_arith) x92) (fun _ => ?_)
      (fun hgt₂ => ?_)
    · exact WP.mono (Pad.openMain_ok v hp₂ (by omega_arith))
        fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
    · have := of_decide_eq_false hgt₂
      simp only [Pad.threshold, Bool.false_eq_true, ↓reduceIte] at this
      exact WP.mono (openMain_ok true hp₂ (by omega_arith) (by omega_arith))
        fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)

end VG.Proof.ChaCha20Poly1305.AArch64.OpenPad

end

end


/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Correctness (`Correct.lean`, and `Stitched/` for the eight-block stream's
own code), constant time, and a state satisfying the precondition: of `seal`
and of `open`'s body (`openCode`), which decrypts from the source (`x4`) to
the destination (`x8`), and of the functions: `open` (`openInPlace`, the
destination the data) and `open_to` (`openTo`, the destination from `x6` and
`tag` and `work` from the stack). Each is proven with its working space as its
last argument (`sealScratchContract`, `openZeroScratchContract`,
`openToScratchContract`), and then of the functions, which allocate it in a
frame of 1280 bytes (`seal`) or 1312 (`open` and `open_to`, which also save
the destination, `len` and our caller's `x28` after the context) on the stack
and wipe its first 768 after the code (`Verified.stackScratchWiped`,
`Verified.stackArgScratchWipedPre`). `open`'s and `open_to`'s code is proven
with permission to write only the destination, the context and those 32
bytes, which their working space covers (`RegionModel.verified_narrowTo`).

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards). The address of `tag`, which no register can
keep through the eight-block stream's code, is saved in the context, so the
analysis, which knows nothing of memory, checks the code up to the tag
(`sealMainCode`, `openMainCode`) and the rest (`sealTail`, `openTail`)
separately: between them, correctness says that both runs load the same
address, from the same place (`MainS`, `MainO`), and the rest is checked with
it public.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData decrypt)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h => hr r (VG.AArch64.Taint.mem_ofRegs.mp h)⟩) hc

/-! ## Correctness -/

theorem sealCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    sealCode c stitched = .seq (sealMainCode c stitched) sealTail := by
  cases stitched <;> rfl

theorem openCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    openCode c stitched = .seq (.block saveData) (.seq (openMainCode c stitched) openTail) := by
  cases stitched <;> rfl

theorem sealMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealMainCode v.callee v.stitched) s₀ (MainS s₀) := by
  unfold sealMainCode
  refine WP.seq (WP.mono (Short.check_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  obtain hp₁ := Short.APre.agree ag hp
  refine WP.ite (decide (Short.lo v.callee.sve ≤ L s₀ ∧ L s₀ ≤ 511)) (Short.check_eval x9) (fun h => ?_) (fun hn => ?_)
  · have hlo : 1 ≤ L s₁ := by
      have := (of_decide_eq_true h).1
      have : 1 ≤ Short.lo v.callee.sve := by cases v.callee.sve <;> decide
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega_arith
    obtain h511 : L s₁ ≤ 511 := by
      have := (of_decide_eq_true h).2
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega_using [this]
    exact WP.mono (Pad.sealRoute_ok v hp₁ hlo h511) fun _ h => Short.MainS.agree ag h
  · split
    · refine WP.seq (WP.mono (OpenKey.routeKey_ok v.callee.sve true s₁) fun s₂ ⟨ag₂, x9₂, x10₂⟩ => ?_)
      obtain hp₂ := Short.APre.agree ag₂ hp₁
      refine WP.ite (decide (Short.inRoute v.callee.sve true (L s₁))) (Short.route_eval x9₂)
        (fun h => ?_) (fun _ => ?_)
      rotate_left
      · have hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
        refine WP.iteCold_iff.mpr (WP.ite (decide (keyLo v.callee.sve true ≤ L s₁ ∧ L s₁ ≤ 704))
          (OpenKey.key_eval x10₂) (fun hk => ?_) (fun _ => ?_))
        · have hk' := of_decide_eq_true hk
          obtain h513 : 513 ≤ keyLo v.callee.sve true := by cases v.callee.sve <;> decide
          exact WP.mono (SealKey.sealMain_ok v hp₂ (by omega_using [hL₂, hk', h513]) (by omega_using [hL₂, hk']))
            fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
        · exact WP.mono (sealStitchedMain_ok v hp₂) fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
      · have hr := of_decide_eq_true h
        obtain hL : 512 ≤ L s₂ := by
          obtain hlo : 256 ≤ wideLo v.callee.sve true := by cases v.callee.sve <;> decide
          obtain hs : Short.lo v.callee.sve ≤ 64 := by cases v.callee.sve <;> decide
          obtain hn' := of_decide_eq_false hn
          simp only [Short.inRoute] at hr
          obtain e1 := ag.gpr .x5 (by decide) (by decide)
          obtain e2 := ag₂.gpr .x5 (by decide) (by decide)
          simp only [L, e1, e2] at hr hn' ⊢
          omega_using [hlo, hs, hn', hr]
        exact WP.mono (sealWideMain_ok v hp₂ hL) fun _ h => Short.MainS.agree ag (Short.MainS.agree ag₂ h)
    · exact WP.mono (sealMain_ok v hp₁) fun _ h => Short.MainS.agree ag h

theorem openMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openMainCode v.callee v.stitched) s₀ (MainO s₀) := by
  unfold openMainCode
  refine WP.seq (WP.mono (Short.check_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  obtain hp₁ := Short.APre.agree ag hp
  refine WP.ite (decide (Short.lo v.callee.sve ≤ L s₀ ∧ L s₀ ≤ 511)) (Short.check_eval x9) (fun h => ?_) (fun hn => ?_)
  · have hlo : 1 ≤ L s₁ := by
      have := (of_decide_eq_true h).1
      have : 1 ≤ Short.lo v.callee.sve := by cases v.callee.sve <;> decide
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega_arith
    obtain h511 : L s₁ ≤ 511 := by
      have := (of_decide_eq_true h).2
      rw [L, ag.gpr .x5 (by decide) (by decide)]; simp only [L] at *; omega_using [this]
    exact WP.mono (OpenPad.openRoute_ok v hp₁ hlo h511) fun _ h => Short.MainO.agree ag h
  · split
    · refine WP.seq (WP.mono (OpenKey.routeKey_ok v.callee.sve false s₁) fun s₂ ⟨ag₂, x9₂, x10₂⟩ => ?_)
      obtain hp₂ := Short.APre.agree ag₂ hp₁
      refine WP.ite (decide (Short.inRoute v.callee.sve false (L s₁))) (Short.route_eval x9₂)
        (fun h => ?_) (fun _ => ?_)
      rotate_left
      · have hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
        refine WP.iteCold_iff.mpr (WP.ite (decide (keyLo v.callee.sve false ≤ L s₁ ∧ L s₁ ≤ 704)) (OpenKey.key_eval x10₂)
          (fun hk => ?_) (fun _ => ?_))
        · have hk' := of_decide_eq_true hk
          obtain h513 : 513 ≤ keyLo v.callee.sve false := by cases v.callee.sve <;> decide
          exact WP.mono (OpenKey.openMain_ok v hp₂ (by omega_using [hL₂, hk', h513]) (by omega_using [hL₂, hk']))
            fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
        · exact WP.mono (openStitchedMain_ok v hp₂) fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
      · have hr := of_decide_eq_true h
        obtain hL : 512 ≤ L s₂ := by
          obtain hlo : 256 ≤ wideLo v.callee.sve false := by cases v.callee.sve <;> decide
          obtain hs : Short.lo v.callee.sve ≤ 64 := by cases v.callee.sve <;> decide
          obtain hn' := of_decide_eq_false hn
          simp only [Short.inRoute] at hr
          obtain e1 := ag.gpr .x5 (by decide) (by decide)
          obtain e2 := ag₂.gpr .x5 (by decide) (by decide)
          simp only [L, e1, e2] at hr hn' ⊢
          omega_using [hlo, hs, hn', hr]
        exact WP.mono (openWideMain_ok v hp₂ hL) fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
    · exact WP.mono (openMain_ok v hp₁) fun _ h => Short.MainO.agree ag h

theorem seal_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (sealCode v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ sealAArch64.post s s' := by
  rw [sealCode_eq]
  exact WP.seq (WP.mono (sealMainCode_ok v (APre.of s hs)) fun _ h => sealTail_ok (APre.of s hs) h)

/-! ### `open`'s body -/

/-- The 32 bytes after `open`'s context. -/
abbrev slotOf (σ : State) : Region := ⟨off (σ.gpr .x7) 1280, 32⟩

/-- `saveData`: the destination, `len` and our caller's `x28` after the
context, and `x28` set to the destination's distance from the data. -/
theorem saveData_ok {σ : State} (hp : preOpenAArch64 σ) :
    WP isa (.block saveData) σ fun s => (∀ r, r ≠ .x28 → s.gpr r = σ.gpr r) ∧
      s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4 ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      Frame [slotOf σ] σ.mem s.mem ∧
      s.mem.readW (off (σ.gpr .x7) 1280) 64 = σ.gpr .x8 ∧
      s.mem.readW (off (σ.gpr .x7) 1288) 64 = σ.gpr .x5 ∧
      s.mem.readW (off (σ.gpr .x7) 1296) 64 = σ.gpr .x28 := by
  obtain ⟨-, -, -, -, -, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wc, -⟩ := hp
  obtain hc : ∀ d, 1280 ≤ d → d + 8 ≤ 1312 → (slotOf σ).Contains (off (σ.gpr .x7) d) 8 := fun d h1 h2 =>
    Offset.contains (σ.gpr .x7) h1 (by omega_using [h2]) (by omega_using [])
  obtain hin : slotOf σ ∈ σ.wr := by rw [hw]; simp
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1280) (by decide) rfl
    ⟨_, hin, hc 1280 (Nat.le_refl _) (by decide)⟩ fun s₁ m₁ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1288) (by decide) (by rw [m₁.gpr])
    ⟨_, by rw [m₁.wr]; exact hin, hc 1288 (by decide) (by decide)⟩ fun s₂ m₂ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str (a := off (σ.gpr .x7) 1296) (by decide)
    (by rw [m₂.gpr, m₁.gpr]) ⟨_, by rw [m₂.wr, m₁.wr]; exact hin, hc 1296 (by decide) (by decide)⟩
    fun s₃ m₃ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_sub fun s₄ u₄ => WP.block_nil ⟨fun r hr => ?_, ?_,
    by rw [u₄.rd, m₃.rd, m₂.rd, m₁.rd], by rw [u₄.wr, m₃.wr, m₂.wr, m₁.wr], ?_, ?_, ?_, ?_⟩
  · rw [u₄.other r hr, m₃.gpr, m₂.gpr, m₁.gpr]
  · rw [u₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr]
  · rw [u₄.mem, m₃.mem, m₂.mem, m₁.mem, m₂.gpr, m₁.gpr]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 1280 (Nat.le_refl _) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1288 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (hc 1296 (by decide) (by decide))
  · rw [u₄.mem, m₃.mem, m₂.mem, m₁.mem, readW64_off _ _ _ (by decide) (by decide) (by decide),
      readW64_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [u₄.mem, m₃.mem, m₂.mem, readW64_off _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, m₁.gpr]
  · rw [u₄.mem, m₃.mem, Mem.readW_writeW_self64, m₂.gpr, m₁.gpr]

/-- `op false s`, after `saveData`: the destination. -/
theorem op_ofOpen {σ s : State} (hg : ∀ r, r ≠ .x28 → s.gpr r = σ.gpr r)
    (h28 : s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4) : op false s = σ.gpr .x8 := by
  rw [op_false]
  show s.gpr .x4 + s.gpr .x28 = _
  rw [hg .x4 (by decide), h28, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The main code's precondition, after `saveData`. -/
theorem APre.ofOpen {σ s : State} (h : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s.gpr r = σ.gpr r)
    (h28 : s.gpr .x28 = σ.gpr .x8 - σ.gpr .x4) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr) :
    APre false s := by
  obtain ⟨hk, hn, ha, ht, hd, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, qd, sk, sn, sa, sd, st, sq,
    wc, wa, wd, wq, wt, wk, wn⟩ := h
  obtain g0 := hg .x0 (by decide); have g1 := hg .x1 (by decide); have g2 := hg .x2 (by decide)
  obtain g3 := hg .x3 (by decide); have g4 := hg .x4 (by decide); have g5 := hg .x5 (by decide)
  obtain g6 := hg .x6 (by decide); have g7 := hg .x7 (by decide)
  obtain eL : L s = (σ.gpr .x5).toNat := by simp only [L, g5]
  obtain ekR : kR s = ⟨σ.gpr .x0, 32⟩ := by simp only [kR, kp, g0]
  obtain enR : nR s = ⟨σ.gpr .x1, 12⟩ := by simp only [nR, np, g1]
  obtain eaR : aR s = ⟨σ.gpr .x2, (σ.gpr .x3).toNat⟩ := by simp only [aR, ad, AL, g2, g3]
  obtain edR : dR s = ⟨σ.gpr .x4, (σ.gpr .x5).toNat⟩ := by simp only [dR, dp, L, g4, g5]
  obtain etR : tR s = ⟨σ.gpr .x6, 16⟩ := by simp only [tR, tp, g6]
  obtain ecR : ctxR s = ⟨σ.gpr .x7, 1280⟩ := by simp only [ctxR, cx, g7]
  obtain esR : slotR s = ⟨σ.gpr .x7 + BitVec.ofNat 64 1280, 32⟩ := by simp only [slotR, sub, off, cx, g7]
  obtain eop := op_ofOpen hg h28
  obtain eqR : qR s = ⟨σ.gpr .x8, (σ.gpr .x5).toNat⟩ := by
    rw [← eL, ← eop, op_false]
  obtain eo : (⟨op false s, L s⟩ : Region) = ⟨σ.gpr .x8, (σ.gpr .x5).toNat⟩ := by rw [eop, eL]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hrd]
    simp only [rdR, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [ekR]; exact hk
    · rw [enR]; exact hn
    · rw [eaR]; exact ha
    · rw [etR]; exact ht
  · rw [hwr, hw, eqR, ecR, esR]; rfl
  · rw [edR, hrd, hwr]; exact hd
  · rw [ecR, ekR]; exact ck
  · rw [ecR, enR]; exact cn
  · rw [ecR, eaR]; exact ca
  · rw [ecR, edR]; exact cd
  · rw [ecR, etR]; exact ct
  · rw [eo, hwr, hw]; simp
  · rw [eop, eL]; exact wq
  · rw [eo, ecR]; exact cq
  · rw [eo, ekR]; exact qk.symm
  · rw [eo, enR]; exact qn.symm
  · rw [eo, eaR]; exact qa.symm
  · rw [eo, etR]; exact qt.symm
  · rcases qd with e | e
    · left; rw [eop, e]; exact g4.symm
    · right; rw [eo, edR]; exact e
  · simp only [cx, g7]; omega_using [wc]
  · simp only [ad, AL, g2, g3]; exact wa
  · rw [show dp s = σ.gpr .x4 from g4, eL]; exact wd
  · simp only [tp, g6]; exact wt
  · simp only [kp, g0]; exact wk
  · simp only [np, g1]; exact wn
  · rw [esR, ekR]; exact sk
  · rw [esR, enR]; exact sn
  · rw [esR, eaR]; exact sa
  · rw [esR, edR]; exact sd
  · rw [esR, etR]; exact st
  · rw [esR, eqR]; exact sq
  · simp only [cx, g7]; exact wc

/-- `saveData`'s stores are outside the arguments the body reads. -/
theorem slot_bytes {σ : State} (hp : preOpenAArch64 σ) {m : Mem} (hf : Frame [slotOf σ] σ.mem m) :
    bytesAt m (σ.gpr .x0) 32 = bytesAt σ.mem (σ.gpr .x0) 32 ∧
      bytesAt m (σ.gpr .x1) 12 = bytesAt σ.mem (σ.gpr .x1) 12 ∧
      bytesAt m (σ.gpr .x2) (σ.gpr .x3).toNat = bytesAt σ.mem (σ.gpr .x2) (σ.gpr .x3).toNat ∧
      bytesAt m (σ.gpr .x4) (σ.gpr .x5).toNat = bytesAt σ.mem (σ.gpr .x4) (σ.gpr .x5).toNat ∧
      bytesAt m (σ.gpr .x6) 16 = bytesAt σ.mem (σ.gpr .x6) 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sk, sn, sa, sd, st, -⟩ := hp
  obtain one : ∀ {r : Region}, (slotOf σ).Disjoint r → ∀ q ∈ [slotOf σ], r.Disjoint q := fun h q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact h.symm
  exact ⟨bytesAt_frame hf (one sk) (by decide), bytesAt_frame hf (one sn) (by decide),
    bytesAt_frame hf (one sa) (Nat.le_of_lt (σ.gpr .x3).isLt),
    bytesAt_frame hf (one sd) (Nat.le_of_lt (σ.gpr .x5).isLt), bytesAt_frame hf (one st) (by decide)⟩

theorem post_of_save {σ s₁ s' : State} (hp : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s₁.gpr r = σ.gpr r)
    (hf : Frame [slotOf σ] σ.mem s₁.mem) (h : openAArch64.post s₁ s') : openAArch64.post σ s' := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  rw [openAArch64, Contract.post_mk] at h ⊢
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), hg .x8 (by decide), bk, bn, ba, bd, bt] at h
  exact h

theorem ok_of_save {σ s₁ : State} (hp : preOpenAArch64 σ) (hg : ∀ r, r ≠ .x28 → s₁.gpr r = σ.gpr r)
    (hf : Frame [slotOf σ] σ.mem s₁.mem) : okAArch64 s₁ = okAArch64 σ := by
  obtain ⟨bk, bn, ba, bd, bt⟩ := slot_bytes hp hf
  unfold okAArch64
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), bk, bn, ba, bd, bt]

/-- `open`'s body, from the source (`x4`) to the destination (`x8`). -/
theorem openBody_ok (v : Proof.ChaCha20.AArch64.XorImpl) (σ : State) (hs : preOpenAArch64 σ) :
    WP isa (openCode v.callee v.stitched) σ fun s' => abiPreserved σ s' ∧ openAArch64.post σ s' := by
  rw [openCode_eq]
  refine WP.seq (WP.mono (WP.withSp (WP.preservedV (saveData_ok hs) (by lit_decide)))
    fun s₁ ⟨⟨⟨g₁, x28₁, rd₁, wr₁, f₁, d₁, l₁, c₁⟩, v₁⟩, sp₁⟩ => ?_)
  obtain hp₁ : APre false s₁ := APre.ofOpen hs g₁ x28₁ rd₁ wr₁
  obtain eop := op_ofOpen g₁ x28₁
  obtain e7 : cx s₁ = σ.gpr .x7 := g₁ .x7 (by decide)
  refine WP.seq (WP.mono (openMainCode_ok v hp₁) fun s₂ h₂ => ?_)
  refine WP.mono (openTail_ok (σ := σ) hp₁ h₂ (by rw [e7, d₁, eop]) (by rw [e7, l₁, g₁ .x5 (by decide)])
    (by rw [e7, c₁]) g₁ sp₁ v₁ (by rw [eop, g₁ .x8 (by decide)]))
    fun s₃ ⟨ha, hq⟩ => ⟨ha, post_of_save hs g₁ f₁ hq⟩

/-! ## Constant time -/

theorem sealLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x2 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem sealRest_taint : ∃ h, (taint.check (Taint.ofRegs [.x2, .x21])
    (.seq finalizeTag (.block restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem openLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x12 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem saveData_taint : ∃ h, (taint.check (Taint.ofRegs [.x7]) (.block saveData) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem compare_taint : ∃ h, (taint.check (Taint.ofRegs [.x12, .x21]) (.block compare) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21]) (.block zeroLoad) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zeroLoop_taint : ∃ h, (taint.check (Taint.ofRegs [.x9, .x10]) zeroLoop h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore28_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block (.ldr .x .x28 .x21 1296 :: restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem skip_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pub_regs {s₁ s₂ : State} (hq : pubAArch64 s₁ s₂) :
    ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub
    (sealCode v.callee v.stitched) := by
  rw [sealCode_eq]
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain hp₁ := APre.of _ h₁
  obtain hp₂ := APre.of _ h₂
  obtain ⟨-, -, -, -, -, -, p6, p7, psp⟩ := id hq
  refine (rel_seq (rel_taint _ psp (pub_regs hq) v.sealTaint) (sealMainCode_ok v hp₁)
    (sealMainCode_ok v hp₂) (fun τ₁ τ₂ m₁ m₂ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  obtain sp : τ₁.sp = τ₂.sp := by rw [m₁.inv.sp, m₂.inv.sp, psp]
  refine rel_seq (rel_taint [.x21] sp (by
      simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, cx, p7]) sealLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x2₁, k₁⟩ ⟨x2₂, k₂⟩ => rel_taint [.x2, .x21] (by rw [k₁.sp, k₂.sp, sp]) ?_ sealRest_taint
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x2₁, x2₂, tp, tp, p6]
  · rw [k₁.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21, m₂.inv.x21, cx,
      cx, p7]

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `openTail`, in two runs from the states `openMainCode_ok` describes:
the branch to `zeroData` is on the result, which the two runs' leaks say
agree (`hok`), and `zeroData`'s loop on `len`, which correctness says it
loads from where `saveData` saved it. -/
theorem tail_rel {τ₁ τ₂ ρ₁ ρ₂ : State} (hp₁ : APre false τ₁) (hp₂ : APre false τ₂)
    (m₁ : MainO τ₁ ρ₁) (m₂ : MainO τ₂ ρ₂)
    (d₁ : τ₁.mem.readW (off (cx τ₁) 1280) 64 = op false τ₁)
    (l₁ : τ₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5)
    (d₂ : τ₂.mem.readW (off (cx τ₂) 1280) 64 = op false τ₂)
    (l₂ : τ₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5)
    (ecx : cx τ₁ = cx τ₂) (eop : op false τ₁ = op false τ₂) (el : τ₁.gpr .x5 = τ₂.gpr .x5)
    (etp : tp τ₁ = tp τ₂) (hok : okAArch64 τ₁ = okAArch64 τ₂) (sp : ρ₁.sp = ρ₂.sp) :
    RelCT isa (Eq2 ρ₁ ρ₂) openTail TT := by
  unfold openTail
  refine rel_seq (rel_taint [.x21] sp (by simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, ecx])
      openLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x12₁, k₁⟩ ⟨x12₂, k₂⟩ => ?_
  obtain x21₁ : u₁.gpr .x21 = cx τ₁ := by rw [k₁.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21]
  obtain x21₂ : u₂.gpr .x21 = cx τ₂ := by rw [k₂.cs _ (pres .x21) (pres30 .x21), m₂.inv.x21]
  obtain spu : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, sp]
  refine rel_seq (rel_taint [.x12, .x21] spu (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [x12₁, x12₂, etp]
      · rw [x21₁, x21₂, ecx]) compare_taint)
    (WP.withSp (compare_ok hp₁ x21₁ x12₁ (by rw [k₁.rd, m₁.inv.rd]) (by rw [k₁.wr, m₁.inv.wr])))
    (WP.withSp (compare_ok hp₂ x21₂ x12₂ (by rw [k₂.rd, m₂.inv.rd]) (by rw [k₂.wr, m₂.inv.wr])))
    fun w₁ w₂ ⟨⟨rax₁, g₁, _, mm₁, rd₁, wr₁⟩, sp₁⟩ ⟨⟨rax₂, g₂, _, mm₂, rd₂, wr₂⟩, sp₂⟩ => ?_
  obtain ⟨c₁, t₁⟩ := m₁.tags hp₁ k₁.mem_eq
  obtain ⟨c₂, t₂⟩ := m₂.tags hp₂ k₂.mem_eq
  rw [c₁, t₁] at rax₁
  rw [c₂, t₂] at rax₂
  obtain hb : (w₁.gpr .x0).setWidth 32 = (w₂.gpr .x0).setWidth 32 := by
    rw [rax₁, rax₂]
    by_cases h₁ : okAArch64 τ₁ = true
    · have h₂ : okAArch64 τ₂ = true := hok ▸ h₁
      simp only [(ok_iff τ₁).mp h₁, (ok_iff τ₂).mp h₂, ↓reduceIte]
    · have h₂ : ¬okAArch64 τ₂ = true := hok ▸ h₁
      simp only [show ¬mac (otk τ₁) (macData (A τ₁) (D τ₁)) = T0 τ₁ from fun h' => h₁ ((ok_iff τ₁).mpr h'),
        show ¬mac (otk τ₂) (macData (A τ₂) (D τ₂)) = T0 τ₂ from fun h' => h₂ ((ok_iff τ₂).mpr h'),
        ↓reduceIte]
  obtain x21w₁ : w₁.gpr .x21 = cx τ₁ := by rw [g₁ _ (pres .x21), x21₁]
  obtain x21w₂ : w₂.gpr .x21 = cx τ₂ := by rw [g₂ _ (pres .x21), x21₂]
  obtain rdw₁ : w₁.rd = τ₁.rd := by rw [rd₁, k₁.rd, m₁.inv.rd]
  obtain rdw₂ : w₂.rd = τ₂.rd := by rw [rd₂, k₂.rd, m₂.inv.rd]
  obtain wrw₁ : w₁.wr = τ₁.wr := by rw [wr₁, k₁.wr, m₁.inv.wr]
  obtain wrw₂ : w₂.wr = τ₂.wr := by rw [wr₂, k₂.wr, m₂.inv.wr]
  obtain mw₁ : w₁.mem = ρ₁.mem := by rw [mm₁, k₁.mem_eq]
  obtain mw₂ : w₂.mem = ρ₂.mem := by rw [mm₂, k₂.mem_eq]
  obtain dw₁ : w₁.mem.readW (off (cx τ₁) 1280) 64 = op false τ₁ := by
    rw [mw₁, m₁.slot hp₁ (Nat.le_refl _) (by decide), d₁]
  obtain dw₂ : w₂.mem.readW (off (cx τ₂) 1280) 64 = op false τ₂ := by
    rw [mw₂, m₂.slot hp₂ (Nat.le_refl _) (by decide), d₂]
  obtain lw₁ : w₁.mem.readW (off (cx τ₁) 1288) 64 = τ₁.gpr .x5 := by
    rw [mw₁, m₁.slot hp₁ (by decide) (by decide), l₁]
  obtain lw₂ : w₂.mem.readW (off (cx τ₂) 1288) 64 = τ₂.gpr .x5 := by
    rw [mw₂, m₂.slot hp₂ (by decide) (by decide), l₂]
  obtain spw : w₁.sp = w₂.sp := by rw [sp₁, sp₂, spu]
  refine rel_seq ?_ (zeroIte_ok hp₁ x21w₁ rdw₁ wrw₁ dw₁ lw₁) (zeroIte_ok hp₂ x21w₂ rdw₂ wrw₂ dw₂ lw₂)
    fun z₁ z₂ ⟨x21z₁, spz₁⟩ ⟨x21z₂, spz₂⟩ => rel_taint [.x21] (by rw [spz₁, spz₂, spw])
      (by simp only [List.mem_singleton, forall_eq, x21z₁, x21z₂, x21w₁, x21w₂, ecx]) restore28_taint
  refine RelCT.ite (fun a b ⟨ea, eb⟩ => by rw [ea, eb, eval_zero_w, eval_zero_w, hb]) ?_ ?_
  · refine (?_ : RelCT isa (Eq2 w₁ w₂) zeroData TT).mono (fun _ _ h => h.1) fun _ _ h => h
    unfold zeroData
    exact rel_seq (rel_taint [.x21] spw (by simp only [List.mem_singleton, forall_eq, x21w₁, x21w₂, ecx])
        zeroLoad_taint)
      (WP.withSp (zeroLoad_ok hp₁ x21w₁ rdw₁ wrw₁ dw₁ lw₁)) (WP.withSp (zeroLoad_ok hp₂ x21w₂ rdw₂ wrw₂ dw₂ lw₂))
      fun y₁ y₂ ⟨⟨x9₁, x10₁, _⟩, spy₁⟩ ⟨⟨x9₂, x10₂, _⟩, spy₂⟩ =>
        rel_taint [.x9, .x10] (by rw [spy₁, spy₂, spw]) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [x9₁, x9₂, eop]
          · rw [x10₁, x10₂, el]) zeroLoop_taint
  · exact (rel_taint [] spw (by simp) skip_taint).mono (fun _ _ h => h.1) fun _ _ h => h

/-- `open`'s body, in two runs from states that agree on its arguments and on
whether the tag is right. -/
theorem openBody_rel (v : Proof.ChaCha20.AArch64.XorImpl) {σ₁ σ₂ : State} (h₁ : preOpenAArch64 σ₁)
    (h₂ : preOpenAArch64 σ₂)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8], σ₁.gpr r = σ₂.gpr r)
    (psp : σ₁.sp = σ₂.sp) (hok : okAArch64 σ₁ = okAArch64 σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (openCode v.callee v.stitched) TT := by
  rw [openCode_eq]
  obtain p4 := hq .x4 (by simp); have p5 := hq .x5 (by simp); have p6 := hq .x6 (by simp)
  obtain p7 := hq .x7 (by simp); have p8 := hq .x8 (by simp)
  refine rel_seq (rel_taint [.x7] psp (by simp only [List.mem_singleton, forall_eq, p7]) saveData_taint)
    (WP.withSp (saveData_ok h₁)) (WP.withSp (saveData_ok h₂))
    (fun τ₁ τ₂ ⟨⟨g₁, x28₁, rd₁, wr₁, f₁, d₁, l₁, _⟩, sp₁⟩ ⟨⟨g₂, x28₂, rd₂, wr₂, f₂, d₂, l₂, _⟩, sp₂⟩ => ?_)
  obtain hpτ₁ := APre.ofOpen h₁ g₁ x28₁ rd₁ wr₁
  obtain hpτ₂ := APre.ofOpen h₂ g₂ x28₂ rd₂ wr₂
  obtain eop₁ := op_ofOpen g₁ x28₁
  obtain eop₂ := op_ofOpen g₂ x28₂
  obtain spτ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28] spτ
      (fun r hr => ?_) v.openTaint)
    (openMainCode_ok v hpτ₁) (openMainCode_ok v hpτ₂) fun ρ₁ ρ₂ mo₁ mo₂ => ?_
  · by_cases h28 : r = .x28
    · subst h28; rw [x28₁, x28₂, p8, p4]
    · have hs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28], r ≠ .x28 →
          r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8] := by decide
      rw [g₁ r h28, g₂ r h28]
      exact hq r (hs r hr h28)
  · exact tail_rel hpτ₁ hpτ₂ mo₁ mo₂
      (by rw [show cx τ₁ = σ₁.gpr .x7 from g₁ .x7 (by decide), d₁, eop₁])
      (by rw [show cx τ₁ = σ₁.gpr .x7 from g₁ .x7 (by decide), l₁, g₁ .x5 (by decide)])
      (by rw [show cx τ₂ = σ₂.gpr .x7 from g₂ .x7 (by decide), d₂, eop₂])
      (by rw [show cx τ₂ = σ₂.gpr .x7 from g₂ .x7 (by decide), l₂, g₂ .x5 (by decide)])
      (by simp only [cx, g₁ .x7 (by decide), g₂ .x7 (by decide), p7]) (by rw [eop₁, eop₂, p8])
      (by rw [g₁ .x5 (by decide), g₂ .x5 (by decide), p5])
      (by simp only [tp, g₁ .x6 (by decide), g₂ .x6 (by decide), p6])
      (by rw [ok_of_save h₁ g₁ f₁, ok_of_save h₂ g₂ f₂, hok])
      (by rw [mo₁.inv.sp, mo₂.inv.sp, spτ])

/-! ## `open`, in place

The function moves the data's address to the destination (`mov x8, x4`) and
runs the body. -/

open VG.AArch64 in
/-- `open`'s precondition with permission to write only the data, the
context and the 32 bytes after it (`openWr`). -/
def preInAArch64 (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let work : Region := ⟨s.gpr .x7, 1280⟩
  let slot : Region := ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩
  key ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ tag ∈ s.rd ∧ s.wr = [data, work, slot] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  slot.Disjoint key ∧ slot.Disjoint nonce ∧ slot.Disjoint aad ∧ slot.Disjoint data ∧
  slot.Disjoint tag ∧
  (s.gpr .x7).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64

open VG.AArch64 in
/-- `vg_chacha20_poly1305_open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`
(`preInAArch64`): zeros at `data` if the tag is wrong; it may leak whether it
is (`openLeakAArch64`). -/
def openInAArch64 : Contract AArch64.isa where
  pre := preInAArch64
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (bytesAt s.mem (s.gpr .x6) 16) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = List.replicate (s.gpr .x5).toNat 0
  pub s₁ s₂ := pubAArch64 s₁ s₂ ∧ openLeakAArch64 s₁ = openLeakAArch64 s₂

/-- `mov x8, x4`. -/
theorem movIn_ok (σ : State) :
    WP isa (.block [mov .x8 .x4]) σ fun u => (∀ r, r ≠ .x8 → u.gpr r = σ.gpr r) ∧
      u.gpr .x8 = σ.gpr .x4 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.v = σ.v :=
  VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun _ hu hsp hv =>
    WP.block_nil ⟨hu.other, hu.gpr, hu.mem, hu.rd, hu.wr, hsp, hv⟩

theorem movIn_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block [mov .x8 .x4]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The body's precondition, after `mov x8, x4`. -/
theorem preIn_body {s u : State} (h : preInAArch64 s) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (h8 : u.gpr .x8 = s.gpr .x4) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) : preOpenAArch64 u := by
  obtain ⟨hk, hn, ha, ht, hw, ck, cn, ca, cd, ct, dk, dn, da, dt, sk, sn, sa, sd, st, wc, wa, wd, wt, wk,
    wn⟩ := h
  simp only [preOpenAArch64]
  rw [hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide), hg .x4 (by decide),
    hg .x5 (by decide), hg .x6 (by decide), hg .x7 (by decide), h8, hrd, hwr]
  exact ⟨hk, hn, ha, ht, List.mem_append_right _ (by rw [hw]; simp), hw, ck, cn, ca, cd, ct, cd, dk, dn, da, dt,
    .inl rfl, sk, sn, sa, sd, st, sd, wc, wa, wd, wd, wt, wk, wn⟩

theorem openIn_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openInAArch64.pre s) :
    ∃ t s', Exec isa (openInPlace v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ openInAArch64.post s s' := by
  show WP isa (.seq (.block [mov .x8 .x4]) (openCode v.callee v.stitched)) s _
  refine WP.seq (WP.mono (movIn_ok s) fun u ⟨hg, h8, hm, hrd, hwr, hsp, hv⟩ => ?_)
  refine WP.mono (openBody_ok v u (preIn_body hs hg h8 hrd hwr)) fun s' ⟨ha, hq⟩ => ⟨?_, ?_⟩
  · exact ⟨fun r hr => by rw [ha.1 r hr, hg r (by rintro rfl; simp [preserved] at hr)], by rw [ha.2.1, hsp],
      fun r hr => by rw [ha.2.2 r hr, hv]⟩
  · rw [openAArch64, Contract.post_mk] at hq
    rw [openInAArch64, Contract.post_mk]
    rw [hm, hg .x0 (by decide), hg .x1 (by decide), hg .x2 (by decide), hg .x3 (by decide),
      hg .x4 (by decide), hg .x5 (by decide), hg .x6 (by decide), h8] at hq
    exact hq

theorem openIn_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa openInAArch64.pre openInAArch64.pub (openInPlace v.callee v.stitched) := by
  show ConstantTime isa _ _ (.seq (.block [mov .x8 .x4]) (openCode v.callee v.stitched))
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨hq, hl⟩ := hq
  obtain hr := pub_regs hq
  obtain ⟨-, -, -, -, -, -, -, -, psp⟩ := id hq
  obtain hok : okAArch64 σ₁ = okAArch64 σ₂ := leak_bool hl
  refine (rel_seq (rel_taint [] psp (by simp) movIn_taint) (movIn_ok σ₁) (movIn_ok σ₂) ?_
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  rintro u₁ u₂ ⟨g₁, x8₁, m₁, rd₁, wr₁, sp₁, -⟩ ⟨g₂, x8₂, m₂, rd₂, wr₂, sp₂, -⟩
  obtain hs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8], r ≠ .x8 →
      r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] := by decide
  refine openBody_rel v (preIn_body h₁ g₁ x8₁ rd₁ wr₁) (preIn_body h₂ g₂ x8₂ rd₂ wr₂) (fun r hr' => ?_)
    (by rw [sp₁, sp₂, psp]) ?_
  · by_cases h8 : r = .x8
    · subst h8; rw [x8₁, x8₂]; exact hr .x4 (by simp)
    · rw [g₁ r h8, g₂ r h8]; exact hr r (hs r hr' h8)
  · unfold okAArch64
    rw [m₁, m₂, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide), g₁ .x3 (by decide),
      g₁ .x4 (by decide), g₁ .x5 (by decide), g₁ .x6 (by decide), g₂ .x0 (by decide), g₂ .x1 (by decide),
      g₂ .x2 (by decide), g₂ .x3 (by decide), g₂ .x4 (by decide), g₂ .x5 (by decide), g₂ .x6 (by decide)]
    exact hok

/-! ## `open_to`

The function moves the destination to `x8` (`mov x8, x6`), loads `tag` and
`work` from the stack into `x6` and `x7`, and runs the body. -/

open VG.AArch64 in
/-- `open_to`'s precondition with permission to write only the destination,
the context and the 32 bytes after it (`toWr`), and `dst_len = len`. -/
def preToN (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let src : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let dst : Region := ⟨s.gpr .x6, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1280⟩
  let slot : Region := ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  key ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ tag ∈ s.rd ∧ src ∈ s.rd ∧ args ∈ s.rd ∧
  s.wr = [dst, work, slot] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧
  work.Disjoint tag ∧ work.Disjoint dst ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint tag ∧ src.Disjoint dst ∧
  slot.Disjoint key ∧ slot.Disjoint nonce ∧ slot.Disjoint aad ∧ slot.Disjoint src ∧
  slot.Disjoint tag ∧ slot.Disjoint dst ∧
  (stackArg s 1).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧
  (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧ s.sp.toNat + 16 ≤ 2 ^ 64

open VG.AArch64 in
/-- `open_to`'s result: `decrypt` of the source, with the tag at the first
stack argument. -/
def openToRes (s : AArch64.State) : Option (List Byte) :=
  decrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
    (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (bytesAt s.mem (stackArg s 0) 16)

open VG.AArch64 in
/-- What `open_to` may leak: whether the message is authenticated. -/
def openToLeakAArch64 (s : AArch64.State) : List Nat := [if (openToRes s).isSome then 1 else 0]

open VG.AArch64 in
def pubToAArch64 (s₁ s₂ : AArch64.State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
  s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
  s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
  stackArg s₁ 1 = stackArg s₂ 1

open VG.AArch64 in
/-- `vg_chacha20_poly1305_open_to(key, nonce, aad, aad_len, src, len, dst, dst_len, tag, work) -> u32`
(`preToN`): decrypts from `src` to `dst`, zeros at `dst` if the tag is wrong;
it may leak whether it is (`openToLeakAArch64`). -/
def openToN : Contract AArch64.isa where
  pre := preToN
  post s s' :=
    match openToRes s with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x6) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x6) (s.gpr .x5).toNat = List.replicate (s.gpr .x5).toNat 0
  pub s₁ s₂ := pubToAArch64 s₁ s₂ ∧ openToLeakAArch64 s₁ = openToLeakAArch64 s₂

/-- An `ldr` from the stack, keeping the stack pointer and the vector registers. -/
theorem wp_ldrSp64 {s : State} {t : Reg} {off : Nat} {is : List Instr} {Q : State → Prop}
    (ho : off % 8 = 0 ∧ off < 32768) (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8)
    (k : ∀ s', Upd s s' t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64) → s'.sp = s.sp → s'.v = s.v →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (exec_ldrSp ho h) (k _ (Upd.write64 _ _ _) rfl rfl)

/-- `open_to`'s moves. -/
theorem toEntry_ok {σ : State} (ha : (⟨stackArgAddr σ 0, 16⟩ : Region) ∈ σ.rd)
    (_hsp : σ.sp.toNat + 16 ≤ 2 ^ 64) :
    WP isa (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) σ fun u =>
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u.gpr r = σ.gpr r) ∧ u.gpr .x8 = σ.gpr .x6 ∧
      u.gpr .x6 = stackArg σ 0 ∧ u.gpr .x7 = stackArg σ 1 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧
      u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.v = σ.v := by
  obtain ha' : (⟨σ.sp, 16⟩ : Region) ∈ σ.rd := by
    obtain e : stackArgAddr σ 0 = σ.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    rw [← e]; exact ha
  obtain hin : ∀ d, d + 8 ≤ 16 → InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, List.mem_append_left _ ha', Offset.contains_base _ hd (by omega_using [hd])⟩
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun u₁ v₁ sp₁ w₁ => ?_
  refine wp_ldrSp64 (by decide) (by rw [v₁.rd, v₁.wr, sp₁]; exact hin 0 (by decide)) fun u₂ v₂ sp₂ w₂ => ?_
  refine wp_ldrSp64 (by decide) (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, sp₂, sp₁]; exact hin 8 (by decide))
    fun u₃ v₃ sp₃ w₃ => WP.block_nil ⟨fun r h6 h7 h8 => by rw [v₃.other r h7, v₂.other r h6, v₁.other r h8],
      by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr],
      by rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, sp₁]; rfl,
      by rw [v₃.gpr, v₂.mem, v₁.mem, sp₂, sp₁]; rfl,
      by rw [v₃.mem, v₂.mem, v₁.mem], by rw [v₃.rd, v₂.rd, v₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr],
      by rw [sp₃, sp₂, sp₁], by rw [w₃, w₂, w₁]⟩

theorem toEntry_taint : ∃ h, (taint.check (Taint.ofRegs [])
    (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The body's precondition, after `open_to`'s moves. -/
theorem preTo_body {s u : State} (h : preToN s)
    (hg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → u.gpr r = s.gpr r) (h8 : u.gpr .x8 = s.gpr .x6)
    (h6 : u.gpr .x6 = stackArg s 0) (h7 : u.gpr .x7 = stackArg s 1) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) : preOpenAArch64 u := by
  obtain ⟨hk, hn, ha, ht, hd, -, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, dq, sk, sn, sa, sd, st, sq,
    wc, wa, wd, wq, wt, wk, wn, -⟩ := h
  simp only [preOpenAArch64]
  rw [hg .x0 (by decide) (by decide) (by decide), hg .x1 (by decide) (by decide) (by decide),
    hg .x2 (by decide) (by decide) (by decide), hg .x3 (by decide) (by decide) (by decide),
    hg .x4 (by decide) (by decide) (by decide), hg .x5 (by decide) (by decide) (by decide), h6, h7, h8,
    hrd, hwr]
  exact ⟨hk, hn, ha, ht, List.mem_append_left _ hd, hw, ck, cn, ca, cd, ct, cq, qk, qn, qa, qt, .inr dq,
    sk, sn, sa, sd, st, sq, wc, wa, wd, wq, wt, wk, wn⟩

theorem openTo_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openToN.pre s) :
    ∃ t s', Exec isa (openTo v.callee v.stitched) s t s' ∧ abiPreserved s s' ∧ openToN.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, ha, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp⟩ := hs'
  show WP isa (.seq (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) (openCode v.callee v.stitched)) s _
  refine WP.seq (WP.mono (toEntry_ok ha hsp) fun u ⟨hg, h8, h6, h7, hm, hrd, hwr, hsp', hv⟩ => ?_)
  refine WP.mono (openBody_ok v u (preTo_body hs hg h8 h6 h7 hrd hwr)) fun s' ⟨ha', hq⟩ => ⟨?_, ?_⟩
  · exact ⟨fun r hr => by
      rw [ha'.1 r hr, hg r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
        (by rintro rfl; simp [preserved] at hr)], by rw [ha'.2.1, hsp'], fun r hr => by rw [ha'.2.2 r hr, hv]⟩
  · rw [openAArch64, Contract.post_mk] at hq
    rw [openToN, Contract.post_mk, openToRes]
    rw [hm, hg .x0 (by decide) (by decide) (by decide), hg .x1 (by decide) (by decide) (by decide),
      hg .x2 (by decide) (by decide) (by decide), hg .x3 (by decide) (by decide) (by decide),
      hg .x4 (by decide) (by decide) (by decide), hg .x5 (by decide) (by decide) (by decide), h6, h8] at hq
    exact hq

theorem openTo_ct (v : Proof.ChaCha20.AArch64.XorImpl) :
    ConstantTime isa openToN.pre openToN.pub (openTo v.callee v.stitched) := by
  show ConstantTime isa _ _ (.seq (.block [mov .x8 .x6, .ldrSp .x6 0, .ldrSp .x7 8]) (openCode v.callee v.stitched))
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨psp, p0, p1, p2, p3, p4, p5, p6, p7, a0, a1⟩, hl⟩ := hq
  obtain hok : (openToRes σ₁).isSome = (openToRes σ₂).isSome := leak_bool hl
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨-, -, -, -, -, ha₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp₁⟩ := h₁'
  obtain ⟨-, -, -, -, -, ha₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp₂⟩ := h₂'
  refine (rel_seq (rel_taint [] psp (by simp) toEntry_taint) (toEntry_ok ha₁ hsp₁) (toEntry_ok ha₂ hsp₂) ?_
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  rintro u₁ u₂ ⟨g₁, x8₁, x6₁, x7₁, m₁, rd₁, wr₁, sp₁, -⟩ ⟨g₂, x8₂, x6₂, x7₂, m₂, rd₂, wr₂, sp₂, -⟩
  have hg (r : Reg) (h : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5]) : u₁.gpr r = u₂.gpr r := by
    obtain h' : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := by revert r; decide
    rw [g₁ r h'.1 h'.2.1 h'.2.2, g₂ r h'.1 h'.2.1 h'.2.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine openBody_rel v (preTo_body h₁ g₁ x8₁ x6₁ x7₁ rd₁ wr₁) (preTo_body h₂ g₂ x8₂ x6₂ x7₂ rd₂ wr₂)
    (fun r hr => ?_) (by rw [sp₁, sp₂, psp]) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [x6₁, x6₂, a0]
    · rw [x7₁, x7₂, a1]
    · rw [x8₁, x8₂, p6]
  · unfold okAArch64
    rw [m₁, m₂, g₁ .x0 (by decide) (by decide) (by decide), g₁ .x1 (by decide) (by decide) (by decide),
      g₁ .x2 (by decide) (by decide) (by decide), g₁ .x3 (by decide) (by decide) (by decide),
      g₁ .x4 (by decide) (by decide) (by decide), g₁ .x5 (by decide) (by decide) (by decide), x6₁,
      g₂ .x0 (by decide) (by decide) (by decide), g₂ .x1 (by decide) (by decide) (by decide),
      g₂ .x2 (by decide) (by decide) (by decide), g₂ .x3 (by decide) (by decide) (by decide),
      g₂ .x4 (by decide) (by decide) (by decide), g₂ .x5 (by decide) (by decide) (by decide), x6₂]
    exact hok

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 1280⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read,
and its whole working space of 1312 bytes writable). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x4000, 1312⟩]

theorem seal_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (sealCode v.callee v.stitched) (sealScratchContract AArch64.abi 160) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealAArch64,
      Proof.ChaCha20Poly1305.preAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [sealSat] using sealSat)

open VG.AArch64 in
/-- `open`'s precondition with its whole working space, `work` (1312 bytes),
writable: what its contract gives, whose regions cover `preInAArch64`'s, the
context and the 32 bytes after it (`preOpenW_narrow`). -/
def preOpenW (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let work : Region := ⟨s.gpr .x7, 1312⟩
  s.rd = [key, nonce, aad, tag] ∧ s.wr = [data, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  (s.gpr .x7).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64

/-- `openInAArch64`, with `preOpenW`. -/
def openW : Contract AArch64.isa where
  pre := preOpenW
  post := openInAArch64.post
  pub := openInAArch64.pub

/-- The regions `preInAArch64` permits writing: the data, the context and the
32 bytes after it. -/
def openWr (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 1280⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩]

theorem preOpenW_narrow {s : State} (h : preOpenW s) : preInAArch64 (s.withRegions s.rd (openWr s)) := by
  obtain ⟨hrd, -, c_k, c_n, c_a, c_d, c_t, d_k, d_n, d_a, d_t, wc, wa, wd, wt, wk, wn⟩ := h
  obtain sc : Region.Sub ⟨s.gpr .x7, 1280⟩ ⟨s.gpr .x7, 1312⟩ := Region.sub_prefix (by decide)
  obtain ss : Region.Sub ⟨s.gpr .x7 + BitVec.ofNat 64 1280, 32⟩ ⟨s.gpr .x7, 1312⟩ := sub_off _ (by decide)
  obtain m0 : (⟨s.gpr .x0, 32⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m1 : (⟨s.gpr .x1, 12⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m2 : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m6 : (⟨s.gpr .x6, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  exact ⟨m0, m1, m2, m6, rfl, c_k.sub_left sc, c_n.sub_left sc, c_a.sub_left sc,
    c_d.sub_left sc, c_t.sub_left sc, d_k, d_n, d_a, d_t,
    c_k.sub_left ss, c_n.sub_left ss, c_a.sub_left ss, c_d.sub_left ss, c_t.sub_left ss, wc, wa, wd, wt, wk, wn⟩

theorem openWr_covers {s : State} (h : preOpenW s) : Covers (openWr s) s.wr := by
  rw [h.2.1]
  refine Covers.of_sub fun r hr => ?_
  simp only [openWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, (BitVec.add_zero _).symm,
      show 0 + 1280 ≤ 1312 by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 1280, rfl, show 1280 + 32 ≤ 1312 by decide⟩

/-- The postcondition of a contract given by its fields, as a rewrite. The kernel compares two
`match`es on `decrypt` that are not the same term by evaluating `decrypt`, so the postconditions
below are unfolded by rewriting, not by unification. -/
private theorem contract_post_mk {M : ISA} (pre : M.State → Prop) (post : M.State → M.State → Prop)
    (pub : M.State → M.State → Prop) : (Contract.mk pre post pub).post = post := rfl

/-- `openInAArch64`'s postcondition, which reads only the memory and the registers, gives `openW`'s. -/
private theorem openW_post_of {t t' u u' : State} (h : openInAArch64.post t t') (hm : t.mem = u.mem)
    (hg : t.gpr = u.gpr) (hm' : t'.mem = u'.mem) (hg' : t'.gpr = u'.gpr) : openW.post u u' := by
  rw [openW, contract_post_mk, openInAArch64, contract_post_mk]
  rw [openInAArch64, contract_post_mk, hm, hg, hm', hg'] at h
  exact h

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openW_implies : openW.Implies (openZeroScratchContract AArch64.abi 164) :=
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, AArch64.abi, AArch64.argRegs]
        simp only [openW, openInAArch64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openZeroPost,
          Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openLeakAArch64, openW, preOpenW,
          openInAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
          [openSat] using openSat }

/-- `open` against `openInAArch64`, whose precondition permits writing only the
data, the context and the 32 bytes after it. -/
theorem open_verifiedN (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) openInAArch64 :=
  ⟨openIn_ok v, openIn_ct v, openW_implies.sat_left.elim fun _ hs => ⟨_, preOpenW_narrow hs⟩⟩

/-- Then against `openW`, which permits writing all of `work`: the code runs as
it does with fewer permissions (`RegionModel.verified_narrowTo`). -/
theorem open_verifiedW (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) openW :=
  regionModel.verified_narrowTo (T := AArch64.target) (fun _ _ _ _ h => h) (open_verifiedN v)
    State.rd openWr (fun _ hs => preOpenW_narrow hs)
    (fun _ hs => (Covers.refl _).append (openWr_covers hs)) (fun _ hs => openWr_covers hs)
    (fun _ _ _ h => openW_post_of h rfl rfl rfl rfl) (fun _ _ _ _ h => h) openW_implies.sat_left

theorem open_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openInPlace v.callee v.stitched) (openZeroScratchContract AArch64.abi 164) :=
  Verified.of_implies (open_verifiedW v) openW_implies

open VG.AArch64 in
/-- `open_to`'s precondition with its whole working space, `work` (1312
bytes), writable: what its contract gives (`tag` and `work` on the stack). -/
def preToW (s : AArch64.State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let src : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let dst : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1312⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  s.rd = [key, nonce, aad, src, tag, args] ∧ s.wr = [dst, work] ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint src ∧
  work.Disjoint dst ∧ work.Disjoint tag ∧
  dst.Disjoint key ∧ dst.Disjoint nonce ∧ dst.Disjoint aad ∧ dst.Disjoint src ∧ dst.Disjoint tag ∧
  (stackArg s 1).toNat + 1312 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
  (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧
  s.sp.toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat = (s.gpr .x5).toNat

/-- `openToN`, with `preToW`. -/
def openToW : Contract AArch64.isa where
  pre := preToW
  post := openToN.post
  pub := openToN.pub

/-- The regions `preToN` permits writing: the destination, the context and the
32 bytes after it. -/
def toWr (s : State) : List Region :=
  [⟨s.gpr .x6, (s.gpr .x5).toNat⟩, ⟨stackArg s 1, 1280⟩, ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩]

theorem preToW_narrow {s : State} (h : preToW s) : preToN (s.withRegions s.rd (toWr s)) := by
  obtain ⟨hrd, -, ck, cn, ca, cs, cq, ct, qk, qn, qa, qs, qt, wc, wa, ws, wq, wt, wk, wn, wsp, h75⟩ := h
  obtain sc : Region.Sub ⟨stackArg s 1, 1280⟩ ⟨stackArg s 1, 1312⟩ := Region.sub_prefix (by decide)
  obtain ss : Region.Sub ⟨stackArg s 1 + BitVec.ofNat 64 1280, 32⟩ ⟨stackArg s 1, 1312⟩ := sub_off _ (by decide)
  obtain eq : (⟨s.gpr .x6, (s.gpr .x5).toNat⟩ : Region) = ⟨s.gpr .x6, (s.gpr .x7).toNat⟩ := by rw [h75]
  obtain m0 : (⟨s.gpr .x0, 32⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m1 : (⟨s.gpr .x1, 12⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m2 : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain m4 : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain mt : (⟨stackArg s 0, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  obtain ma : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  rw [← eq] at cq qk qn qa qt qs
  rw [h75] at wq
  exact ⟨m0, m1, m2, mt, m4, ma, rfl, ck.sub_left sc, cn.sub_left sc,
    ca.sub_left sc, cs.sub_left sc, ct.sub_left sc, cq.sub_left sc, qk, qn, qa, qt, qs.symm,
    ck.sub_left ss, cn.sub_left ss, ca.sub_left ss, cs.sub_left ss, ct.sub_left ss,
    cq.sub_left ss, wc, wa, ws, wq, wt, wk, wn, wsp⟩

theorem toWr_covers {s : State} (h : preToW s) : Covers (toWr s) s.wr := by
  obtain ⟨-, hw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h75⟩ := h
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  simp only [toWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, by simp only [h75]; omega_using []⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, (BitVec.add_zero _).symm,
      show 0 + 1280 ≤ 1312 by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 1280, rfl, show 1280 + 32 ≤ 1312 by decide⟩

/-- `openToN`'s postcondition, which reads only `openToRes`, the memory and the registers, gives
`openToW`'s. -/
private theorem openToW_post_of {t t' u u' : State} (h : openToN.post t t') (hr : openToRes t = openToRes u)
    (hg : t.gpr = u.gpr) (hm' : t'.mem = u'.mem) (hg' : t'.gpr = u'.gpr) : openToW.post u u' := by
  rw [openToW, contract_post_mk, openToN, contract_post_mk]
  rw [openToN, contract_post_mk, hr, hg, hm', hg'] at h
  exact h

/-- The indices of `open_to`'s two stack arguments, for the calling
convention's evaluation. -/
theorem range2 : List.range 2 = [0, 1] := rfl

/-- A state satisfying `open_to`'s precondition (as `sealSat`, with no source
and no destination): the stack arguments at `0x9000`, `tag` (`0x3000`) and
`work` (`0x4000`). -/
def openToSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x2200
    | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x30 else bif Nat.beq a.toNat 0x9009 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x2200, 0⟩, ⟨0x4000, 1312⟩]

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem openToW_implies : openToW.Implies (openToScratchContract AArch64.abi 164) :=
    { pre := by
        intro s h
        sig_pre [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] at h
        sig_split h
        -- The facts of the stack arguments' regions, which `sig_split` leaves together.
        rename_i hc _ _ _ _ _ _ _ _
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.false_or, Bool.true_or, List.cons_append, List.nil_append,
          Sig.conj_cons_cons, Sig.conj_single] at hc
        obtain ⟨-, hta, -⟩ := hc
        sig_reduce [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil]
        sig_simp [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | (sig_simp_only [Nat.mul_comm] at *
             first | with_reducible assumption | sig_disjoint_symm)
          | simp only [*, List.mem_cons, List.mem_singleton, true_or, or_true]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPost, AArch64.abi, AArch64.argRegs, range2]
        simp only [openToW, openToN, openToRes] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil] at h
        sig_split h
        rename_i hsp hl h0 h1 h2 h3 h4 h5 h6 h7 a0
        exact ⟨⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, h⟩, hl⟩
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract,
          Proof.ChaCha20Poly1305.openToScratchSig, Spec.ChaCha20Poly1305.openToPre,
          Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak, openToW, preToW, openToN,
          openToRes, openToLeakAArch64, pubToAArch64, AArch64.abi, AArch64.argRegs, range2, List.append_eq,
          List.getD_cons_succ, List.getD_cons_zero, List.filterMap_cons, List.filterMap_nil, Bool.cond_true,
          Bool.cond_false, Sig.pairFacts, List.cons_append, List.nil_append, List.append_nil]
          [openToSat, AArch64.stackArg, AArch64.stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax]
          using openToSat }

/-- `open_to` against `openToN`, whose precondition permits writing only the
destination, the context and the 32 bytes after it. -/
theorem openTo_verifiedN (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) openToN :=
  ⟨openTo_ok v, openTo_ct v, openToW_implies.sat_left.elim fun _ hs => ⟨_, preToW_narrow hs⟩⟩

theorem openTo_verifiedW (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) openToW :=
  regionModel.verified_narrowTo (T := AArch64.target) (fun _ _ _ _ h => h) (openTo_verifiedN v)
    State.rd toWr (fun _ hs => preToW_narrow hs)
    (fun _ hs => (Covers.refl _).append (toWr_covers hs)) (fun _ hs => toWr_covers hs)
    (fun _ _ _ h => openToW_post_of h rfl rfl rfl rfl) (fun _ _ _ _ h => h) openToW_implies.sat_left

theorem openTo_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openTo v.callee v.stitched) (openToScratchContract AArch64.abi 164) :=
  Verified.of_implies (openTo_verifiedW v) openToW_implies

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State := { sealSat with wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, AArch64.abi, AArch64.argRegs] [sealFrameSat, sealSat]
    using sealFrameSat

theorem seal_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96 (sealCode v.callee v.stitched))
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi 1280) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 160) (post := Spec.ChaCha20Poly1305.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1280) (words := 96) (seal_verified v) (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State := { openSat with wr := [⟨0x2100, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1312).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, AArch64.abi, AArch64.argRegs]
    [openFrameSat, openSat] using openFrameSat

theorem open_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1312 .x7 96 (openInPlace v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openZeroContract AArch64.abi 1312) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 164) (post := Spec.ChaCha20Poly1305.openZeroPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openLeak AArch64.abi.ptrBits))
    (bytes := 1312) (words := 96) (open_verified v) (by decide) (by decide) (by decide)
    (openZeroPost_out _) openFrameSat_pre

/-- A state satisfying `open_to`'s precondition, without the working space:
the stack argument `tag` (`0x3000`) at `0x9000`. -/
def openToFrameSat : State :=
  { openToSat with mem a := bif Nat.beq a.toNat 0x9001 then 0x30 else 0,
                   rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x9000, 8⟩],
                   wr := [⟨0x2200, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract AArch64.abi 1328).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    AArch64.abi, AArch64.argRegs]
    [openToFrameSat, openToSat, AArch64.stackArg, AArch64.stackArgAddr, Mem.readW, Mem.read,
      Spec.ChaCha20Poly1305.pMax]
    using openToFrameSat

theorem openTo_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratchWiped 1328 1 96 (openTo v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openToContract AArch64.abi 1328) :=
  AArch64.Verified.stackArgScratchWipedPre (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work")
    (e := .u64) (n := 164) (pre := Spec.ChaCha20Poly1305.openToPre AArch64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openToLeak AArch64.abi.ptrBits))
    (bytes := 1328) (words := 96) (openTo_verified v) (by decide) (by decide) (by decide)
    (openToPre_local _) (openToPost_local _) (openToPost_out _) openToFrameSat_pre
    (hleak := openToLeak_local _)

end VG.Proof.ChaCha20Poly1305.AArch64
