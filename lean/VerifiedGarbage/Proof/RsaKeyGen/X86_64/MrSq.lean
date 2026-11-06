module

public import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrBit
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-!
# A candidate on x86-64: Miller–Rabin's squarings

`ECtx`: the exponent `E` in `aE` and the lowest set bit of `c − 1`'s lowest
nonzero word after it. `mrSq_ok`: `y := y²` (as `y R mod c`) and the flag
or'ed with `y = c − 1`; `mrLast_ok`: the same, under the mask of `σ > j`
from that bit.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- The exponent of a candidate `c`: `E` in `aE`, and after its `w` words
the lowest set bit `2^(a mod 64)` of `c − 1`'s lowest nonzero word. -/
structure ECtx (m : Mem) (B : Addr) (w c : Nat) : Prop where
  e : wv m B (slot w aE) w = mrE c
  l : word m B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64)

/-- `ECtx` survives changes away from `aE`. -/
theorem ECtx.of_frm {m m' : Mem} {B : Addr} {w c : Nat} {rs : List (Nat × Nat)} (h : ECtx m B w c)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE)
    (hn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64) : ECtx m' B w c :=
  ⟨by rw [hf.wv_eq (fun r hr => by have := hd r hr; omega) (by omega)]; exact h.e,
    by rw [hf.word_eq (fun r hr => by have := hd r hr; omega) (by omega)]; exact h.l⟩

theorem aE_fits {B : Addr} {Z w : Nat} (hd : MrDims B Z w) : slot w aE + 8 * (w + 2) ≤ Z := by
  have h := hd.x
  have e1 : slot w aRm1 = 256 + 26 * (8 * (w + 2)) := rfl
  have e2 : slot w aE = 256 + 24 * (8 * (w + 2)) := rfl
  omega

/-- What a squaring changes. -/
def sqRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * kFlag, 8)]

/-- `sqRanges`'s ranges, in the header and in the arrays. -/
theorem sqRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(176, 8)]
    [(2, 1), (3, 1), (6, 1)] (sqRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    sqRanges, Public.aAcc, Public.aTmp, Public.aY, aAcc, aTmp, aY, sFn, kFlag, kPlen] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)

theorem mrSq_eq (mul : Nat → Nat → Nat → Prog isa) : mrSq mul =
    [mul aY aY aY] ++ (eqMask aRm1 ++
      ([.block [.mov .rax (.mem (hdr kFlag)), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax]] :
        List (Prog isa))) := rfl

/-- `y := y²`, as `y R mod c` in `aY`: the multiplication, then the mask of
`y = c − 1` into `rbp`. -/
theorem sqHead_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm y : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) :
    WP isa (seqs ([M.mm aY aY aY] ++ eqMask aRm1)) s fun t =>
      MrCtx t B Z w mi c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      t.gpr .rbp = mask (decide (y * y % c = c - 1)) ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_arith
  refine wp_seqs_append (by simp) (by simp [eqMask]) ?_
  simp only [seqs]
  refine WP.mono (M.mm_ok hg hZ (by omega_arith) hw' (o := aY) (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨hg₁, hlt₁, hy₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hy₁
  rw [hY] at hy₁
  have hY₁ : wv s₁.mem B (slot w aY) w = y * y % c * 2 ^ (64 * w) % c := mont_val hR hlt₁ hy₁ rfl rfl
  have hf₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem s₁.mem :=
    Frm.of_arrays ha₁ (by simp)
  have hc₁ : MrCtx s₁ B Z w mi c bm := hc.of_frm hd hf₁ hg₁.scr hg₁.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  refine WP.mono (eqMask_ok hg₁ hZ (by omega_arith) hw' (j := aRm1) (by decide) hXZ)
    fun t ⟨hbp, hm, k⟩ => ?_
  have hlt2 : y * y % c < c := Nat.mod_lt _ hc0
  have em1 : decide (y * y % c * 2 ^ (64 * w) % c = c - 2 ^ (64 * w) % c) = decide (y * y % c = c - 1) :=
    decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt2)
  rw [hY₁, hc₁.rm1, em1] at hbp
  have hft : Frm B [] s₁.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  refine ⟨hc₁.of_frm hd hft (hg₁.scr.congr k.2.2) ((k.gpr (by decide)).trans hg₁.rdi) (by simp) (by simp) (by simp)
    (by simp) (by simp), by rw [hm]; exact hY₁, hbp, by rw [hm]; exact hf₁, (k₁.trans k).mono (by decide)⟩

/-- `mrSq`: `y := y²` and the flag or'ed with `y = c − 1`. -/
theorem mrSq_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm y : Nat} {P : Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P) :
    WP isa (seqs (mrSq M.mm)) s fun t =>
      MrCtx t B Z w mi c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (P || decide (y * y % c = c - 1)) ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  have hZ := hd.z
  rw [mrSq_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (sqHead_ok M hd hc hodd hc1 hY) fun s₁ ⟨hc₁, hY₁, hbp, hf₁, k₁⟩ => ?_
  have hg₁ := hc₁.good
  have hP₁ : word s₁.mem B (8 * kFlag) = mask P := by
    rw [hf₁.word_eq (d := 8 * kFlag) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kFlag kPlen sFn; omega_arith)]; exact hP
  have hl : InRegions (s₁.rd ++ s₁.wr) (off B (8 * kFlag)) 8 :=
    hg₁.scr.ld (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  have hs : InRegions s₁.wr (off B (8 * kFlag)) 8 :=
    hg₁.scr.st (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  simp only [seqs]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kFlag))
      (mask (P || decide (y * y % c = c - 1)))) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl, hs, hP₁, hbp, mask_or2]) rfl) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kFlag, 8)] s₁.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by unfold kFlag kPlen sFn; omega_arith)) (by simp)
  have hgt : Good t B Z w mi := ⟨hg₁.scr.congr k.2.2, (k.gpr (by decide)).trans hg₁.rdi,
    Hdr.of_frm hg₁.hdr hft (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl)⟩
  refine ⟨hc₁.of_frm hd hft hgt.scr hgt.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl),
    ?_, by rw [hm, word_writeW_self], ?_, (k₁.trans k).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith)]; exact hY₁
  · exact (hf₁.mono (by simp [sqRanges])).trans (hft.mono (by simp [sqRanges]))

theorem sigK_and (j : Nat) (hj : 1 ≤ j ∧ j ≤ 3) {k : Nat} (hk : k < 64) :
    (sigK j &&& BitVec.twoPow 64 k = 0) = ¬ (j < sigOf k) := by
  rw [BitVec.and_comm]
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl
  · exact sig_mask1 k hk
  · exact sig_mask2 k hk
  · exact sig_mask3 k hk

theorem mask_def' (b : Bool) : 0#64 - BitVec.setWidth 64 (BitVec.ofBool b) = mask b := rfl

theorem mask_and3 (a b : Bool) : mask a &&& mask b = mask (a && b) := by cases a <;> cases b <;> decide

theorem mask_ne0 (b : Bool) :
    mask b ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = mask (!b) := by cases b <;> decide

/-- `mrLast j`: `y := y²` and the flag or'ed with `y = c − 1` if `σ > j`. -/
theorem mrLast_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm y : Nat} {P : Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w mi c bm ∧ wv t.mem B (slot w aY) w = (y * y % c) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (P || (decide (y * y % c = c - 1) && decide (j < mrSig c))) ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  have hZ := hd.z
  have hXZ := hd.x
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  unfold mrLast
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (sqHead_ok M hd hc hodd hc1 hY) fun s₁ ⟨hc₁, hY₁, hbp, hf₁, k₁⟩ => ?_
  have hg₁ := hc₁.good
  have hP₁ : word s₁.mem B (8 * kFlag) = mask P := by
    rw [hf₁.word_eq (d := 8 * kFlag) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kFlag kPlen sFn; omega_arith)]; exact hP
  have hE₁ : ECtx s₁.mem B w c := hE.of_frm hf₁ (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (by unfold slot aE aRm1 at *; omega_arith)
  simp only [seqs]
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  have hl : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₂.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hs : InRegions s₂.wr (off B (8 * kFlag)) 8 :=
    hg₂.scr.st (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  have hL : word s₂.mem B (slot w aE + 8 * w) = BitVec.twoPow 64 (mrA c % 64) := by rw [hm₂]; exact hE₁.l
  have hbp₂ : s₂.gpr .rbp = mask (decide (y * y % c = c - 1)) := (k₂.gpr (by decide)).trans hbp
  have hσ : (!decide (sigK j &&& BitVec.twoPow 64 (mrA c % 64) = 0)) = decide (j < mrSig c) := by
    have h := sigK_and j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
    rw [sigOf_mod] at h
    unfold mrSig; simp only [h, decide_not, Bool.not_not]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r12] (Q := fun t => t.mem = s₂.mem.writeW (off B (8 * kFlag))
      (mask (P || (decide (y * y % c = c - 1) && decide (j < mrSig c))))) (by
    xrun [State.ea, hdr, ix, hg₂.rdi, hdrOff, hl kFlag (by decide), hl sW (by decide), hs, hg₂.hdr.hw, hbx,
      addr0 rfl rfl, hg₂.scr.ld (d := slot w aE + 8 * w) (by unfold slot aE aRm1 at *; omega_arith), hL,
      (hm₂ ▸ hP₁ : word s₂.mem B (8 * kFlag) = mask P), hbp₂, decide_lt_one, mask_def', mask_ne0, mask_and3, hσ, mask_or2]) rfl) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kFlag, 8)] s₁.mem t.mem := by
    rw [hm, hm₂]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by unfold kFlag kPlen sFn; omega_arith)) (by simp)
  have hgt : Good t B Z w mi := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₁.hdr hft (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl)⟩
  refine ⟨hc₁.of_frm hd hft hgt.scr hgt.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl),
    ?_, by rw [hm, word_writeW_self], ?_, ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hm₂]; exact hY₁
  · exact (hf₁.mono (by simp [sqRanges])).trans (hft.mono (by simp [sqRanges]))

end VG.Proof.RsaKeyGen.X86_64
