import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2

/-!
# A candidate on x86-64: Montgomery arithmetic modulo `c`

The start of `montSetup`: `-c⁻¹ mod 2^64` into the header (`msHead_ok`),
the number 1 (`aOne`), `R² mod c` (`aR2`: `2^(64 w − 1)`, the top bit of
the candidate, doubled `w + 1` times and squared six times, `msR2_ok`), and
`R mod c` (`aY`, `msY_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `-c⁻¹ mod 2^64` into `sMinv`, `rdx = 1`, `rcx = 0`. -/
theorem msHead_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .r10))] :
      List Instr) ++ minv ++ ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr))) s
      fun t =>
      Good t B Z w (t.gpr .r15) ∧ ((word s.mem B (slot w aN)).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      t.gpr .rdx = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = s.mem.writeW (off B (8 * sMinv)) (t.gpr .r15) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .r10, .r12, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r12, .rbx] (Q := fun t => t.gpr .r10 = off B (slot w aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = word s.mem B (slot w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hg.hdr.hw,
      hg.hdr.harr aN (by decide), show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hg.scr.ld (d := slot w aN) (by omega)]) rfl) fun s₁ ⟨⟨h10, h12, hbx, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (minv_ok s₁ (by rw [hbx]; exact hodd)) fun s₂ ⟨hinv, k₂, hm₂⟩ => ?_
  rw [hbx] at hinv
  have hs₂ := (hg.scr.congr k₁.2.2).congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
      t.mem = s₂.mem.writeW (off B (8 * sMinv)) (s₂.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (d := 8 * sMinv) (by
      have := hdr_lt_slot w 8 (show sMinv < 32 by decide); omega)]) rfl)
    fun t ⟨⟨hdx, hcx, hm⟩, k⟩ => ?_
  have h15 : t.gpr .r15 = s₂.gpr .r15 := k.gpr (by decide)
  have hm' : t.mem = s.mem.writeW (off B (8 * sMinv)) (t.gpr .r15) := by rw [hm, hm₂, hm₁, h15]
  refine ⟨⟨hs₂.congr k.2.2, (k.gpr (by decide)).trans hdi₂, ?_⟩, by rw [h15]; exact hinv, hdx, hcx,
    (k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12), hm', ((k₁.trans k₂).trans k).mono (by decide)⟩
  rw [hm']
  exact ⟨by rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hg.hdr.hw, word_writeW_self _ _ _ _,
    fun j hj => (hdrStore_hdr _ _ _ (by decide) (by unfold sArr; omega) (by unfold sArr sMinv; omega)).trans
      (hg.hdr.harr j hj)⟩

/-- The steps of `R² mod c`. -/
def msR2 (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block [.movImm64 .rdx (BitVec.ofNat 64 (2 ^ 63)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sW)), .alu .add .rcx (.imm 1)],
  doubles aN aAcc aTmp aR2 kT0,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2]

/-- What `R² mod c` changes. -/
def msR2Ranges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aR2, 8 * (w + 2)), (8 * kT0, 8)]

/-- `R² mod c` for the odd `c` of `w` words, its top bit set. -/
theorem msR2_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {N : Nat} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hodd : N % 2 = 1) (htop : 2 ^ (64 * w - 1) ≤ N) :
    WP isa (seqs (msR2 M.mm)) s fun t => Good t B Z w mi ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (msR2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  have hv0 : 2 ^ 63 * 2 ^ (64 * (w - 1)) < N := by
    have e : 2 ^ 63 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w - 1) := by rw [← Nat.pow_add]; congr 1; omega
    have : 2 ^ (64 * w - 1) % 2 = 0 := by
      rw [show 64 * w - 1 = (64 * w - 2) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
    rw [e]; omega
  unfold msR2
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 (2 ^ 63) ∧
      t.gpr .rcx = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) (by
    xrun [h12, ofNat64_pred (show 1 ≤ w by omega) (by omega)]) rfl) fun t₃ ⟨⟨hdx₃, hcx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs.congr k₃.2.2
  have hH₃ : Hdr t₃.mem B w mi := by rw [hm₃]; exact hg.hdr
  have hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hg.rdi
  refine WP.seq (WP.mono (setWord_ok hs₃ hdi₃ hH₃ hZ ((k₃.gpr (by decide)).trans h12) (by omega) hw' (o := aR2)
    (by decide) (ri := .rcx) (by decide) (i := w - 1) (by omega) hcx₃) fun t₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  rw [hdx₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 ^ 63 < 2 ^ 64 by decide)] at hv₄
  have hs₄ := hs₃.congr k₄.2.2
  have ha₄ : Arrays B w [aR2] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hH₄ : Hdr t₄.mem B w mi := ha₄.hdr hH₃
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans hdi₃
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (w + 1) ∧
      t.mem = t₄.mem) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sW) (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
      hH₄.hw, sx1, ofNat_add_one]) rfl) fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have hN₄ : wv t₄.mem B (slot w aN) w = N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃]; exact hn
  have hw0₄ : word t₄.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₄.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₃]
  refine WP.seq (WP.mono (doubles_ok hs₅ ((k₅.gpr (by decide)).trans hdi₄) (hm₅ ▸ hH₄) hZ hw hw'
    (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sl := kT0) (by decide) (by decide)
    (c := w + 1) (by omega) (by omega) hcx₅ (by rw [hm₅, hv₄, hN₄]; exact hv0))
    fun t₆ ⟨hv₆, hf₆, hH₆, k₆⟩ => ?_)
  rw [hm₅, hv₄, hN₄, show 2 ^ (w + 1) * (2 ^ 63 * 2 ^ (64 * (w - 1))) = 2 ^ w * 2 ^ (64 * w) by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega] at hv₆
  have hf₆' : Frm B (msR2Ranges w) t₅.mem t₆.mem := hf₆
  have hg₆ : Good t₆ B Z w mi := ⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans hdi₄),
    hH₆⟩
  have harr : ∀ {j : Nat}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aR2 → ∀ r ∈ msR2Ranges w,
      slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3
    have := hdr_lt_slot w j (show kT0 < 32 by decide)
    have s1 := slot_sep (w := w) h1
    have s2 := slot_sep (w := w) h2
    have s3 := slot_sep (w := w) h3
    simp only [msR2Ranges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> omega
  have hNf : wv t₆.mem B (slot w aN) w = N := by
    rw [hf₆'.wv_eq (fun r hr => by have := harr (show aN < 8 by decide) (by decide) (by decide) (by decide) r hr; omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega), hm₅]; exact hN₄
  have hW0 : word t₆.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hf₆'.word_eq (fun r hr => by have := harr (show aN < 8 by decide) (by decide) (by decide) (by decide) r hr; omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega), hm₅, hw0₄]
  show WP isa (seqs (List.replicate (5 + 1) (M.mm aR2 aR2 aR2))) t₆ _
  refine WP.mono (sqs_ok M 5 hg₆ hZ hw hw' hR (E := w) hNf (by rw [hW0]; exact hinv)
    (by rw [hv₆]; exact Nat.mod_lt _ hN0) (by rw [hv₆, Nat.mod_mod]))
    fun t ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, ?_, ?_, ((((k₃.trans k₄).trans k₅).trans k₆).trans h5).mono (by decide)⟩
  · rw [← Nat.mod_eq_of_lt h2, h3, ← Nat.pow_add]
  · have f₄ : Frm B (msR2Ranges w) s.mem t₄.mem := by
      rw [← hm₃]; exact Frm.of_arrays ha₄ (by simp [msR2Ranges])
    exact ((f₄.trans (by rw [hm₅]; exact Frm.refl _ _ _)).trans hf₆').trans
      (Frm.of_arrays h4 (by simp [msR2Ranges]))

end VG.Proof.RsaKeyGen.X86_64
