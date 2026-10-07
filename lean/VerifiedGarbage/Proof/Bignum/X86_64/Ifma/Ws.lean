import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Post
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain

/-!
# RSA with AVX512_IFMA on x86-64: the workspaces around the IFMA branch

Lemmas for `CrtIfma`'s branch (`Branch.lean`, `Main.lean`): what stays
of `n`'s workspace below the primes' (`NSafe`), what `pre` leaves (`APost`),
and the checks' state after the sizes' test (`CrtReady.of_regs`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Ranges that keep `n`'s values and header but `aAcc`, `aTmp`, `aY`, `aX`,
`sD` and `sCnt`: those of `gRanges`, `aX`, and anything above `n`'s arrays. -/
def NSafe (w : Nat) (rs : List (Nat × Nat)) : Prop :=
  ∀ r ∈ rs, r ∈ gRanges w ∨ r = (slot w Public.aX, 8 * (w + 2)) ∨ slot w 8 ≤ r.1

theorem nsafe_wv {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : NSafe w rs) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY)
    (h4 : j ≠ Public.aX) (hz : slot w 8 ≤ 2 ^ 64) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  refine hf.wv_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := slot_sep (w := w) h1
    have := slot_sep (w := w) h2
    have := slot_sep (w := w) h3
    have := hdr_lt_slot w j (show Crt.sD < 32 by decide)
    have := hdr_lt_slot w j (show Public.sCnt < 32 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega
  · subst h; have := slot_sep (w := w) h4; simp only; omega
  · exact .inl (by omega)

theorem nsafe_word {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : NSafe w rs) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    word m' B (8 * i) = word m B (8 * i) := by
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := hdr_lt_slot w Public.aAcc hi
    have := hdr_lt_slot w Public.aTmp hi
    have := hdr_lt_slot w Public.aY hi
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
      unfold Crt.sD sFn at h1 ⊢; omega
    · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
      unfold Public.sCnt sFn at h2 ⊢; omega
  · subst h; have := hdr_lt_slot w Public.aX hi; exact .inl (by simp only; omega)
  · exact .inl (by omega)

theorem NVals.of_nsafe {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N : Nat} (h : NVals s B w minv N)
    {rs : List (Nat × Nat)} (hf : Frm B rs s.mem t.mem) (hr : NSafe w rs) (hz : slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    NVals t B w minv N := by
  have lN := slot_le (w := w) (show Public.aN < 8 by decide)
  have hN0 := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
  have e := fun {j} (hj : j < 8) h1 h2 h3 h4 => nsafe_wv (j := j) hf hr hj h1 h2 h3 h4 hz
  refine ⟨by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.n, ?_,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2lt,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.one⟩
  have := (wv_mod64 t.mem B (slot w Public.aN) (n := w) hw).symm
  rw [this, e (by decide) (by decide) (by decide) (by decide) (by decide), wv_mod64 s.mem B (slot w Public.aN) hw]
  exact h.inv

theorem preRanges_nsafe {w op wp oq wq : Nat} (hp : slot w 8 ≤ op) (hq : slot w 8 ≤ oq) :
    NSafe w (preRanges w op wp oq wq) := fun r hr => by
  simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | rfl | rfl | rfl
  · exact .inl hr
  · exact .inr (.inl rfl)
  · exact .inr (.inr (by simp only [xRange]; omega))
  · exact .inr (.inr (by simp only [xRange]; omega))

theorem above_nsafe {w L : Nat} {rs : List (Nat × Nat)} (hL : slot w 8 ≤ L) (hr : ∀ r ∈ rs, L ≤ r.1) :
    NSafe w rs := fun r h => .inr (.inr (by have := hr r h; omega))

/-- What `pre` leaves (`pre_ok`), from `s`. -/
def APost (s t : State) (B : Addr) (Z w op oq wp : Nat) (minv mp mq : BitVec 64) (N P Q C : Nat) : Prop :=
  Good t B Z w minv ∧ NVals t B w minv N ∧ PrimeRdy t B op wp mp N P C ∧ PrimeRdy t B oq wp mq N Q C ∧
    Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ Keep mmRegs s t ∧
    word t.mem (off B op) (8 * sMaskX) = word s.mem (off B op) (8 * sMaskX)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont' {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

end VG.Proof.Bignum.X86_64

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem ofNat_eq_iff {n v : Nat} (hn : n < 2 ^ 64) (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 n = BitVec.ofNat 64 v ↔ n = v :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hv] at this,
   fun h => h ▸ rfl⟩

theorem mx_ffff (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_and]
  have : (0xFFFF : BitVec 32).getLsbD (6 + i) = true := by
    rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; omega
  rw [this, Bool.and_true]

/-- The checks' state, across a change of `rax` and `rdx` only. -/
theorem CrtReady.of_regs {s t t' : State} {B : Addr} {Z w pl ql : Nat} {minv mp mq : BitVec 64} {N C P Q : Nat}
    {M : Bool} (h : CrtReady s t B Z w pl ql minv mp mq N C P Q M) (hm : t'.mem = t.mem)
    (k : Keep [.rax, .rdx] t t') : CrtReady s t' B Z w pl ql minv mp mq N C P Q M := by
  have hx : ∀ {X : Nat} {o wx : Nat} {mx : BitVec 64}, XVals t B o wx mx X → XVals t' B o wx mx X :=
    fun hx => by rw [show t' = { t' with mem := t.mem } by rw [← hm]]; exact ⟨hx.n, hx.inv, hx.one⟩
  have hN : NVals t' B w minv N := by
    rw [show t' = { t' with mem := t.mem } by rw [← hm]]
    exact ⟨h.nv.n, h.nv.inv, h.nv.r2, h.nv.r2lt, h.nv.one⟩
  exact ⟨⟨h.good.scr.congr k.2.2, (k.gpr (by decide)).trans h.good.rdi, hm ▸ h.good.hdr⟩, hN, hm ▸ h.xm,
    hm ▸ h.msk, hm ▸ h.wsP, hm ▸ h.wsQ, hm ▸ h.pws, hx h.pxv, hm ▸ h.pmask, hm ▸ h.qws, hx h.qxv,
    hm ▸ h.hfix, hm ▸ h.iscr, (h.keep.trans k).mono (by simp [mmRegs])⟩

end VG.Proof.Bignum.X86_64
