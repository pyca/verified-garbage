module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pub
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry

/-!
# RSAES-OAEP encryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks of the lengths
(`chkK`, `chkMsg`: `k < 2 hLen + 2` and `msg_len > k - 2 hLen - 2`, from the
top bits of differences), then either zeros and 0 (`fail_ok`) or `EM`
(`em_ok`, `mask_ok`) and RSAEP of it (`call_ok`): if `pre` holds the
modulus' values, RSAES-OAEP-ENCRYPT (RFC 8017 §7.1.1). `code_correct`: the
function against its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_sub wp_lsr wp_or wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The test of `chkMsg`: the top bit of `y`, or of `x - y`, for `x < 2⁶³`. -/
theorem msgBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 64) :
    ((BitVec.ofNat 64 y >>> 63 ||| (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63) != 0) = decide (x < y) := by
  by_cases h : y < 2 ^ 63
  · rw [ltBit hx h]
    have e : BitVec.ofNat 64 y >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [e]; split <;> rename_i hxy <;> simp only [hxy, decide_true, decide_false] <;> decide
  · have e : BitVec.ofNat 64 y >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt hy]; simp; omega
    rw [e, decide_eq_true (by omega), bne_iff_ne]
    intro h0
    have := congrArg (fun v : BitVec 64 => v.getLsbD 0) h0
    simp at this

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s →
    Spec.Rsa.written t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (labB s) (msgB s) (seedB Hs.len s)))

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {s : State} (P : PreO H.D s)
include hH hG hHh hHl hGh hGl hGv P

omit hH hG hHh hGh hGl hGv in
theorem fail_done {t : State} (h : Base S vO s t) (hl : kk s < 2 * H.D + 2 + mLen s) :
    WP isa encFail t (Done Hs Gs s) :=
  WP.mono (fail_ok P h) fun t' ⟨sv, h3, hb⟩ => ⟨sv, fun _ => by
    rw [Proof.RsaOaep.encrypt_none (by rw [bytesAt_length, bytesAt_length, hHl]; exact hl), h3]
    exact ⟨rfl, hb⟩⟩

theorem main_done {t : State} (E : Entered s t) (hk : 2 * H.D + 2 + mLen s ≤ kk s) :
    WP isa (encMain H G) t (Done Hs Gs s) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  refine em_ok P hH hHh rfl E hk fun t₁ b₁ he => ?_
  refine mask_ok P hG hGh hGl hGv rfl hD0 hD64 (bytesAt_length _ _ _)
    (by rw [hHh, hH.hashLen]) (bytesAt_length _ _ _) hk b₁ he fun t₂ b₂ hem => ?_
  refine WP.seq (WP.mono (pubArgs_ok P b₂ hem) fun t₃ a₃ => WP.mono (call_ok P a₃) fun t₄ ⟨sv, res⟩ =>
    ⟨sv, fun hc => ?_⟩)
  have hs : (seedB Hs.len s).length = Hs.len := bytesAt_length _ _ _
  rw [Proof.RsaOaep.encrypt_some hs (by rw [bytesAt_length, bytesAt_length, hHl]; exact hk), bytesAt_length,
    bytesAt_length, hHl]
  exact res hc

theorem checks_done {t : State} (E : Entered s t) : WP isa (checks H G) t (Done Hs Gs s) := by
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  have b := E.base
  refine WP.seq (wp_li (by omega) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have b₃ := b.only P.fits k₃
  have r3 : (t₃.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
    rw [e₃, e₂, e₁, o₁.get .r15, b.r15, ← ofNat_toNat (s.gpr .r6)]
    exact ne_zero_ltBit (by omega) (by omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₃
    (by rw [r3] at hc; simp at hc; omega)) (fun hc => ?_)
  have hk : 2 * H.D + 2 ≤ kk s := by rw [r3] at hc; simp at hc; omega
  refine WP.seq (wp_li (by omega) fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_lsr fun t₇ o₇ e₇ => wp_lsr fun t₈ o₈ e₈ => wp_or fun t₉ o₉ e₉ => wp_nil ?_)
  have k₉ : Only [.r3, .r4] t₃ t₉ := (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉))))).mono
  have b₉ := b₃.only P.fits k₉
  have r3' : (t₉.gpr .r3 != 0) = decide (kk s - (2 * H.D + 2) < mLen s) := by
    rw [e₉, e₈, o₇.get .r10, o₆.get .r10, o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, o₈.get .r4, e₇, e₆,
      o₅.get .r10, o₄.get .r10, k₃.get .r10, E.r10, e₅, o₄.get .r15, k₃.get .r15, b.r15, e₄,
      ← ofNat_toNat (s.gpr .r6), ← ofNat_toNat (stackArg s 1), Offset.ofNat_sub_ofNat hk]
    exact msgBit (by omega) (stackArg s 1).isLt
  have E₉ : Entered s t₉ := ⟨b₉, by rw [k₉.get .r9, k₃.get .r9]; exact E.r9,
    by rw [k₉.get .r10, k₃.get .r10]; exact E.r10, by rw [k₉.get .r11, k₃.get .r11]; exact E.r11⟩
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P b₉
    (by rw [r3'] at hc; simp at hc; omega)) (fun hc => main_done hH hG hHh hHl hGh hGl hGv P E₉
    (by rw [r3'] at hc; simp at hc; omega))

theorem code_ok : WP isa (encrypt H G) s (Post Hs Gs s) := by
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono (entry_ok P) fun t E => WP.seq (WP.mono (checks_done hH hG hHh hHl hGh hGl hGv P E)
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hc => ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res hc

end

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include hH hG hHh hHl hGh hGl hGv

/-- The correctness of `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, against
its shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304).pre s) :
    ∃ t s', Exec isa (encrypt H G) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaOaep.encryptPrecomputedContract Hs Gs abi 304).post s s' := by
  have P : PreO H.D s := hHl ▸ preO_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok hH hG hHh hHl hGh hGl hGv P
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    stackArgs_seven, List.append_eq]
  exact hr

end

end VG.Proof.RsaOaep.PPC64LE
