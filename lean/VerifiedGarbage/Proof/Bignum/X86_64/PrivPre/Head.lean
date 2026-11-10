module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_private_precompute` on x86-64: up to `vg_rsa_private_crt`'s code

After `entry`, `zeroPre` writes zeros to `pre` (`zeroPre_ok`), and `n` and
`k` are reloaded (`head_ok`); from there, with `pre` read as the input and
as `qInv` (zeros) and `p`, `q` as the exponents, the state is one that
`vg_rsa_private_crt`'s code starts from (`ppPre_of`, `CrtPre`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem eight_w (r : BitVec 64) {L : Nat} (h : r = BitVec.ofNat 64 L) :
    r + r + (r + r) + (r + r + (r + r)) = BitVec.ofNat 64 (L * 8) := by
  subst h; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega

/-- `zeroPre`: zeros to the `8 L` bytes at `op`, which `sOut` holds. -/
theorem zeroPre_ok {t : State} {B : Addr} {Z L : Nat} {op : Addr} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hL1 : 1 ≤ L) (hL : L * 8 < 2 ^ 31) (hsi : t.gpr .rsi = BitVec.ofNat 64 L)
    (hO : word t.mem B (8 * sOut) = op) (hout : ∀ j < L * 8, InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa PrivPre.zeroPre t fun u =>
      (∀ j < L * 8, u.mem (op + BitVec.ofNat 64 j) = 0) ∧
      (∀ x, (∀ j < L * 8, x ≠ op + BitVec.ofNat 64 j) → u.mem x = t.mem x) ∧ Keep [.rcx, .rsi, .rax] t u := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold PrivPre.zeroPre
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = op ∧
      t'.gpr .rcx = BitVec.ofNat 64 (L * 8) ∧ t'.gpr .rax = 0 ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hO, eight_w _ hsi]) rfl)
      fun s₁ ⟨⟨hsi₁, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := L * 8) (by omega) (FailInv s₁ op (L * 8)) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi₁, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun u hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩
  intro j _ hj u hI
  have hst : InRegions u.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  have hax' : (u.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
      t'.mem = u.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (L * 8 - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = L * 8))) (by
    xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ L * 8 - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show L * 8 - j - 1 < 2 ^ 64 by omega)]
    exact ⟨by rw [show L * 8 - j - 1 = L * 8 - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- After `entry`, `zeroPre` and the reloads of `n` and `k`, from `s`. -/
structure PPHead (s t : State) : Prop where
  scr : Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 2
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)
  hO : word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi
  hN : word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx
  hK : word t.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hIn : word t.mem (stackArg s 2) (8 * sIn) = s.gpr .rdi
  hP : word t.mem (stackArg s 2) (8 * sP) = s.gpr .r8
  hPl : word t.mem (stackArg s 2) (8 * sPlen) = BitVec.ofNat 64 (s.gpr .r9).toNat
  hQ : word t.mem (stackArg s 2) (8 * sQ) = stackArg s 0
  hQl : word t.mem (stackArg s 2) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hDp : word t.mem (stackArg s 2) (8 * sDp) = s.gpr .r8
  hDq : word t.mem (stackArg s 2) (8 * sDq) = stackArg s 0
  hQi : word t.mem (stackArg s 2) (8 * sQinv) = s.gpr .rdi
  zero : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0
  frame : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
    (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x
  inScr : ∀ x, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x →
    (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : Keep [.r11, .r10, .rax, .rdi, .rcx, .rsi, .rdx] s t

/-- `entry`, `zeroPre`, and `n` and `k` into `rdx` and `rcx`. -/
theorem head_ok {s : State} (c : PPCtx s) :
    WP isa (.block PrivPre.entry) s fun t₁ => WP isa PrivPre.zeroPre t₁ fun t₂ =>
      WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hL := c.hL
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  refine WP.mono (entry_ok c) fun t₀ ⟨hdi, hsv, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (zeroPre_ok hs₀ hdi (by omega) (L := (s.gpr .rsi).toNat) (by omega) (by omega)
    (by rw [k₀.gpr (by decide), ofNat_toNat_self]) hO (fun j hj => by rw [k₀.2.2]; exact c.hout j hj))
    fun t₁ ⟨hz₁, hf₁, k₁⟩ => ?_
  have hs₁ := hs₀.congr k₁.2.2
  -- The header is not in `pre`.
  have hh : ∀ i < 32, word t₁.mem (stackArg s 2) (8 * i) = word t₀.mem (stackArg s 2) (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hf₁ _ (fun j hj => scr_ne_out c.houts (d := 8 * i) (i := b) (by omega)
      (by omega) j hj)
  have hdi₁ : t₁.gpr .rdi = stackArg s 2 := (k₁.gpr (by decide)).trans hdi
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₁.mem) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₁.ld (d := 8 * sK) (by unfold sK sFn; omega), hh sN (by decide), hh sK (by decide), hN, hK]) rfl)
    fun t ⟨⟨hdx, hcx, hm⟩, k₂⟩ => ?_
  have hw : ∀ i < 32, word t.mem (stackArg s 2) (8 * i) = word t₀.mem (stackArg s 2) (8 * i) := fun i hi => by
    rw [hm]; exact hh i hi
  have kk := (k₀.trans k₁).trans k₂
  have hfr : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x := fun x hx hxz => by
    rw [hm, hf₁ x hx, ho₀ x (by omega)]
  exact ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans hdi₁, hdx, by rw [hcx, ofNat_toNat_self],
    fun i hi => by rw [hw i (by omega)]; exact hsv i hi,
    by rw [hw _ (by decide)]; exact hO, by rw [hw _ (by decide)]; exact hN,
    by rw [hw _ (by decide), hK, ofNat_toNat_self], by rw [hw _ (by decide)]; exact hI,
    by rw [hw _ (by decide)]; exact hP, by rw [hw _ (by decide), hPl, ofNat_toNat_self],
    by rw [hw _ (by decide)]; exact hQ, by rw [hw _ (by decide), hQl, ofNat_toNat_self],
    by rw [hw _ (by decide)]; exact hDp, by rw [hw _ (by decide)]; exact hDq, by rw [hw _ (by decide)]; exact hQi,
    fun j hj => by rw [hm]; exact hz₁ j hj, hfr, fun x hxz hx => hfr x hx hxz, kk.mono (by decide)⟩

/-- Bytes outside `pre` and the working space, as they were. -/
theorem Src.of_head {s t : State} {p : Addr} {bs : List Byte}
    (h : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) p bs)
    (hne : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < bs.length, s.gpr .rdi + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i)
    (hf : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t (stackArg s 2) ((stackArg s 3).toNat * 8) p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi,
    fun i hi => by rw [hf _ (fun j hj he => hne j hj i hi he.symm) (h.out i hi)]; exact h.val i hi, h.out⟩

/-- `pre`'s first bytes, zeros, as a byte string the code reads. -/
theorem src_zeros {s t : State} {n : Nat} (c : PPCtx s) (hn : n ≤ (s.gpr .rsi).toNat * 8)
    (hz : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0) (hwr : t.wr = s.wr) :
    Src t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdi) (List.replicate n 0) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => c.houts i (by simp at hi; omega)⟩
  · simp only [List.length_replicate] at hi
    obtain ⟨r, hr, hc⟩ := c.hout i (by omega)
    exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact hr), hc⟩
  · simp only [List.length_replicate] at hi
    rw [hz i (by omega), List.getElem_replicate]

/-- `vg_rsa_private_crt`'s precondition, after the head and the modulus'
check, with `pre` (zeros) as the input and as `qInv`. -/
theorem ppPre_of {s t₁ t : State} (c : PPCtx s) (h : PPHead s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) :
    CrtPre t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx)
      (s.gpr .rdi) (s.gpr .r8) (stackArg s 0) (s.gpr .r8) (stackArg s 0) (s.gpr .rdi)
      (s.gpr .r9).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (List.replicate (s.gpr .rcx).toNat 0)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (List.replicate (s.gpr .r9).toNat 0) := by
  have kk := h.keep.trans k
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  have hdi : t.gpr .rdi = stackArg s 2 := (k.gpr (by decide)).trans h.rdi
  have hf : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x := fun x hx hxz => by
    rw [hm]; exact h.frame x hx hxz
  have hz : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0 := fun j hj => by
    rw [hm]; exact h.zero j hj
  have hz8 : offQ (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat + slot (wsWords (stackArg s 1).toNat) 8 +
      wsTab (wsWords (stackArg s 1).toNat) ≤ (stackArg s 3).toNat * 8 :=
    crt_room hk1 hpl2 hql2 hZ
  have hnb := Src.of_head (t := t) c.hnb (by rw [bytesAt_length]; exact c.hon) hf kk.2.1 kk.2.2
  have hpb := Src.of_head (t := t) c.hpb (by rw [bytesAt_length]; exact c.hop) hf kk.2.1 kk.2.2
  have hqb := Src.of_head (t := t) c.hqb (by rw [bytesAt_length]; exact c.hoq) hf kk.2.1 kk.2.2
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz8, zk := (by omega), k1 := hk1, k2 := hk2,
      hO := (by rw [hm]; exact h.hO), hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK),
      hIn := (by rw [hm]; exact h.hIn), hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl),
      hQ := (by rw [hm]; exact h.hQ), hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp),
      hDq := (by rw [hm]; exact h.hDq), hQi := (by rw [hm]; exact h.hQi), n := hnb,
      x := src_zeros c (by omega) hz kk.2.2, p := hpb, q := hqb, dp := hpb, dq := hqb,
      qi := src_zeros c (by omega) hz kk.2.2, nl := bytesAt_length _ _ _, xl := List.length_replicate,
      pbl := bytesAt_length _ _ _, qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _,
      dql := bytesAt_length _ _ _, qil := List.length_replicate, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.2.2]; exact c.hout j (by omega)),
      outSep := (fun j hj => c.houts j (by omega)) }

end VG.Proof.Bignum.X86_64.PrivPre
