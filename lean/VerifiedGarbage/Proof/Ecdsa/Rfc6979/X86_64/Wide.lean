module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: scalars longer than the hash

For scalars longer than the hash function's output (`wide`): the `Q` bytes
at an offset above the streaming functions' addresses, shifted right in place
through the words at `scratch + 2560` (`conv_ok`, by `loadBytes_ok`,
`shrWords_ok` and `storeBytes_ok`), which only P-521's scalars need, whose
`n` has fewer bits than they have; the digest for `core` (`coreDigest_ok`),
the digest after `zPre` zero bytes and before `zPost`, shifted right if
`sh ≠ 0`, which is the digest's number shifted left by `sh` bits; and the
candidate (`candW_ok`): `blocks` successive `V`s (`candSteps_ok`), the first
`Q` bytes of them kept above the addresses, shifted right by `sh` bits if
`sh ≠ 0`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Mont (wordsVal Outside off)
open VG.Proof.Mont.X86_64 (Scr KeepRegs)
open VG.Proof.Weierstrass.X86_64 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) : Scr t L.scr 8192 :=
  ⟨hdi, by rw [hc.wr]; simp, hL.nc⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (hdi : s'.gpr .rdi = s.gpr .rdi)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨hdi.trans h.rdi, hwr ▸ h.wr, h.nowrap⟩

/-- `rcx ← -1`. -/
theorem ones_ok (u : State) : WP isa (.block [.movImm64 .rcx (BitVec.allOnes 64)]) u fun u' =>
    u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr .rcx = BitVec.allOnes 64 ∧
      ∀ r, r ≠ .rcx → u'.gpr r = u.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `conv o s`: the `Q` bytes at `rsp + o`, above the streaming functions'
addresses, shifted right by `s` bits in place, through the words at
`scratch + 2560`, for P-521's scalars. -/
theorem conv_ok (hL : L.Ok) (hbig : P.R.big = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .rdi = L.scr) {o s : Nat} (ho₁ : 240 ≤ o) (ho₂ : o + 72 ≤ 384) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  have hw9 : P.w = 9 := (P.R.sizesW hbig).1
  have hQ66 : P.Q = 66 := (P.R.sizesW hbig).2.1
  have he := L.he
  have hnb := hL.nb
  refine WP.of_sf ?_
  rw [Cfg.conv, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := o) (by omega_arith)) fun u₁ h₁ => ?_
  have hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .rsi = L.B + BitVec.ofNat 64 (24 + o) := h₁.val
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .rsi) (by decide) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (fun d hd => by rw [hsi₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith))
    (by rw [hsi₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr) (n := P.w) (o := 2560) (sh := s) (by omega_arith)
    hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine WP.mono (ones_ok u₃) fun u₄ ⟨hm₄, hrd₄, hwr₄, hcx₄, hg₄⟩ => ?_
  have hsp₄ : u₄.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hg₄ _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.keep _ (by decide), hc.rsp]
  have hwr₄' : u₄.wr = t.wr := by rw [hwr₄, k₃.wr, k₂.wr, h₁.ctx.wr, hc.wr]
  have hdst : u₄.gpr .rsp + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by rw [hsp₄, Offset.add_add]
  refine WP.mono (storeBytes_ok (scr_keep (scr_keep hS₁ (k₂.gpr _ (by decide)) k₂.wr)
      ((hg₄ _ (by decide)).trans (k₃.gpr _ (by decide))) (hwr₄.trans k₃.wr))
    (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .rsp) (by decide) (by decide) true
    (by rw [hcx₄]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [hdst, toNat_add_of (by omega_arith)]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄']; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ hsy => ?_
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem u₅.mem := by
    have f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    have f₅ := frame_of_outside O₅ (by omega_arith)
    rw [add_ofNat_zero, hm₄] at f₅
    rw [h₁.mem, show 8 * P.w = 72 by omega_arith] at f₂
    exact (f₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
    rw [k₅.gpr _ (by simp [h₁', h₃]), hg₄ _ h₂, k₃.gpr _ (by simp [h₁', h₃]), k₂.gpr _ (by simp [h₁']),
      h₁.keep _ h₄]
  refine ⟨hc.keep hL (by rw [k₅.rd, hrd₄, k₃.rd, k₂.rd, h₁.ctx.rd, hc.rd]) (by rw [k₅.wr, hwr₄']) (hg _ (by decide)
      (by decide) (by decide) (by decide)) (fun r hr hr' => hg r (ne_cs hr (by decide)) (ne_cs hr (by decide))
      (ne_cs hr (by decide)) (ne_cs hr (by decide))) hf (hsy := hsy) fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₅
    simp only [ite_true] at hb₅
    rw [hb₅, hm₄, hv₃, hv₂, hsi₁, ecdsa_bytesAt, h₁.mem]

/-! ## Copies into the frame above the streaming functions' addresses -/

/-- `n ≥ 8` bytes copied to `rsp + d`, above the streaming functions'
addresses, by `copyBytes`, with `Ctx` kept. -/
theorem copyFB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) {so d n : Nat} (hn : 8 ≤ n) (hd₁ : 240 ≤ d) (hd₂ : 24 + d + n ≤ 408)
    (hso : so + n < 2 ^ 64)
    (hr : ∀ j, j + 8 ≤ n → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, n⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), n⟩) :
    WP isa (.block (Cfg.copyBytes n src so .rsp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) n =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) n := by
  have he := L.he
  rw [← fr_add] at hsep ⊢
  refine WP.mono_sf (copyBytes_ok (by decide) hsr hsep hn hso (by omega_arith) hs hc.rsp hr
    fun j hj => by rw [fr_add]; exact hc.inFrW (by omega_arith) (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  refine ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [fr_add]
        exact safe_high L (by omega_arith) (by omega_arith)) hsy, hg, hf, hb⟩

/-- `k` zero words at `rsp + d`, above the streaming functions' addresses,
`rax` zero, with `Ctx` kept. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (ha : u.gpr .rax = 0) {d k : Nat} (hd₁ : 240 ≤ d)
    (hd₂ : 24 + d + 8 * k ≤ 408) :
    WP isa (.block (Cfg.zeroN k .rsp d)) u fun u' => Ctx L g m₀ u' ∧ u'.gpr = u.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + d), 8 * k⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) (8 * k) = List.replicate (8 * k) 0 := by
  have he := L.he
  have hnb := hL.nb
  rw [← fr_add]
  refine WP.mono_sf (zeroN_words (D := L.B + BitVec.ofNat 64 24) (d := d) (K := k) (by decide) (by omega_arith) k
    (Nat.le_refl _) u hc.rsp ha fun j hj => by rw [fr_add]; exact hc.inFrW (by omega_arith) (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  refine ⟨hc.keep hL hrd hwr (by rw [hg]) (fun r _ _ => by rw [hg]) hf
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [fr_add]
        exact safe_high L (by omega_arith) (by omega_arith)) hsy, hg, hf, hb⟩

/-- `sh` is below 8, and nonzero only for the curve whose `n` has fewer bits than its scalars. -/
theorem sh_lt (P : RfcHash) : P.R.sh < 8 := by have := P.R.nBits_len; omega_arith

theorem big_of_sh (h : P.R.sh ≠ 0) : P.R.big = true := by
  cases hb : P.R.big
  · have h₁ := P.R.nBits_len; have h₂ := (P.R.sizesA hb).2.2.1; omega_arith
  · rfl

theorem shift_mul (e a b : Nat) : (e * 2 ^ (a + b)) >>> b = e * 2 ^ a := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The hash is at least 20 bytes, shorter than the scalars, and a whole
number of words longer than none of them. -/
theorem wide_sizes (hW : P.wide = true) : P.D < P.Q ∧ P.Q ≤ 66 ∧ 20 ≤ P.D ∧ P.D ≤ 64 ∧ P.D % 4 = 0 := by
  have hz := P.sizes
  have : P.D < P.Q := by simpa [RfcHash.wide] using hW
  exact ⟨this, by omega, by omega, by omega, by omega⟩

/-! ## The digest for `core` -/

/-- The digest for `core`: the digest's number shifted left by `sh` bits, in
`Q` bytes above the streaming functions' addresses. -/
theorem coreDigest_ok (hL : L.Ok) (hW : P.wide = true) (hdn : P.D ≤ dn) {t : State}
    (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg) (hdi : t.gpr .rdi = L.scr) :
    WP isa (.block (cfgOf P).coreDigest) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 264, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 264) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.D) * 2 ^ P.R.sh) := by
  obtain ⟨hDQ, hQ66, hD20, hD64, -⟩ := wide_sizes hW
  have hsh := sh_lt P
  have he := L.he
  have hnb := hL.nb
  have hzp : (cfgOf P).zPost = (P.R.sh + 7) / 8 := rfl
  have hzP : (cfgOf P).zPre = P.Q - P.D - (P.R.sh + 7) / 8 := rfl
  have hzp1 : (P.R.sh + 7) / 8 ≤ 1 := by omega_arith
  have hcD : (cfgOf P).D = P.D := rfl
  rw [Cfg.coreDigest, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zeroRax_ok hL hc) fun u₁ h₁ => ?_
  refine WP.mono (zeroF_ok hL h₁.ctx h₁.val (d := fX) (k := (P.Q + 7) / 8) (by decide) (by simp only [fX]; omega_arith))
    fun u₂ ⟨hc₂, hg₂, hf₂, hz₂⟩ => ?_
  have hdg₂ : Spec.Sha256.bytesAt u₂.mem L.dg P.D = Spec.Sha256.bytesAt t.mem L.dg P.D := by
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by simp only [fX]; omega_arith)).symm.sub_left (Region.sub_prefix hdn)) (by omega_arith), h₁.mem]
  refine WP.mono (copyFB_ok hL hc₂ (src := .rsi) (S := L.dg)
    (by rw [hg₂, h₁.keep _ (by decide)]; exact hsi) (by decide) (so := 0)
    (d := fX + (cfgOf P).zPre) (n := (cfgOf P).D) (by show 8 ≤ P.D; omega_arith) (by simp only [fX]; omega_arith)
    (by simp only [fX, hzP]; show _ + P.D ≤ _; omega_arith) (by show _ + P.D < _; omega_arith)
    (fun j hj => by rw [Nat.zero_add]; exact hc₂.inDg (by show j + 8 ≤ dn; omega_arith) (by show j ≤ 64; omega_arith))
    (by rw [add_ofNat_zero]
        exact (hL.stk_DG (by simp only [fX, hzP]; show _ + P.D ≤ _; omega_arith)).symm.sub_left
          (Region.sub_prefix hdn)))
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  simp only [fX, hzP, cfgOf_D] at hf₃ hb₃
  -- The digest after `zPre` zero bytes and before `zPost`.
  have hY : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 264) P.Q =
      List.replicate (P.Q - P.D - (P.R.sh + 7) / 8) 0 ++ (Spec.Sha256.bytesAt t.mem L.dg P.D ++
        List.replicate ((P.R.sh + 7) / 8) 0) := by
    have hz : ∀ a n, a + n ≤ 8 * ((P.Q + 7) / 8) → (a + n ≤ P.Q - P.D - (P.R.sh + 7) / 8 ∨ P.Q - (P.R.sh + 7) / 8 ≤ a) →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 (264 + a)) n = List.replicate n 0 := fun a n h₁' h₂' => by
      rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
      have := hz₂
      rw [show 24 + fX = 264 by rfl, show 8 * ((P.Q + 7) / 8) = a + (n + (8 * ((P.Q + 7) / 8) - a - n)) by omega_arith,
        Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
        ← List.replicate_append_replicate, ← List.replicate_append_replicate] at this
      exact (List.append_inj (List.append_inj this (by simp [Spec.Sha256.bytesAt])).2
        (by simp [Spec.Sha256.bytesAt])).1
    have e₁ := hz 0 (P.Q - P.D - (P.R.sh + 7) / 8) (by omega_arith) (.inl (by omega_arith))
    have e₂ := hz (P.Q - (P.R.sh + 7) / 8) ((P.R.sh + 7) / 8) (by omega_arith) (.inr (Nat.le_refl _))
    rw [Nat.add_zero] at e₁
    have e₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 (264 + (P.Q - P.D - (P.R.sh + 7) / 8))) P.D =
        Spec.Sha256.bytesAt t.mem L.dg P.D := by
      rw [show 264 + (P.Q - P.D - (P.R.sh + 7) / 8) = 24 + (240 + (P.Q - P.D - (P.R.sh + 7) / 8)) by omega_arith,
        hb₃, add_ofNat_zero, hdg₂]
    have e₀ := Proof.Hmac.Common.bytesAt_add u₃.mem (L.B + BitVec.ofNat 64 264) (P.Q - P.D - (P.R.sh + 7) / 8)
      (P.D + (P.R.sh + 7) / 8)
    rw [show P.Q - P.D - (P.R.sh + 7) / 8 + (P.D + (P.R.sh + 7) / 8) = P.Q by omega_arith] at e₀
    rw [e₀, Proof.Hmac.Common.bytesAt_add _ _ P.D, Offset.add_add, Offset.add_add, e₁, e₃,
      show 264 + (P.Q - P.D - (P.R.sh + 7) / 8) + P.D = 264 + (P.Q - (P.R.sh + 7) / 8) by omega_arith, e₂]
  have hlt := ofBytes_lt (Spec.Sha256.bytesAt t.mem L.dg P.D)
  rw [Proof.Hmac.Common.bytesAt_length] at hlt
  by_cases h0 : P.R.sh = 0
  · have hc' : (cfgOf P).sh = 0 := h0
    simp only [hc', ite_true]
    refine WP.block_nil ⟨hc₃, ?_, ?_⟩
    · refine ((h₁.mem ▸ hf₂).sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
        (hf₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [hY, h0, Nat.pow_zero, Nat.mul_one, show (0 + 7) / 8 = 0 from rfl, List.replicate_zero, List.append_nil,
        Nat.sub_zero]
      have e := toBytes_pad (P.Q - P.D) P.D _ hlt
      have e' := toBytes_ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.D)
      rw [Proof.Hmac.Common.bytesAt_length] at e'
      rw [show P.Q - P.D + P.D = P.Q by omega_arith, e'] at e
      exact e.symm
  · have hc' : (cfgOf P).sh = P.R.sh := rfl
    have hz1 : (P.R.sh + 7) / 8 = 1 := by omega_arith
    simp only [hc', h0, ite_false]
    refine WP.mono (conv_ok hL (big_of_sh h0) hc₃ (by rw [hg₃ _ (by decide), hg₂, h₁.keep _ (by decide)]; exact hdi)
      (o := fX) (s := 8 * (cfgOf P).zPost - P.R.sh) (by decide) (by decide) (by rw [hzp]; omega_arith)
      (by rw [hzp]; omega_arith)) fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ⟨hc₄, ?_, ?_⟩
    · refine (((h₁.mem ▸ hf₂).sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
        (hf₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans
        (hf₄.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., sub_refl _⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
    · simp only [fX] at hb₄
      have key : ∀ x, (x * 2 ^ (8 * 1)) >>> (8 * 1 - P.R.sh) = x * 2 ^ P.R.sh := fun x => by
        have := shift_mul x P.R.sh (8 * 1 - P.R.sh)
        rwa [show P.R.sh + (8 * 1 - P.R.sh) = 8 * 1 by omega_arith] at this
      rw [hb₄, hY, hzp, hz1, ofBytes_zeros, ofBytes_append_zeros, key]

/-! ## The candidate -/

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and the candidate above the streaming functions' addresses. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 336, 72⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- The `V`s a candidate takes, and the bytes each of them gives it. -/
theorem blocks_sizes (hW : P.wide = true) :
    2 ≤ (cfgOf P).blocks ∧ P.D * ((cfgOf P).blocks - 1) < P.Q ∧ P.Q ≤ P.D * (cfgOf P).blocks ∧
      P.D * ((cfgOf P).blocks - 1) ≤ 64 := by
  obtain ⟨hDQ, hQ66, -, -, hD4⟩ := wide_sizes hW
  have hl := P.R.nBits_len
  have hQ : P.Q = P.R.E.C.len := rfl
  rw [cfgOf_blocks]
  rcases P.hDB.2.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    simp only [h] at hDQ ⊢ <;> omega

/-- Unless the hash is shorter than the scalars, one `V` makes a candidate. -/
theorem blocks_one (hW : P.wide = false) : (cfgOf P).blocks = 1 := by
  have hz := P.sizes
  have hQD : P.Q ≤ P.D := (P.sizesA hW).2.2
  have hl := P.R.nBits_len
  have hQ : P.Q = P.R.E.C.len := rfl
  rw [cfgOf_blocks]
  rcases P.hDB.2.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    simp only [h] at hQD ⊢ <;> omega

/-- `V = HMAC_K(V)`, and its first `chunk i` bytes to the candidate's place
after the `i` `V`s before it. -/
theorem candStep_ok (hL : L.Ok) (hT : L.T = P.T) (hW : P.wide = true) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hi : i < (cfgOf P).blocks) :
    WP isa ((cfgOf P).candStep i) u fun u' => Ctx L g m₀ u' ∧
      Frame (KVW L ++ [⟨L.B + BitVec.ofNat 64 (336 + P.D * i), 72 - P.D * i⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = kOf P L u.mem ∧ vOf P L u'.mem = P.mac (kOf P L u.mem) (vOf P L u.mem) ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (336 + P.D * i)) ((cfgOf P).chunk i) =
        (P.mac (kOf P L u.mem) (vOf P L u.mem)).take ((cfgOf P).chunk i) := by
  obtain ⟨hb2, hb₁, hb₂, hb₃⟩ := blocks_sizes hW
  obtain ⟨hDQ, hQ66, hD20, hD64, -⟩ := wide_sizes hW
  have hDi : P.D * i ≤ P.D * ((cfgOf P).blocks - 1) := Nat.mul_le_mul_left _ (by omega_arith)
  have hbb : P.D * (cfgOf P).blocks = P.D * ((cfgOf P).blocks - 1) + P.D := by
    rw [← Nat.mul_succ]; congr 1; omega_arith
  have hch : 8 ≤ (cfgOf P).chunk i ∧ (cfgOf P).chunk i ≤ P.D ∧ P.D * i + (cfgOf P).chunk i ≤ 72 := by
    simp only [Cfg.chunk, cfgOf_D, cfgOf_len]
    split
    · have : P.D * (i + 1) ≤ P.D * ((cfgOf P).blocks - 1) := Nat.mul_le_mul_left _ (by omega_arith)
      rw [Nat.mul_succ] at this; omega_arith
    · have : i = (cfgOf P).blocks - 1 := by omega_arith
      subst this
      simp only [Nat.max_def]
      split <;> omega_arith
  have he := L.he
  have hnb := hL.nb
  have hfV : fV = 64 := rfl
  have hfK : fKb = 312 := rfl
  have hcD : (cfgOf P).D = P.D := rfl
  refine WP.seq (WP.mono (hmacV_ok hL hT hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 (24 + fV), (cfgOf P).chunk i⟩
      ⟨L.B + BitVec.ofNat 64 (24 + (fKb + P.D * i)), (cfgOf P).chunk i⟩ :=
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (copyFB_ok hL hc₁ (src := .rsp) (S := L.B + BitVec.ofNat 64 24) hc₁.rsp (by decide) (so := fV)
    (d := fKb + P.D * i) (n := (cfgOf P).chunk i) hch.1 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [fr_add]; exact hc₁.inFr (by omega_arith) (by omega_arith)) (by rw [fr_add]; exact hsep))
    fun u₂ ⟨hc₂, _, hf₂, hb₂'⟩ => ?_
  simp only [fV, fKb, show 24 + (312 + P.D * i) = 336 + P.D * i by omega_arith] at hf₂ hb₂'
  have kv : kOf P L u₂.mem = kOf P L u₁.mem ∧ vOf P L u₂.mem = vOf P L u₁.mem :=
    ⟨bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by omega_arith),
     bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by omega_arith)⟩
  refine ⟨hc₂, ?_, kv.1.trans hk₁, kv.2.trans hv₁, ?_⟩
  · refine (hf₁.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega_arith)
  · rw [hb₂', fr_add, show (24 + 64 : Nat) = 88 from rfl, ← hv₁, bytesAt_take _ _ hch.2.1]

/-- The steps from `i` of the `k` left, after the `i` `V`s before them. -/
theorem candSteps_ok (hL : L.Ok) (hT : L.T = P.T) (hW : P.wide = true) :
    ∀ k i, i + k = (cfgOf P).blocks → 0 < k → ∀ u : State, Ctx L g m₀ u →
      WP isa ((cfgOf P).candSteps i k) u fun u' => Ctx L g m₀ u' ∧
        Frame (KVW L ++ [⟨L.B + BitVec.ofNat 64 (336 + P.D * i), 72 - P.D * i⟩]) u.mem u'.mem ∧
        kOf P L u'.mem = kOf P L u.mem ∧
        vOf P L u'.mem = (Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L u.mem) k (vOf P L u.mem)).2 ∧
        Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (336 + P.D * i)) (P.Q - P.D * i) =
          ((Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L u.mem) k (vOf P L u.mem)).1).take (P.Q - P.D * i)
  | 0, _, _, h, _, _ => absurd h (Nat.lt_irrefl _)
  | 1, i, hik, _, u, hc => by
    obtain ⟨hb2, hb₁, hb₂, hb₃⟩ := blocks_sizes hW
    have hi : i = (cfgOf P).blocks - 1 := by omega_arith
    have hch : (cfgOf P).chunk i = max 8 (P.Q - P.D * i) := by
      have hn : ¬ i + 1 < (cfgOf P).blocks := by omega_arith
      unfold Cfg.chunk
      rw [ite_eq_right_of_eq_false _ _ (eq_false hn), hi]
      rfl
    show WP isa ((cfgOf P).candStep i) u _
    refine WP.mono (candStep_ok hL hT hW hc (by omega_arith)) fun u' ⟨hc', hf', hk', hv', hb'⟩ =>
      ⟨hc', hf', hk', by rw [hv']; rfl, ?_⟩
    rw [hch] at hb'
    rw [bytesAt_take _ _ (Nat.le_max_right 8 _), hb', List.take_take, Nat.min_eq_left (Nat.le_max_right 8 _),
      show (Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L u.mem) 1 (vOf P L u.mem)).1 =
        P.mac (kOf P L u.mem) (vOf P L u.mem) ++ [] from rfl, List.append_nil]
  | k + 2, i, hik, _, u, hc => by
    obtain ⟨hb2, hb₁, hb₂, hb₃⟩ := blocks_sizes hW
    obtain ⟨hDQ, hQ66, hD20, hD64, -⟩ := wide_sizes hW
    have hch : (cfgOf P).chunk i = P.D := by
      simp only [Cfg.chunk, cfgOf_D, show i + 1 < (cfgOf P).blocks by omega_arith, ite_true]
    have hDi : P.D * (i + 1) ≤ P.D * ((cfgOf P).blocks - 1) := Nat.mul_le_mul_left _ (by omega_arith)
    rw [Nat.mul_succ] at hDi
    show WP isa (.seq ((cfgOf P).candStep i) ((cfgOf P).candSteps (i + 1) (k + 1))) u _
    refine WP.seq (WP.mono (candStep_ok hL hT hW hc (by omega_arith)) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁'⟩ => ?_)
    rw [hch] at hb₁'
    refine WP.mono (candSteps_ok hL hT hW (k + 1) (i + 1) (by omega_arith) (by omega_arith) u₁ hc₁)
      fun u₂ ⟨hc₂, hf₂, hk₂, hv₂, hb₂'⟩ => ⟨hc₂, ?_, ?_, ?_, ?_⟩
    · refine hf₁.trans (hf₂.sub fun r hr => ?_)
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, sub_refl _⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Offset.sub _ (by rw [Nat.mul_succ]; omega_arith)
          (by rw [Nat.mul_succ]; omega_arith)⟩
    · rw [hk₂, hk₁]
    · rw [hv₂, hk₁, hv₁]; rfl
    · -- `V`, then the steps after it.
      have hV : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (336 + P.D * i)) P.D =
          P.mac (kOf P L u.mem) (vOf P L u.mem) := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact hL.stk_SCR (by have := L.he; omega_arith)
              · exact Offset.disjoint_base _ (by omega_arith) (by have := hL.nb; have := L.he; omega_arith)
            · simp only [List.mem_singleton] at hr; subst hr
              exact Offset.disjoint _ (by rw [Nat.mul_succ]; omega_arith) (by have := hL.nb; have := L.he; omega_arith)
                (by have := hL.nb; have := L.he; rw [Nat.mul_succ]; omega_arith)) (by omega_arith), hb₁',
          List.take_of_length_le (by rw [mac_length])]
      rw [show P.Q - P.D * i = P.D + (P.Q - P.D * (i + 1)) by rw [Nat.mul_succ]; omega_arith,
        Proof.Hmac.Common.bytesAt_add, Offset.add_add, show 336 + P.D * i + P.D = 336 + P.D * (i + 1) by
          rw [Nat.mul_succ]; omega_arith, hb₂', hV, hk₁, hv₁]
      show _ = (P.mac (kOf P L u.mem) (vOf P L u.mem) ++
        (Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L u.mem) (k + 1) (P.mac (kOf P L u.mem) (vOf P L u.mem))).1).take _
      rw [List.take_append, mac_length,
        List.take_of_length_le (l := P.mac (kOf P L u.mem) (vOf P L u.mem)) (by rw [mac_length]; omega_arith),
        show P.D + (P.Q - P.D * (i + 1)) - P.D = P.Q - P.D * (i + 1) by omega_arith]

/-- `T` of `n` `V`s. -/
theorem genT_length (P : RfcHash) : ∀ n (K V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.T.S.H K n V).1.length = P.D * n
  | 0, _, _ => rfl
  | n + 1, K, V => by
    show (Spec.Hmac.hmac P.T.S.H K V ++ (Spec.Ecdsa.Rfc6979.genT P.T.S.H K n (Spec.Hmac.hmac P.T.S.H K V)).1).length = _
    rw [List.length_append, genT_length P n, show (Spec.Hmac.hmac P.T.S.H K V).length = P.D from mac_length P K V,
      Nat.mul_succ]; omega

/-- The candidate, if the hash is shorter than the scalars: `blocks`
successive `V = HMAC_K(V)`, the first `Q` bytes of them shifted right by
`sh` bits, in the candidate's place. -/
theorem candW_ok (hL : L.Ok) (hT : L.T = P.T) (hW : P.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L t.mem) (cfgOf P).blocks (vOf P L t.mem)).2 ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 336) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes
          ((Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L t.mem) (cfgOf P).blocks (vOf P L t.mem)).1.take P.Q) >>>
            P.R.sh) := by
  obtain ⟨hb2, hb₁, hb₂, hb₃⟩ := blocks_sizes hW
  obtain ⟨hDQ, hQ66, hD20, hD64, -⟩ := wide_sizes hW
  have hcw : (cfgOf P).wide = true := hW
  have hsteps := candSteps_ok hL hT hW (cfgOf P).blocks 0 (Nat.zero_add _) (by omega_arith) t hc
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hsteps
  have hcww : ∀ r ∈ KVW L ++ [(⟨L.B + BitVec.ofNat 64 336, 72⟩ : Region)], ∃ r' ∈ CWW L, Region.Sub r r' :=
    fun r hr => ⟨r, by
      simp only [KVW, CWW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr, sub_refl _⟩
  -- The candidate's `T` has at least `Q` bytes.
  have hTl : ∀ K V : List Byte, P.Q ≤ (Spec.Ecdsa.Rfc6979.genT P.T.S.H K (cfgOf P).blocks V).1.length := by
    intro K V; rw [genT_length]; exact hb₂
  by_cases h0 : P.R.sh = 0
  · have hc' : (cfgOf P).sh = 0 := h0
    simp only [Cfg.cand, hcw, hc', ite_true]
    refine WP.mono hsteps fun u ⟨hcu, hf, hk, hv, hb⟩ => ⟨hcu, hf.sub hcww, hk, hv, ?_⟩
    rw [hb, h0, Nat.shiftRight_zero]
    have e := toBytes_ofBytes ((Spec.Ecdsa.Rfc6979.genT P.T.S.H (kOf P L t.mem) (cfgOf P).blocks
      (vOf P L t.mem)).1.take P.Q)
    rw [List.length_take, Nat.min_eq_left (hTl _ _)] at e
    exact e.symm
  · have hc' : (cfgOf P).sh = P.R.sh := rfl
    simp only [Cfg.cand, hcw, hc', h0, ite_true, ite_false]
    refine WP.seq (WP.mono hsteps fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁⟩ => ?_)
    refine WP.seq (WP.mono (scrPtr_ok hL hc₁) fun u₂ ⟨hc₂, hm₂, hdi₂⟩ => ?_)
    have hsh := sh_lt P
    refine WP.mono (conv_ok hL (big_of_sh h0) hc₂ hdi₂ (o := fKb) (s := P.R.sh) (by decide) (by decide)
      (by omega_arith) (by omega_arith)) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ⟨hc₃, ?_, ?_, ?_, ?_⟩
    · have hf₃' : Frame _ u₁.mem u₃.mem := hm₂ ▸ hf₃
      refine (hf₁.sub hcww).trans (hf₃'.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp [CWW], Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 336, 72⟩, by simp [CWW], Region.sub_prefix (by omega_arith)⟩
    · have : kOf P L u₃.mem = kOf P L u₂.mem := bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by have := L.he; omega_arith) (by omega_arith)
        · exact Offset.disjoint _ (by simp only [fKb]; omega_arith) (by omega_arith)
            (by have := hL.nb; have := L.he; simp only [fKb]; omega_arith)) (by omega_arith)
      rw [this, hm₂, hk₁]
    · have : vOf P L u₃.mem = vOf P L u₂.mem := bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by have := L.he; omega_arith) (by omega_arith)
        · exact Offset.disjoint _ (by simp only [fKb]; omega_arith) (by omega_arith)
            (by have := hL.nb; have := L.he; simp only [fKb]; omega_arith)) (by omega_arith)
      rw [this, hm₂, hv₁]
    · simp only [fKb] at hb₃
      rw [hb₃, hm₂, hb₁]

end VG.Proof.Ecdsa.Rfc6979.X86_64
