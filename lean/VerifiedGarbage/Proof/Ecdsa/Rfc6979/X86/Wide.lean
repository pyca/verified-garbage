import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen

/-!
# Deterministic ECDSA on x86 (32-bit): scalars longer than the hash

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Wide.lean`), for a curve whose
scalars are longer than the hash function's output (`wide`: P-521's 66 bytes
with SHA-512's 64): the `Q` bytes at an offset in the frame's top words,
shifted right in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`); the digest for `core`,
the digest then `Q - D` zero bytes shifted right, which is the digest's
number shifted left by `sh` bits (`coreDigest_ok`); and the candidate, `V`
kept in the frame's top words and, after the next `V`, its first word after
it, shifted right by `sh` bits (`candW_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.X86 (Scr Keeps)
open VG.Proof.Weierstrass.X86 (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

theorem scr_of (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) : Scr t L.scr 8192 := by
  have hn : L.scr.toNat + 8192 ≤ 2 ^ 32 := by
    have := hL.nc; have := L.a3.isLt
    simp only [Lay.scr, BitVec.toNat_setWidth]; omega_arith
  have hF : 20 ≤ L.F.toNat := by have := hL.FN; have := hL.e272; omega_arith
  -- The calls' 20 bytes below `F` are in the stack the contract gives.
  have hd : Region.Disjoint ⟨L.F.setWidth 64 - BitVec.ofNat 64 20, 20⟩ ⟨L.scr, 8192⟩ := by
    rw [hL.F64, Offset.add_ofNat_sub _ (by decide)]
    exact hL.stk_scr0 (by omega_arith) (Nat.le_refl _)
  refine ⟨by rw [hdi], by rw [hc.wr]; simp, hn, ?_⟩
  rw [hc.esp]
  exact VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl _) hF hn (by decide) hd

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (hdi : s'.gpr .edi = s.gpr .edi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hwr : s'.wr = s.wr) : Scr s' base size :=
  h.of_eq hdi hsp hwr

/-- In the wide case, the frame has 36 words at its top. -/
theorem e36 (hw : L.wide = P.R.wide) (hW : P.R.wide = true) : L.e = 36 := by
  rw [L.ew, hw, hW]; rfl

/-- `conv o s`: the `Q` bytes at `esp + o`, in the frame's top words,
shifted right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    (hdi : t.gpr .edi = L.a3) {o s : Nat} (ho₁ : 196 ≤ o) (ho₂ : o + 72 ≤ 340) (hs₁ : 1 ≤ s) (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → t'.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (76 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have nB := hL.nB
  have hFN := hL.FN
  have e272 := hL.e272
  have e20 := hL.e20
  have hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, RfcHash.w]; omega_arith
  refine WP.of_syms ?_
  rw [Cfg.conv, hw2, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) o) fun u₁ h₁ => ?_
  have hS₁ : Scr u₁ L.scr 8192 := scr_keep (scr_of hL hc hdi) (h₁.keep _ (by decide))
    (h₁.keep _ (by decide)) (by rw [h₁.ctx.wr, hc.wr])
  have hsi₁ : u₁.gpr .esi = L.F + BitVec.ofNat 32 o := h₁.val
  have ha₁ : (L.F + BitVec.ofNat 32 o).setWidth 64 = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine WP.mono (loadBytes_ok hS₁ (len := P.Q) (n := P.w) (o := 2560) (src := .esi) (by decide) (by omega_arith)
    (by rw [hsi₁, hL.frN (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hsi₁, ha₁, Offset.add_add]; exact h₁.ctx.inFr (by omega_arith) (by omega_arith) hL)
    (by rw [hsi₁, ha₁]; exact hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hv₂, k₂, O₂⟩ => ?_
  refine WP.mono (shrWords_ok (scr_keep hS₁ (k₂.1 _ (by decide)) (k₂.1 _ (by decide)) k₂.2.2) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₃ ⟨hv₃, k₃, O₃⟩ => ?_
  refine wp_movi fun u₄ v₄ => WP.block_nil ?_
  have hsp₄ : u₄.gpr .esp = L.F := by
    rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), h₁.keep _ (by decide), hc.esp]
  have hwr₄ : u₄.wr = t.wr := by rw [v₄.wr, k₃.2.2, k₂.2.2, h₁.ctx.wr, hc.wr]
  have hS₄ : Scr u₄ L.scr 8192 := scr_keep hS₁ (by rw [v₄.other _ (by decide), k₃.1 _ (by decide),
    k₂.1 _ (by decide)]) (by rw [v₄.other _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide)])
    (by rw [v₄.wr, k₃.2.2, k₂.2.2])
  have hdst : (u₄.gpr .esp).setWidth 64 + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (76 + o) := by
    rw [hsp₄, hL.F64, Offset.add_add]
  refine WP.mono (storeBytes_ok hS₄ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .esp) (by decide)
    (by decide) true (by rw [v₄.gpr]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hsp₄, hFN]; omega_arith)
    (fun e m hem => by rw [hdst, Offset.add_add, hwr₄]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₅ ⟨hb₅, k₅, O₅⟩ => ?_
  intro hsy
  rw [hdst] at hb₅ O₅
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (76 + o), P.Q⟩] t.mem u₅.mem := by
    have f₂ := frame_of_outside (O₂.trans O₃) (by omega_arith)
    have f₅ := frame_of_outside O₅ (by omega_arith)
    rw [BitVec.add_zero, v₄.mem] at f₅
    rw [h₁.mem, show 8 * P.w = 72 by omega_arith] at f₂
    exact (f₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → u₅.gpr r = t.gpr r := fun r h₁' h₂ h₃ h₄ => by
    rw [k₅.1 _ (by simp [h₁', h₃]), v₄.other _ h₂, k₃.1 _ (by simp [h₁', h₃]), k₂.1 _ (by simp [h₁']),
      h₁.keep _ h₄]
  refine ⟨hc.keep (hsy := hsy) hL (by rw [k₅.2.1, v₄.rd, k₃.2.1, k₂.2.1, h₁.ctx.rd, hc.rd]) (by rw [k₅.2.2, hwr₄])
      (hg _ (by decide) (by decide) (by decide) (by decide)) hf fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₅
    simp only [ite_true] at hb₅
    rw [hb₅, v₄.mem, hv₃, hv₂, hsi₁, ha₁, ecdsa_bytesAt, h₁.mem]

/-! ## Copies into the frame's top words -/

/-- `4 K` bytes copied to `esp + d`, in the frame's top words, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {so d K : Nat} (hd₁ : 196 ≤ d) (hd₂ : d + 4 * K ≤ 196 + 4 * L.e)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .esp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + d)) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  have nB := hL.nB
  have he := L.he
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => fr_addr hL (by omega_arith)) hsep (by omega_arith) K
    (Nat.le_refl _) u hs hc.esp hr fun j hj => by rw [Offset.add_add]; exact hc.inFrW (by omega_arith) (by omega_arith) hL)
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)), hg, hf, hb⟩

/-- A zero word at `esp + o`, in the frame's top words. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 196 ≤ o)
    (ho₂ : o + 4 ≤ 196 + 4 * L.e) :
    WP isa (.block [.mov .eax (.imm 0), .store (stk o) .eax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + o)) k = List.replicate k 0 := by
  have nB := hL.nB
  have ea : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF (by omega_arith)
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other .esp (by decide), hc.esp])
    (by rw [v₁.wr, ea]; exact hc.inFrW (by omega_arith) (by omega_arith) hL) fun u₂ v₂ => WP.block_nil ?_
  have hm : u₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (76 + o)) (0 : BitVec 32) := by
    rw [v₂.mem, v₁.gpr, v₁.mem, ea]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + o), 4⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    fun r hr => by rw [v₂.gpr, v₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `sh` is 7 for P-521's sizes. -/
theorem sh7 (hW : P.R.wide = true) : P.R.sh = 7 := by
  have h₁ := P.R.nBits_len; have h₂ := P.R.sizesW hW; omega_arith

theorem shift_mul (e : Nat) : (e * 2 ^ (8 * 2)) >>> (8 * (66 - 64) - 7) = e * 2 ^ 7 := by
  rw [show 8 * (66 - 64) - 7 = 9 from rfl, Nat.shiftRight_eq_div_pow,
    show e * 2 ^ (8 * 2) = e * 2 ^ 7 * 2 ^ 9 by rw [Nat.mul_assoc, ← Nat.pow_add],
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-! ## The digest for `core` -/

/-- The digest for `core`: the digest's number shifted left by `sh` bits, in
`Q` bytes in the frame's top words. -/
theorem coreDigest_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) (hdn : P.F.H.D ≤ dn)
    {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a2) (hdi : t.gpr .edi = L.a3) :
    WP isa (.block (cfgOf P).coreDigest) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 272, P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 272) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem L.dg P.F.H.D) * 2 ^ P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have hsh := sh7 hW
  have nB := hL.nB
  have ng := hL.ng
  show WP isa (.block ([.mov .eax (.imm 0), .store (stk (196 + P.Q - 4)) .eax] ++
    Cfg.copyN (P.F.H.D / 4) .esi 0 .esp 196 ++ (cfgOf P).conv 196 (8 * (P.Q - P.F.H.D) - P.R.sh))) t _
  rw [hQ66, hD64, hsh, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zeroF_ok hL hc (o := 196 + 66 - 4) (by omega_arith) (by omega_arith)) fun u₁ ⟨hc₁, hg₁, hf₁, hz₁⟩ => ?_
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg 64 = Spec.Sha256.bytesAt t.mem L.dg 64 :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))).symm)
      (by omega_arith)
  refine WP.mono (copyF_ok hL hc₁ (src := .esi) (S := L.a2) (SA := L.dg) ((hg₁ _ (by decide)).trans hsi)
    (by decide) (so := 0) (d := 196) (K := 64 / 4) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
    (fun j hj => hc₁.inDg (by omega_arith) (by omega_arith))
    ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))).symm)
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (conv_ok hL hw hW hc₂ (by rw [hg₂ _ (by decide), hg₁ _ (by decide), hdi]) (o := 196)
    (s := 8 * (66 - 64) - 7) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] at hf₁ hz₁ hf₂ hb₂ hf₃ hb₃
  rw [hQ66] at hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans hf₃
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · -- The digest then two zero bytes, shifted right by 9 bits.
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 272) 66 =
        Spec.Sha256.bytesAt t.mem L.dg 64 ++ List.replicate 2 0 := by
      rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, hb₂, hdg₁, Offset.add_add]
      refine congrArg (Spec.Sha256.bytesAt t.mem L.dg 64 ++ ·) ?_
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by omega_arith)]
      have h4 := hz₁ (2 + 2) (by omega_arith)
      rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add, ← List.replicate_append_replicate] at h4
      simp only [Nat.reduceAdd] at h4 ⊢
      exact (List.append_inj h4 (by simp [Spec.Sha256.bytesAt])).2
    rw [hb₃, hY, ofBytes_append_zeros, shift_mul]

/-! ## The candidate -/

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, and the candidate in the frame's top words. -/
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 204⟩, ⟨L.B + BitVec.ofNat 64 344, 72⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- Two `V`s to a candidate: `V = HMAC_K(V)`, kept in the frame's top
words, then `V = HMAC_K(V)` again, its first word after it, and the
candidate's `Q` bytes shifted right by `sh` bits. -/
theorem candW_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CWW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 344) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes ((P.mac (kOf P L t.mem) (vOf P L t.mem) ++
          P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem))).take P.Q) >>> P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have hsh := sh7 hW
  have nB := hL.nB
  have hwd : (cfgOf P).wide = true := hW
  have hD' : (cfgOf P).F.H.D = 64 := hD64
  simp only [Cfg.cand, Cfg.keepV, Cfg.candTop, Cfg.scrPtr, hwd, ite_true, fV, fKb, hD', Nat.reduceDiv,
    Nat.reduceAdd]
  refine WP.seq (WP.mono (hmacV_ok hL hw hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  -- `V` in the frame's top words.
  refine WP.seq (WP.mono (copyF_ok hL hc₁ (src := .esp) (S := L.F) (SA := L.B + BitVec.ofNat 64 140) hc₁.esp
    (by decide) (so := 64) (d := 268) (K := 16) (by omega_arith) (by omega_arith) (fun j hj => fr_addr hL (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact hc₁.inFr (by omega_arith) (by omega_arith) hL)
    (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_)
  simp only [Nat.reduceAdd, Nat.reduceMul] at hf₂ hb₂
  have hk₂ : kOf P L u₂.mem = kOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  have hv₂ : vOf P L u₂.mem = vOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  refine WP.seq (WP.mono (hmacV_ok hL hw hc₂) fun u₃ ⟨hc₃, hf₃, hk₃, hv₃⟩ => ?_)
  have hb₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 344) 64 = vOf P L u₁.mem := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by omega_arith), hb₂]
    show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 140) 64 = Spec.Sha256.bytesAt u₁.mem _ P.F.H.D
    rw [hD64]
  -- `scratch` in `edi`.
  have ha := arg_ok hL hc₃ (d := .edi) (by decide) (i := 3) (by omega_arith)
  rw [hw, hW] at ha
  refine WP.seq (WP.mono ha fun u₄ h₄ => ?_)
  rw [WP.block_append_iff]
  -- The next four bytes, from `V`.
  have hr₄ : InRegions (u₄.rd ++ u₄.wr) (addr L.F 64) 4 := by
    rw [hL.addrF (by omega_arith)]; exact h₄.ctx.inFr (by omega_arith) (by omega_arith) hL
  have hw₄ : InRegions u₄.wr (addr L.F 332) 4 := by
    rw [hL.addrF (by omega_arith)]; exact h₄.ctx.inFrW (by omega_arith) (by omega_arith) hL
  refine WP.mono_syms (copyW_ok (u := u₄) (src := .esp) (dst := .esp) (so := 64) (d := 332) h₄.ctx.esp h₄.ctx.esp hr₄
    hw₄ (by decide)) fun u₅ ⟨hrd₅, hwr₅, hg₅, hm₅⟩ hsy₅ => ?_
  rw [hL.addrF (by omega_arith), hL.addrF (by omega_arith)] at hm₅
  simp only [Nat.reduceAdd] at hm₅
  have hf₅ : Frame [⟨L.B + BitVec.ofNat 64 408, 4⟩] u₄.mem u₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₅ : Ctx L g m₀ u₅ := h₄.ctx.keep (hsy := hsy₅) hL hrd₅ hwr₅ (hg₅ _ (by decide)) hf₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)
  refine WP.mono (conv_ok hL hw hW hc₅ (by rw [hg₅ _ (by decide), h₄.val]; rfl) (o := 268) (s := P.R.sh)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun u₆ ⟨hc₆, _, hf₆, hb₆⟩ => ?_
  simp only [Nat.reduceAdd] at hf₆ hb₆
  -- `K` and `V`, apart from the candidate and `scratch`.
  have dK : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 2560, 72⟩ : Region), ⟨L.B + BitVec.ofNat 64 344, P.Q⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hL.stk_scr (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have dK₅ : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 408, 4⟩ : Region)],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have kv : ∀ {m m' : Mem} {ws : List Region}, Frame ws m m' →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ r) →
      kOf P L m' = kOf P L m ∧ vOf P L m' = vOf P L m := fun hf hd =>
    ⟨bytesAt_frame (p := L.B + BitVec.ofNat 64 76) (n := P.F.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by nums))) (by nums),
      bytesAt_frame (p := L.B + BitVec.ofNat 64 140) (n := P.F.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by nums))) (by nums)⟩
  have e₆ := kv hf₆ dK
  have e₅ := kv hf₅ dK₅
  rw [h₄.mem] at e₅
  refine ⟨hc₆, ?_, ?_, ?_, ?_⟩
  · have c₃ : (⟨L.B + BitVec.ofNat 64 344, 72⟩ : Region) ∈ CWW L := by simp [CWW]
    have c₁ : L.SCR ∈ CWW L := by simp [CWW]
    refine ((((hf₁.sub kvw_cww).trans (hf₂.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩)).trans
      (hf₃.sub kvw_cww)).trans (h₄.mem ▸ hf₅.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)).trans
      (hf₆.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c₁, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, c₃, Region.sub_prefix (by omega_arith)⟩
  · rw [e₆.1, e₅.1, hk₃, hk₂, hk₁]
  · rw [e₆.2, e₅.2, hv₃, hk₂, hv₂, hv₁, hk₁]
  · -- The candidate's bytes: the first `V`, then the next two of the second.
    have hkv : P.mac (kOf P L t.mem) (vOf P L t.mem) = vOf P L u₁.mem := hv₁.symm
    have hv₃' : P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOf P L t.mem)) = vOf P L u₃.mem := by
      rw [hv₃, hk₂, hv₂, hv₁, hk₁]
    rw [hQ66] at hb₆ ⊢
    rw [hb₆, hv₃', hkv, List.take_append, List.take_of_length_le (by simp [Spec.Sha256.bytesAt]; omega_arith),
      show 66 - (vOf P L u₁.mem).length = 2 by simp [Spec.Sha256.bytesAt]; omega_arith]
    refine congrArg (fun x => Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes x >>> P.R.sh)) ?_
    rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [bytesAt_frame hf₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by omega_arith), h₄.mem, hb₃]
    · rw [bytesAt_take _ _ (k := 4) (by omega_arith), hm₅, bytesAt_copied, h₄.mem]
      show _ = (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 140) P.F.H.D).take 2
      rw [hD64, ← bytesAt_take _ _ (by omega_arith), ← bytesAt_take _ _ (by omega_arith)]

end VG.Proof.Ecdsa.Rfc6979.X86
