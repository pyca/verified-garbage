import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen

/-!
# Deterministic ECDSA on 32-bit ARM: scalars longer than the hash

As on x86 (`Proof/Ecdsa/Rfc6979/X86/Wide.lean`), for a curve whose scalars
are longer than the hash function's output (`wide`: P-521's 66 bytes with
SHA-512's 64): the `Q` bytes at an offset in the frame's top words, shifted
right in place through the words at `scratch + 2560` (`conv_ok`, by
`loadBytes_ok`, `shrWords_ok` and `storeBytes_ok`, with `out` and `d` kept in
`r2` and `r3` meanwhile, as those use `r4` and `r5`); the digest for `core`,
the digest then `Q - D` zero bytes shifted right, which is the digest's
number shifted left by `sh` bits (`coreDigest_ok`); and the candidate, `V`
kept in the frame's top words and, after the next `V`, its first word after
it, shifted right by `sh` bits (`candW_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Mont (wordsVal Outside off ofs)
open VG.Proof.Mont.Arm (Scr)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm dpVal)
open VG.Proof.Weierstrass.Arm (loadBytes_ok shrWords_ok storeBytes_ok)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  have h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  have h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_arith)

/-- `scratch`'s first 4096 bytes, as the conversions address them from `r12`. -/
theorem scr_of (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.scr) :
    Scr t (State.addr L.scr) 4096 :=
  ⟨by rw [h12], ⟨8192, by omega_arith, by omega_arith, by rw [hwr]; simp⟩, by have := hL.nc; rw [toNat_addr]; omega_arith,
    Nat.le_refl _⟩

theorem scr_keep {s s' : State} {base : Addr} {size : Nat} (h : Scr s base size) (h12 : s'.gpr .r12 = s.gpr .r12)
    (hwr : s'.wr = s.wr) : Scr s' base size :=
  ⟨h12 ▸ h.wb, hwr ▸ h.wr, h.nowrap, h.small⟩

/-- In the wide case, the frame has 36 words at its top. -/
theorem e36 (hw : L.wide = P.R.wide) (hW : P.R.wide = true) : L.e = 36 := by
  rw [L.ew, hw, hW]; rfl

theorem allOnes_movt : ((0xffff : BitVec 16) ++ ((0xffff : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    BitVec.allOnes 32 := by decide

/-- `conv o s`: the `Q` bytes at `r8 + o`, in the frame's top words, shifted
right by `s` bits in place, through the words at `scratch + 2560`. -/
theorem conv_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t)
    {o s : Nat} (ho₁ : 216 ≤ o) (ho₂ : o + 72 ≤ 360) (hoe : encodable (BitVec.ofNat 32 o) = true) (hs₁ : 1 ≤ s)
    (hs₂ : s < 32) :
    WP isa (.block ((cfgOf P).conv o s)) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + o)) P.Q) >>> s) := by
  obtain ⟨hw9, hQ66, -, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have nB := hL.nB
  have nc := hL.nc
  have hfp := fp_toNat' hL
  have := L.sp.isLt
  have hw2 : (cfgOf P).w / 2 = P.w := by simp only [cfgOf, RfcHash.w]; omega_arith
  have hlen : (cfgOf P).len = P.Q := rfl
  simp only [Cfg.conv, hw2, hlen, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_reg _ _) fun u₂ v₂ => ?_
  refine wp_dp (op2_imm hoe) fun u₃ v₃ => wp_mov (op2_reg _ _) fun u₄ v₄ => ?_
  have K₄ : Rest [.r1, .r2, .r3, .r12] t u₄ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans (v₄.rest (by simp))
  have h12 : u₄.gpr .r12 = L.scr := by
    rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hc.r11]
  have hS₄ : Scr u₄ (State.addr L.scr) 4096 := scr_of hL (by rw [K₄.wr, hc.wr]) h12
  have hr1 : u₄.gpr .r1 = L.fp + BitVec.ofNat 32 o := by
    rw [v₄.other _ (by decide), v₃.gpr, dpVal, v₂.other _ (by decide), v₁.other _ (by decide), hc.r8]
  have ha₁ : State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 (24 + o) := hL.fpA (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (loadBytes_ok hS₄ (len := P.Q) (n := P.w) (o := 2560) (src := .r1) (by decide) (by omega_arith)
    (by rw [hr1, fp_toNat hL (by omega_arith)]; omega_arith) (by omega_arith) (by omega_arith)
    (fun d hd => by rw [hr1, ha₁, Offset.add_add, K₄.rd, K₄.wr]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [hr1, ha₁]; exact (hL.stk_scr (by omega_arith) (by omega_arith)))) fun u₅ ⟨hv₅, k₅, O₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shrWords_ok (scr_keep hS₄ (k₅.gpr _ (by decide)) k₅.wr) (n := P.w) (o := 2560) (sh := s)
    (by omega_arith) hs₁ hs₂) fun u₆ ⟨hv₆, k₆, O₆⟩ => ?_
  refine wp_movw fun u₇ v₇ => wp_movt fun u₈ v₈ => ?_
  have h10 : u₈.gpr .r10 = BitVec.allOnes 32 := by rw [v₈.gpr, v₇.gpr]; exact allOnes_movt
  have K₈ : Rest [.r4, .r5, .r10] u₅ u₈ :=
    (k₆.mono (by simp)).trans <| (v₇.rest (by simp)).trans (v₈.rest (by simp))
  have hS₈ : Scr u₈ (State.addr L.scr) 4096 := scr_keep hS₄
    (by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide)]) (by rw [K₈.wr, k₅.wr])
  have h8 : u₈.gpr .r8 = L.fp := by rw [K₈.gpr _ (by decide), k₅.gpr _ (by decide), K₄.gpr _ (by decide), hc.r8]
  have hdst : State.addr (u₈.gpr .r8) + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by
    rw [h8, hL.fpA0, Offset.add_add]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hS₈ (len := P.Q) (n := P.w) (d := o) (a := 2560) (dst := .r8) (by decide)
    (by decide) true (by rw [h10]; rfl) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [h8]; omega_arith) (by omega_arith)
    (fun e m hem => by
      rw [hdst, Offset.add_add, K₈.wr, k₅.wr, K₄.wr]; exact hc.inFrW (by omega_arith) (by omega_arith))
    (by rw [hdst]; exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm)) fun u₉ ⟨hb₉, k₉, O₉⟩ => ?_
  rw [hdst] at hb₉ O₉
  refine wp_mov (op2_reg _ _) fun u₁₀ v₁₀ => wp_mov (op2_reg _ _) fun u₁₁ v₁₁ => WP.block_nil ?_
  -- Through the conversion, every register but those it writes.
  have K : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → r ≠ .r12 →
      u₉.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 h10' h12' => by
    rw [k₉.gpr _ (by simp [h4, h5]), K₈.gpr _ (by simp [h4, h5, h10']), k₅.gpr _ (by simp [h4]),
      K₄.gpr _ (by simp [h1, h2, h3, h12'])]
  have hr2 : u₉.gpr .r2 = t.gpr .r4 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
  have hr3 : u₉.gpr .r3 = t.gpr .r5 := by
    rw [k₉.gpr _ (by decide), K₈.gpr _ (by decide), k₅.gpr _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)]
  have hg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → u₁₁.gpr r = t.gpr r :=
    fun r h1 h2 h3 h10' h12' => by
      by_cases h4 : r = .r4
      · subst h4; rw [v₁₁.other _ (by decide), v₁₀.gpr, hr2]
      by_cases h5 : r = .r5
      · subst h5; rw [v₁₁.gpr, v₁₀.other _ (by decide), hr3]
      rw [v₁₁.other _ h5, v₁₀.other _ h4, K r h1 h2 h3 h4 h5 h10' h12']
  have m₄ : u₄.mem = t.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have m₈ : u₈.mem = u₆.mem := by rw [v₈.mem, v₇.mem]
  have hm : u₁₁.mem = u₉.mem := by rw [v₁₁.mem, v₁₀.mem]
  -- What changed: the words at `scratch + 2560`, and the bytes converted.
  have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (24 + o), P.Q⟩]
      t.mem u₁₁.mem := by
    have f₅ := frame_of_outside (O₅.trans O₆) (by omega_arith)
    have f₉ := frame_of_outside O₉ (by omega_arith)
    rw [BitVec.add_zero, m₈] at f₉
    rw [show 8 * P.w = 72 by omega_arith, m₄] at f₅
    rw [hm]
    exact (f₅.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₉.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  have hp : ∀ r ∈ ptrRegs, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  refine ⟨hc.keep hL (by rw [v₁₁.rd, v₁₀.rd, k₉.rd, K₈.rd, k₅.rd, K₄.rd])
      (by rw [v₁₁.wr, v₁₀.wr, k₉.wr, K₈.wr, k₅.wr, K₄.wr]) (by rw [v₁₁.sp, v₁₀.sp, k₉.sp, K₈.sp, k₅.sp, K₄.sp])
      (fun r hr => hg r (hp r hr).1 (hp r hr).2.1 (hp r hr).2.2.1 (hp r hr).2.2.2.1 (hp r hr).2.2.2.2) hf
      fun r hr => ?_, hg, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact safe_scr L (by omega_arith)
    · exact safe_high L (by omega_arith) (by omega_arith)
  · rw [ecdsa_bytesAt] at hb₉
    simp only [ite_true] at hb₉
    rw [hm, hb₉, m₈, hv₆, hv₅, hr1, ha₁, ecdsa_bytesAt, m₄]

/-! ## Copies into the frame's top words -/

theorem fpd (hL : L.Ok) (d : Nat) : State.addr L.fp + BitVec.ofNat 64 d = L.B + BitVec.ofNat 64 (24 + d) := by
  rw [hL.fpA0, Offset.add_add]

/-- `4 K` bytes copied to `r8 + d`, in the frame's top words, by `copyN`, with `Ctx` kept. -/
theorem copyF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {so d K : Nat} (hd₁ : 216 ≤ d) (hd₂ : d + 4 * K ≤ 216 + 4 * L.e) (hso : so + 4 * K ≤ 4096)
    (hsn : S.toNat + so + 4 * K ≤ 2 ^ 32)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, 4 * K⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .r8 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) (4 * K) =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) (4 * K) := by
  have nB := hL.nB
  have he := L.he
  have hfp := fp_toNat' hL
  have := L.sp.isLt
  refine WP.mono (copyN_ok (K := K) (by decide) hsr (by rw [fpd hL]; exact hsep) hsn (by omega_arith) hso (by omega_arith) K
    (Nat.le_refl _) u hs hc.r8 hr fun j hj => by rw [fpd hL]; exact hc.inFrW (by omega_arith) (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
  rw [fpd hL] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)), hg, hf, hb⟩

/-- A zero word at `r8 + o`, in the frame's top words. -/
theorem zeroF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho₁ : 216 ≤ o)
    (ho₂ : o + 4 ≤ 216 + 4 * L.e) :
    WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r8 o]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + o)) k = List.replicate k 0 := by
  have he := L.he
  refine wp_mov (op2_imm (v := 0) (by decide)) fun s₁ u₁ =>
    wp_str (a := L.B + BitVec.ofNat 64 (24 + o)) (by omega_arith)
      (by rw [u₁.other _ (by decide), hc.r8]; exact hL.fpA (by omega_arith))
      (by rw [u₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun s₂ m₂ => WP.block_nil ?_
  have hm : s₂.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (24 + o)) (0 : BitVec 32) := by
    rw [m₂.mem, u₁.mem, u₁.gpr]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (24 + o), 4⟩] u.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(hc.upd u₁ (by decide)).keep hL m₂.rd m₂.wr m₂.sp (fun r _ => by rw [m₂.gpr]) (by rw [u₁.mem]; exact hf)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)),
    fun r hr => by rw [m₂.gpr, u₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

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
    {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).coreDigest) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 240, P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have hsh := sh7 hW
  have nB := hL.nB
  have ng := hL.ng
  show WP isa (.block ([.mov .r0 (.imm 0), .str .r0 .r8 (216 + P.Q - 4)] ++
    Cfg.copyN (P.F.H.D / 4) .r6 0 .r8 216 ++ (cfgOf P).conv 216 (8 * (P.Q - P.F.H.D) - P.R.sh))) t _
  rw [hQ66, hD64, hsh, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zeroF_ok hL hc (o := 216 + 66 - 4) (by omega_arith) (by omega_arith)) fun u₁ ⟨hc₁, hg₁, hf₁, hz₁⟩ => ?_
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) 64 = Spec.Sha256.bytesAt t.mem (State.addr L.dg) 64 :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))).symm)
      (by omega_arith)
  refine WP.mono (copyF_ok hL hc₁ (src := .r6) (S := L.dg) hc₁.r6 (by decide) (so := 0) (d := 216) (K := 64 / 4)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (fun j hj => hc₁.inDg (by omega_arith) (by omega_arith))
    (by rw [BitVec.add_zero]
        exact ((hL.kg.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))).symm))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [BitVec.add_zero] at hb₂
  refine WP.mono (conv_ok hL hw hW hc₂ (o := 216) (s := 8 * (66 - 64) - 7) (by omega_arith) (by omega_arith) (by decide)
    (by omega_arith) (by omega_arith)) fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv] at hf₁ hz₁ hf₂ hb₂ hf₃ hb₃
  rw [hQ66] at hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩)).trans hf₃
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · -- The digest then two zero bytes, shifted right by 9 bits.
    have hY : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) 66 =
        Spec.Sha256.bytesAt t.mem (State.addr L.dg) 64 ++ List.replicate 2 0 := by
      rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, hb₂, hdg₁, Offset.add_add]
      refine congrArg (Spec.Sha256.bytesAt t.mem (State.addr L.dg) 64 ++ ·) ?_
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
abbrev CWW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩, ⟨L.B + BitVec.ofNat 64 312, 72⟩]

theorem kvw_cww : ∀ r ∈ KVW L, ∃ r' ∈ CWW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CWW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- Two `V`s to a candidate: `V = HMAC_K(V)`, kept in the frame's top
words, then `V = HMAC_K(V)` again, its first word after it, and the
candidate's `Q` bytes shifted right by `sh` bits. -/
theorem candW_ok (hL : L.Ok) (hw : L.wide = P.R.wide) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ u.gpr .r9 = t.gpr .r9 ∧ Frame (CWW L) t.mem u.mem ∧
      kOf P L u.mem = kOf P L t.mem ∧
      vOfP P L u.mem = P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOfP P L t.mem)) ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) P.Q =
        Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes ((P.mac (kOf P L t.mem) (vOfP P L t.mem) ++
          P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOfP P L t.mem))).take P.Q) >>> P.R.sh) := by
  obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hW
  have he := e36 hw hW
  have hsh := sh7 hW
  have nB := hL.nB
  have hfp := fp_toNat' hL
  have := L.sp.isLt
  have hwd : (cfgOf P).wide = true := hW
  have hD' : (cfgOf P).F.H.D = 64 := hD64
  simp only [Cfg.cand, Cfg.keepV, Cfg.candTop, hwd, ite_true, fV, fKb, hD', Nat.reduceDiv, Nat.reduceAdd]
  refine WP.seq (WP.mono (hmacV_ok hL hc) fun u₁ ⟨hc₁, h9₁, hf₁, hk₁, hv₁⟩ => ?_)
  -- `V` in the frame's top words.
  refine WP.seq (WP.mono (copyF_ok hL hc₁ (src := .r8) (S := L.fp) hc₁.r8 (by decide) (so := 64) (d := 288)
    (K := 16) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [fpd hL]; exact hc₁.inFr (by omega_arith) (by omega_arith))
    (by rw [fpd hL]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_)
  rw [fpd hL] at hb₂
  simp only [Nat.reduceAdd, Nat.reduceMul] at hf₂ hb₂
  have hk₂ : kOf P L u₂.mem = kOf P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
    (by anums)
  have hv₂ : vOfP P L u₂.mem = vOfP P L u₁.mem := bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
    (by anums)
  refine WP.seq (WP.mono (hmacV_ok hL hc₂) fun u₃ ⟨hc₃, h9₃, hf₃, hk₃, hv₃⟩ => ?_)
  have hb₃ : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) 64 = vOfP P L u₁.mem := by
    rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by omega_arith), hb₂]
    show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 88) 64 = Spec.Sha256.bytesAt u₁.mem _ P.F.H.D
    rw [hD64]
  rw [WP.block_append_iff]
  -- The next four bytes, from `V`.
  refine WP.mono (copyW_ok (u := u₃) (src := .r8) (dst := .r8) (so := 64) (d := 352) hc₃.r8 hc₃.r8 (by omega_arith)
    (by omega_arith) (hL.fpA (by omega_arith)) (hL.fpA (by omega_arith)) (hc₃.inFr (by omega_arith) (by omega_arith))
    (hc₃.inFrW (by omega_arith) (by omega_arith)) (by decide)) fun u₄ ⟨hrd₄, hwr₄, hsp₄, hg₄, hm₄⟩ => ?_
  simp only [Nat.reduceAdd] at hm₄
  have hf₄ : Frame [⟨L.B + BitVec.ofNat 64 376, 4⟩] u₃.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₄ : Ctx L g m₀ u₄ := hc₃.keep hL hrd₄ hwr₄ hsp₄ (fun r hr => hg₄ r (ptr_r0 r hr)) hf₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega_arith) (by omega_arith)
  refine WP.mono (conv_ok hL hw hW hc₄ (o := 288) (s := P.R.sh) (by omega_arith) (by omega_arith) (by decide) (by omega_arith)
    (by omega_arith)) fun u₅ ⟨hc₅, hg₅, hf₅, hb₅⟩ => ?_
  simp only [Nat.reduceAdd] at hf₅ hb₅
  -- `K` and `V`, apart from the candidate and `scratch`.
  have dK : ∀ r ∈ [(⟨State.addr L.scr + BitVec.ofNat 64 2560, 72⟩ : Region), ⟨L.B + BitVec.ofNat 64 312, P.Q⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hL.stk_scr (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have dK₄ : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 376, 4⟩ : Region)],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  have kv : ∀ {m m' : Mem} {ws : List Region}, Frame ws m m' →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 24, 128⟩ r) →
      kOf P L m' = kOf P L m ∧ vOfP P L m' = vOfP P L m := fun hf hd =>
    ⟨bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 0)) (n := P.F.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by anums))) (by anums),
      bytesAt_frame (p := L.B + BitVec.ofNat 64 88) (n := P.F.H.D) hf
        (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_arith) (by anums))) (by anums)⟩
  have e₅ := kv hf₅ dK
  have e₄ := kv hf₄ dK₄
  refine ⟨hc₅, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg₄ _ (by decide), h9₃,
      hg₂ _ (by decide), h9₁]
  · have c₃ : (⟨L.B + BitVec.ofNat 64 312, 72⟩ : Region) ∈ CWW L := by simp [CWW]
    have c₁ : L.SCR ∈ CWW L := by simp [CWW]
    refine ((((hf₁.sub kvw_cww).trans (hf₂.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩)).trans
      (hf₃.sub kvw_cww)).trans (hf₄.sub fun r hr => ⟨_, c₃, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)⟩)).trans
      (hf₅.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, c₁, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, c₃, Region.sub_prefix (by omega_arith)⟩
  · rw [e₅.1, e₄.1, hk₃, hk₂, hk₁]
  · rw [e₅.2, e₄.2, hv₃, hk₂, hv₂, hv₁, hk₁]
  · -- The candidate's bytes: the first `V`, then the next two of the second.
    have hkv : P.mac (kOf P L t.mem) (vOfP P L t.mem) = vOfP P L u₁.mem := hv₁.symm
    have hv₃' : P.mac (kOf P L t.mem) (P.mac (kOf P L t.mem) (vOfP P L t.mem)) = vOfP P L u₃.mem := by
      rw [hv₃, hk₂, hv₂, hv₁, hk₁]
    rw [hQ66] at hb₅ ⊢
    rw [hb₅, hv₃', hkv, List.take_append, List.take_of_length_le (by simp [Spec.Sha256.bytesAt]; omega_arith),
      show 66 - (vOfP P L u₁.mem).length = 2 by simp [Spec.Sha256.bytesAt]; omega_arith]
    refine congrArg (fun x => Spec.Weierstrass.toBytes 66 (Spec.Weierstrass.ofBytes x >>> P.R.sh)) ?_
    rw [show (66 : Nat) = 64 + 2 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    simp only [Nat.reduceAdd]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by omega_arith), hb₃]
    · rw [bytesAt_take _ _ (k := 4) (by omega_arith), hm₄, bytesAt_copied]
      show _ = (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 88) P.F.H.D).take 2
      rw [hD64, ← bytesAt_take _ _ (by omega_arith), ← bytesAt_take _ _ (by omega_arith)]

end VG.Proof.Ecdsa.Rfc6979.Arm
