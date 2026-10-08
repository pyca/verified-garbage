import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Flags

/-!
# ECDSA on x86 (32-bit): `x`, `r`, `k R mod n` and the checks of `d`, `k`, `r`

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form (a multiplication by 1), `r = x mod n` (an addition of
zero modulo `n`, as `x < p < 2n`) and `k R mod n` (a multiplication by
`R² mod n`), then ands the masks of `d, k ∈ [1, n-1]` and `r ≠ 0` into the
flag (`middle_ok`).
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem middle_eq (c : Cfg) : c.middle = .seq (Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (Mont.addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO))
    (.seq (Mont.mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N))
    (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR)))))) := rfl

/-- What `middle`'s field operations leave. -/
structure MidPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [XM, X, RR, KM, TMP] ++ wkW c) s.mem s'.mem
  modP : ModOkW c.MP' size c.C.p s'.mem base
  modN : ModOkW c.MN' size c.C.n s'.mem base
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  rr : sv c base s' RR = sv c base s' X % c.C.n
  km_lt : sv c base s' KM < c.C.n
  km : toM c.C.n (2 ^ (64 * c.n)) (sv c base s' KM) = Fin.ofNat c.C.n (sv c base s K)

theorem unch_slots {base : Addr} {m₁ m₂ : Mem} {o : Nat} {l : List Nat} {M : Mod} (hMn : M.n = c.n)
    (hMt : M.tmp = c.sl TMP)
    (h : Unch base [(c.sl o, 8 * M.n), (M.tmp, 8 * M.n), (c.wk, 64 * M.n), Mont.outW] m₁ m₂)
    (ho : o ∈ l) (ht : TMP ∈ l) : Unch base (slW c l ++ wkW c) m₁ m₂ :=
  h.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hMn, hMt] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_map_of_mem ho)
    · exact List.mem_append_left _ (List.mem_map_of_mem ht)
    · exact List.mem_append_right _ (by simp [wkW])
    · exact List.mem_append_right _ (by simp [wkW])

/-- The four field operations of `middle`. -/
theorem midOps_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOkW c.MP' size c.C.p s.mem base) (hMN : ModOkW c.MN' size c.C.n s.mem base)
    (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1) (hzero : sv c base s ZERO = 0)
    (hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', MidPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
      (.seq (Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
      (.seq (Mont.addCall c.SN (c.sl RR) (c.sl X) (c.sl ZERO))
      (.seq (Mont.mulCall c.SN (c.sl KM) (c.sl K) (c.sl R2N)) rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hpn := hc.p_lt_2n
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs (o := XM) (a := RX) (b := ACC) (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hMP.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have kN₁ := hMN.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have one₁ : sv c base s₁ ONE = 1 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hone
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs₁ (o := X) (a := XM) (b := ONE) (by decide) (by decide) (by decide) (by omega)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have kP₂ := kP₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have kN₂ := kN₁.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have zero₂ : sv c base s₂ ZERO = 0 := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hzero]
  have x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, one₁]), toM_mul hpR e₁]
  -- `RR = X mod n`.
  refine WP.seq (WP.mono (slAdd_ok (MN'_n c) hc.fn h7 hs₂ (o := RR) (a := X) (b := ZERO) (by decide) (by decide) (by decide) (by omega)) fun s₃ ⟨k₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have kP₃ := kP₂.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have kN₃ := kN₂.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hr2]
  have K₃ : sv c base s₃ K = sv c base s K := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)]
  -- `KM = K · R² mod n`.
  refine WP.seq (WP.mono (slMul_ok (MN'_n c) hc.fn h7 hs₃ (o := KM) (a := K) (b := R2N) (by decide) (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega))) fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  have X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    kP₃.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    kN₃.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, ?_, lt₄,
    by rw [toM_r2 hnR (by rw [e₄, r2₃]), K₃]⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MN'_n c) rfl k₃.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₄.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)))).mono fun w hw => by
        simpa only [List.mem_append, or_self] using hw
  · rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide), e₃, zero₂,
      Nat.add_zero, X₄]

end VG.Proof.Ecdsa.X86
