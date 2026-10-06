import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect

/-!
# RSASSA-PSS signing on AArch64: the checks and the encoding

`body_ok`: after the prologue (`AtChk`), the checks of the modulus' first
byte and of the lengths, and either zeros to `out` or the encoding and the
private operation: `out` holds `signOut G s`.
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV smear_ok emLen_ok saltFits_ok)

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem maskV_lt (x : Nat) (hx : x < 256) : (maskV x).toNat < 256 := by
  unfold maskV
  split
  · decide
  · rw [BitVec.toNat_ofNat]
    have : Nat.log2 x < 8 := by
      rcases Nat.eq_zero_or_pos x with h | h
      · subst h; decide
      · exact (Nat.log2_lt (by omega)).mpr hx
    have : 2 ^ Nat.log2 x ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem maskV_setWidth (x : Nat) (hx : x < 256) : (maskV x) = ((maskV x).setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := maskV_lt x hx
  omega

theorem mid_frame {s t t' : State} (hm : Mid s t) {rs : List Reg} (k : Keep rs t t') {d₁ d₂ : Nat}
    (h₁ : 248 ≤ d₁ ∧ d₁ + 8 ≤ 288) (h₂ : 248 ≤ d₂ ∧ d₂ + 8 ≤ 288) {v₁ v₂ : BitVec 64}
    (hmem : t'.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 d₁) v₁).writeW (fb s + BitVec.ofNat 64 d₂) v₂) :
    Mid s t' := by
  refine ⟨k.sp.trans hm.sp, k.rd.trans hm.rd, k.wr.trans hm.wr, fun r hr => (k.vcs r hr).trans (hm.v r hr), ?_⟩
  rw [hmem]
  have f : Frame [⟨fb s + BitVec.ofNat 64 d₁, 8⟩, ⟨fb s + BitVec.ofNat 64 d₂, 8⟩] t.mem
      ((t.mem.writeW (fb s + BitVec.ofNat 64 d₁) v₁).writeW (fb s + BitVec.ofNat 64 d₂) v₂) :=
    ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)
  refine hm.fr.frame f (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by decide) (by omega)

theorem body_ok {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
    (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (c : PrivChecked) {K : Nat} {s u : State}
    (hp : PreS H.D K s) (hK : 16 ≤ K) (hcK : c.stack ≤ K) (hu : AtChk s u) :
    WP isa (.ite (.zero .x .x10) signFail (seqs [.block smear, emLen H,
      .ite (.nonzero .x .x10) signFail (seqs [.block ([ld .x12 sSaltLen] ++ saltFits H),
        .ite (.nonzero .x .x10) signFail (signMain H c.name c.code)])])) u fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (signOut G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.sizes.DN
  have hN := hH.N_le
  have hk : 1 ≤ (s.gpr .x3).toNat := by omega
  have Mu : Mid s u := ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x2)).toNat := by rw [hu.x10, setWidth_byte]
  have hn₀ := (s.mem (s.gpr .x2)).isLt
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`.
    have h0 : s.mem (s.gpr .x2) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact this
    exact WP.mono (fail_ok hp Mu hu.x23) fun t ⟨m, r⟩ => ⟨m, by rw [signOut_zero G hk h0]; exact r⟩
  have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h => by
    rw [hx10, h] at hb; exact absurd hb (by decide)
  have h0' : (s.mem (s.gpr .x2)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  generalize hx : (s.mem (s.gpr .x2)).toNat = x at hx10 hn₀ h0'
  have hlo : loV x ≤ 1 := by unfold loV; split <;> omega
  have hrsl : ∀ {t : State}, t.sp = fb s → t.rd = s.rd → t.wr = ⟨fb s, frameBytes⟩ :: s.wr → ∀ {d : Nat},
      d + 8 ≤ frameBytes → InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) 8 := fun _ hrd hwr _ hd => by
    rw [hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  unfold seqs seqs seqs
  -- `smear` and `emLen`.
  refine WP.seq (WP.mono (smear_ok u (x := x) hn₀ h0' hx10) fun u₁ ⟨O₁, h11⟩ => ?_)
  refine WP.seq (WP.mono (emLen_ok H (by omega) (F := fb s) (by rw [O₁.sp, hu.sp]) hn₀ h0'
    (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide)) (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide))
    (k := (s.gpr .x3).toNat) (by rw [O₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk (by omega) h11)
    fun u₂ ⟨K₂, m₂, x9₂, x10₂⟩ => ?_)
  have M₂ : Mid s u₂ := mid_frame Mu (O₁.keep.trans K₂) (d₁ := sC) (d₂ := sLo) (by decide) (by decide)
    (by rw [m₂, O₁.mem])
  have x23₂ : u₂.gpr .x23 = s.gpr .x3 := by rw [K₂.get .x23, O₁.get .x23, hu.x23]
  refine WP.ite _ (eval_nonzero _ _) (fun hb₂ => ?_) (fun hb₂ => ?_)
  · -- `emLen < hLen + 2`.
    rw [x10₂, decide_eq_true_eq] at hb₂
    refine WP.mono (fail_ok hp M₂ x23₂) fun t ⟨m, r⟩ => ⟨m, ?_⟩
    rw [signOut_long G hk h0 (by rw [hx, hGl]; omega)]; exact r
  rw [x10₂, decide_eq_false_iff_not] at hb₂
  unfold seqs seqs
  refine WP.seq (WP.mono (saltFits_ok H (by omega) (F := fb s) (by rw [K₂.sp, O₁.sp, hu.sp])
    (hrsl (by rw [K₂.sp, O₁.sp, hu.sp]) (by rw [K₂.rd, O₁.rd, hu.rd]) (by rw [K₂.wr, O₁.wr, hu.wr]) (by decide))
    (a := (s.gpr .x3).toNat - loV x) (sl := (stackArg s 10).toNat) (by omega) (by omega) x9₂
    (by rw [M₂.fr.sl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (stackArg s 10).isLt)
    fun u₃ ⟨O₃, x9₃, x10₃⟩ => ?_)
  have M₃ : Mid s u₃ := ⟨O₃.sp.trans M₂.sp, O₃.rd.trans M₂.rd, O₃.wr.trans M₂.wr,
    fun r hr => (O₃.vcs r hr).trans (M₂.v r hr), O₃.mem ▸ M₂.fr⟩
  refine WP.ite _ (eval_nonzero _ _) (fun hb₃ => ?_) (fun hb₃ => ?_)
  · -- The salt does not fit.
    rw [x10₃, decide_eq_true_eq] at hb₃
    refine WP.mono (fail_ok hp M₃ (by rw [O₃.get .x23, x23₂])) fun t ⟨m, r⟩ => ⟨m, ?_⟩
    rw [signOut_long G hk h0 (by rw [hx, hGl]; omega)]; exact r
  rw [x10₃, decide_eq_false_iff_not] at hb₃
  have hm₃ : u₃.mem = (u.mem.writeW (fb s + BitVec.ofNat 64 sC) (maskV x)).writeW (fb s + BitVec.ofNat 64 sLo)
      (BitVec.ofNat 64 (loV x)) := by rw [O₃.mem, m₂, O₁.mem]
  have hA : AtMain H.D s (loV x) ((maskV x).setWidth 8) u₃ := {
    sp := M₃.sp
    rd := M₃.rd
    wr := M₃.wr
    x9 := x9₃
    x19 := by rw [O₃.get .x19, K₂.get .x19, O₁.get .x19, hu.x19]
    x20 := by rw [O₃.get .x20, K₂.get .x20, O₁.get .x20, hu.x20]
    x21 := by rw [O₃.get .x21, K₂.get .x21, O₁.get .x21, hu.x21]
    x23 := by rw [O₃.get .x23, x23₂]
    v := M₃.v
    mem := by
      rw [hm₃]
      exact (hu.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    fr := M₃.fr
    lo := by rw [hm₃, Mem.readW_writeW_self64]
    c := by
      rw [hm₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, ← maskV_setWidth x hn₀] }
  refine WP.mono (main_ok hH hGh hGl hG c hp hK hcK hA hlo (by omega)) fun t ⟨m, r⟩ => ⟨m, ?_⟩
  have := signOut_eq G hG hk h0 (by rw [hx, hGl]; omega)
  rw [hx, hGl] at this
  rw [this]; exact r

end VG.Proof.RsaPss.AArch64.Sgn
