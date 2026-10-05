import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT

/-!
# RSAES-OAEP encryption on x86-64: the points between the pieces

What the constant-time proof needs to know of one run between the pieces of
`encMain`: in the frame, with the argument slots as the prologue stored them
(`EW`), MGF1's slots too before MGF1 (`EWM`), and the arguments of
`vg_rsa_public_checked` before its call (`EWP`). Each piece's step is its
correctness lemma, of which only this is kept.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

/-- In the frame, with the argument slots as the prologue stored them. -/
structure EW (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 5)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 5) V W ∧ ArgsW s W

/-- Before MGF1, with its slots set. -/
structure EWM (s t : State) (src srcLen dst dstLen : Nat) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 5)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 5) V W ∧ ArgsW s W ∧ MArgs W (stackArg s 5) src srcLen dst dstLen

/-- The words of `vg_rsa_public_checked`'s stack arguments. -/
def pw (s : State) : Nat → BitVec 64
  | 0 => off (stackArg s 5) oEm
  | 1 => s.gpr .rcx
  | 2 => off (stackArg s 5) oRsa
  | _ => stackArg s 6 - 1024

/-- Before the call of `vg_rsa_public_checked`, with its arguments. -/
structure EWP (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 5)
  w : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = pw s i
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rcx
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = s.gpr .rcx
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9

/-- The argument slots. -/
def encKs : List Nat := [14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

theorem encKs_lt : ∀ k ∈ encKs, k < nW := by decide

theorem encKs_iff {k : Nat} (h : k ∈ encKs) : k = 14 ∨ (21 ≤ k ∧ k ≤ 31) := by
  simp only [encKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega

section
variable {H : Spec.Mgf1.Hash} {s t : State} (hp : EPre H s)
include hp

/-- The frame and the other writable regions. -/
theorem EnvE.frv (he : EnvE s t) : FrV 2 (fb s) [outR s, scrR s] t where
  rsp := he.rsp
  wr := he.wr
  two := rfl
  pw := by
    refine .cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_stk_out.sub_left (frame_sub s)
      · exact hp.d_stk_scr.sub_left (frame_sub s)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.d_out_scr
  len r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Nat.le_of_lt (BitVec.isLt _)
    · have := hp.wS; simp only [scrR]; omega

omit hp in
theorem EW.words (h : EW s t) : ∀ k ∈ encKs, word t.mem (fb s) (8 * k) = encW s k := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  intro k hk
  rw [R.fr k (encKs_lt k hk)]
  exact hW k (encKs_iff hk)

omit hp in
theorem EWM.ew {src srcLen dst dstLen : Nat} (h : EWM s t src srcLen dst dstLen) : EW s t :=
  let ⟨V, W, R, hW, _⟩ := h.rep; ⟨h.he, h.L, V, W, R, hW⟩

end

/-! ## The steps -/

section
variable {Hs : Spec.Mgf1.Hash} {s : State} (hp : EPre Hs s)
include hp

omit hp in
theorem ew_clearEm {t : State} (h : EW s t) : WP isa clearEm t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good clearEm_good (clearEm_ok h.L R)) fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
    ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

theorem ew_copySeed {Hm : Stream} (hl : Hs.len = Hm.D) (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) {t : State}
    (h : EW s t) : WP isa (copySeed Hm) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, w31⟩ := hW.w
  have hsl := hp.hsl; have hk2 := hp.k2; have wSd := hp.wSd
  have hc : ∀ i < Hm.D, (⟨stackArg s 4, Hs.len⟩ : Region).Contains (stackArg s 4 + BitVec.ofNat 64 i) 1 :=
    fun i hi => Offset.contains_base (stackArg s 4) (d := i) (n := 1) (k := Hs.len) (by omega) (by omega)
  exact WP.mono (wp_good (copySeed_good _) (copySeed_ok (H := Hm) h.L R w31 hD hD64
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [h.he.rd, hp.hrd]; simp), hc i hi⟩)
    (fun i hi j hj => ne_of_disjoint hp.d_sd_scr (hc i hi) (Offset.contains_base _
      (by unfold oEm at *; omega) (by unfold oEm at *; omega)))))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

/-- The label, where `hashLabel` finds it. -/
theorem EW.lab {t : State} (h : EW s t) {W : Nat → BitVec 64} (hW : ArgsW s W) :
    LabAt t (fb s) (stackArg s 5) W (stackArg s 0) (stackArg s 1).toNat := by
  obtain ⟨-, -, -, -, -, -, -, w27, w28, -⟩ := hW.w
  have hsl := hp.hsl
  have sS : Region.Sub ⟨stackArg s 5, oRsa⟩ (scrR s) := Region.sub_prefix (by unfold oRsa; omega)
  exact ⟨w27, by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 1).isLt,
    Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.he.rd, hp.hrd]; simp),
    hp.d_lb_scr.sub_right sS, hp.d_stk_lb.sub_left (ret_sub s)⟩

theorem ew_hashLabel {Hm : Hash} (hH : HashOK Hm) (KH : Callees Hm) (mH : MgfLink Hm hH) {t : State}
    (h : EW s t) :
    WP isa (hashLabel Hm.stream oDig) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (hashLabel_good (HGood.of hH KH) oDig)
    (hashLabel_ok hH.stream (Hs := mH.G) mH.hash h.L R (h.lab hp hW) (Or.inl rfl)))
    fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, R3, _, _⟩, sp3, mx3, f3⟩ =>
      ⟨h.he.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3, L3, V3, W, R3, hW⟩

omit hp in
theorem ew_copyLh {Hm : Stream} (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) {t : State} (h : EW s t) :
    WP isa (copyLh Hm) t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (copyLh_good _) (copyLh_ok (H := Hm) h.L R hD hD64))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

theorem ew_putMsg {D : Nat} (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) {t : State} (h : EW s t) :
    WP isa putMsg t (EW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -, -, -, -, -, w29, w30, -⟩ := hW.w
  have hk2 := hp.k2; have hsl := hp.hsl; have wM := hp.wM
  have hmA : ∀ i < (stackArg s 3).toNat, (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Contains
      (stackArg s 2 + BitVec.ofNat 64 i) 1 := fun i hi => Offset.contains_base _ (by omega) (by omega)
  exact WP.mono (wp_good putMsg_good (putMsg_ok h.L R (k := (s.gpr .rcx).toNat) (mLen := (stackArg s 3).toNat)
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w29
    (by omega) hk2 (fun i hi => ⟨_, List.mem_append_left _ (by rw [h.he.rd, hp.hrd]; simp), hmA i hi⟩)
    (fun i hi j hj => ne_of_disjoint hp.d_ms_scr (hmA i hi) (Offset.contains_base _ (by omega) (by omega)))))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, W, R1, hW⟩

omit hp in
theorem ew_dbArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .rcx).toNat) {t : State}
    (h : EW s t) : WP isa (.block (dbArgs Hm)) t fun t' =>
      EWM s t' (oEm + 1) Hm.D (oEm + 1 + Hm.D) ((s.gpr .rcx).toNat - (Hm.D + 1)) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (dbArgs_good _) (dbArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by omega)).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem ew_seedArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .rcx).toNat) {t : State}
    (h : EW s t) : WP isa (.block (seedArgs Hm)) t fun t' =>
      EWM s t' (oEm + 1 + Hm.D) ((s.gpr .rcx).toNat - (Hm.D + 1)) (oEm + 1) Hm.D := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (seedArgs_good _) (seedArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by omega)).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem ew_mgf {Gm : Hash} (hG : HashOK Gm) (KG : Callees Gm) (mG : MgfLink Gm hG) {src srcLen dst dstLen : Nat}
    (hf : MFit src srcLen dst dstLen) {t : State} (h : EWM s t src srcLen dst dstLen) :
    WP isa (mgfXor lay Gm.stream) t (EW s) := by
  obtain ⟨V, W, R, hW, A⟩ := h.rep
  exact WP.mono (wp_good (mgfXor_good (HGood.of hG KG)) (mgfXor_ok hG.stream mG.hash mG.len
    (valid_of_link hG mG) h.L R hf A))
    fun t1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, _⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step rd1 wr1 sp1 (fun r hr _ => cs1 r hr) mx1 f1, L1, V1, W1, R1, fun k hk => by
        rw [hW1 k (by rcases hk with rfl | hk <;> unfold nW frameBytes <;> omega) (by omega) (by omega)]
        exact hW k hk⟩

omit hp in
theorem ew_pubArgs {t : State} (h : EW s t) : WP isa (.block pubArgs) t (EWP s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good pubArgs_good (pubArgs_ok h.L R fun k h1 h2 => hW k (.inr ⟨h1, by omega⟩)))
    fun t1 ⟨⟨L1, k1, R1, hdi, hsi, hdx, hcx, h8, h9⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, fun i hi => by
        rw [R1.rd i rfl (by unfold nW frameBytes; omega)]
        match i, hi with
        | 0, _ => simp [upd, pw]
        | 1, _ => simp [upd, pw]
        | 2, _ => simp [upd, pw]
        | 3, _ => simp [upd, pw], hdi, hsi, hdx, hcx, h8, h9⟩

end

end VG.Proof.RsaOaep.X86_64
