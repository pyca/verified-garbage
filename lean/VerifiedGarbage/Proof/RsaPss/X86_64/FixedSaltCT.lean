module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBack
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp
import VerifiedGarbage.Proof.Framework.Offset

/-! The fixed-salt tail leaks only the requested, public salt length. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {extra : State → State → Prop}

def fixedNb (H : Hash) (s : State) : Nat :=
  (8 + H.D + (stackArg s 1).toNat + H.P.L) / H.P.B + 1

def JFixed (H : Hash) (s t : State) : Prop :=
  JM H (X7 H) s t ∧ (stackArg s 1).toNat < vdb H.D s

def JFixedN (H : Hash) (s t : State) : Prop :=
  VS H s t KM [] (fun _ W => W 27 = BitVec.ofNat 64 (8 + H.D + (stackArg s 1).toNat) ∧
    W 28 = BitVec.ofNat 64 (fixedNb H s)) ∧ t.rd = s.rd ∧
    H.D + 2 ≤ veml s ∧ (stackArg s 1).toNat < vdb H.D s

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

/-- After `fixedHead`: `rcx` = `Y`. -/
def JFixedC (H : Hash) (s t : State) : Prop :=
  JFixedN H s t ∧ t.gpr .rcx = off (stackArg s 3) oY

include hH in
theorem fixedHead_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JFixed H))) (fixedHead H)
      (Two (VAt (extra := extra) lk.G (JFixedC H))) := by
  obtain ⟨_, hc⟩ := hc.fixedHead
  refine two_post (vtwo (G := lk.G) (H := H) [21, 36, 37] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vs ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hfit⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hD : lk.G.len = H.D := lk.len
  have hDN := hH.hDN
  have hN := hH.N_le
  have hk2 := S.ps.k2
  have hB0 := hH.B_pos
  have hL := hH.dims.L
  have hBl := hH.B_le
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg s 1).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg s 1).toNat + H.P.L) H.P.B
  have hnb : fixedNb H s * H.P.B ≤ 2048 := by
    unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hfit; omega
  unfold fixedHead seqs seqs
  refine WP.seq (WP.mono (hashSaltLen_ok hH v.L R (k := 36) (by decide)
    (show W 36 = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hfit; omega)) fun u0 ⟨L0, k0, R0⟩ => ?_)
  refine WP.seq (WP.mono (clearNb_ok hH L0 R0 (nbm := fixedNb H s) (by simp [upd, fixedNb])
    (Nat.succ_pos _) hnb) fun u1 ⟨L1, k1, hcx1, R1⟩ => ?_)
  refine WP.mono (copyDigest_ok hH L1 R1 (p := s.gpr .r8) (by simp [upd]; exact hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, k0.2.1, hrd]
      exact hp.hrd.left _ _ ⟨⟨s.gpr .r8, lk.G.len⟩, by simp,
        Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega) (by omega))
      rwa [k1.2.2, k0.2.2, v.wr]) (by unfold oY oRsa; omega))) fun u2 ⟨L2, k2, R2⟩ => ?_
  exact ⟨s, S, ⟨v.next L2 (k2.2.2.trans (k1.2.2.trans k0.2.2)) R2
    (km_upd (km_upd hw (by decide) _) (by decide) _) ⟨by simp [upd], by simp [upd, fixedNb]⟩,
    k2.2.1.trans (k1.2.1.trans (k0.2.1.trans hrd)), hok, hfit⟩, (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem fixedCopy_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JFixedC H))) (copyFixedSalt H)
      (Two (VAt (extra := extra) G (JFixedN H))) := by
  obtain ⟨_, hc⟩ := hc.copyFixedSalt
  refine two_post (vtwo (G := G) (H := H) [23, 24, 36] [.rcx]
    (fun a => [(.rcx, off (stackArg a 3) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _
      (fun p hp => by rw [List.mem_singleton.mp hp, ← S.arg3]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok, hf⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hlo := vlo_le s
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.mono (copyFixedSalt_ok hH v.L R (e := oEm + vlo s) (db := vdb H.D s)
    (hw 23 (by decide)) (hw 24 (by decide))
    (show W 36 = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hw 36 (by decide)]; simp [vw]) hf
    (by unfold vdb veml oEm oY; omega) (by unfold vdb veml at hf; omega) hcx)
    fun u ⟨L, k, R⟩ => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem padSalt_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JFixedN H))) (.block (padSalt H))
      (Two (VAt (extra := extra) G (JFixedN H))) := by
  obtain ⟨_, hc⟩ := hc.padSalt
  refine two_post (vtwo (G := G) (H := H) [21, 36] [] (fun _ => [])
    (fun a t ⟨s, S, v, hrd, hok, _⟩ => jm_vs (X := fun _ _ _ => True) ⟨s, S, v.sub (fun _ h => h) [] (fun _ h => by cases h)
      (fun _ _ _ => trivial), hrd, hok⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.mono (padSalt_ok v.L R (sl := (stackArg s 1).toNat)
    (show W 36 = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hf; omega)) fun u ⟨L, k, R⟩ => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem fixedSaltPrefix_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JFixed H))) (fixedSaltPrefix H)
      (Two (VAt (extra := extra) lk.G (JFixedN H))) := by
  unfold fixedSaltPrefix seqs seqs
  exact (fixedHead_ct hH lk hc).seq ((fixedCopy_ct hH hc).seq (padSalt_ct hH hc))

/-! ## `fixedHash` -/

include hH in
theorem lenLast_ct (hc : VerifyChecks H.P H.D) : RelCT isa (Two (HF H 1)) (lenLast H) (Two (HF H 1)) := by
  obtain ⟨_, hp⟩ := hc.lenLast
  refine two_post (two_pub 1 [21, 28] [] HA.F HA.S HA.rest hws (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.W
  obtain ⟨-, h1, hnb⟩ := h.1
  exact WP.mono (lenLast_ok hH h.2.L R (len := (List.range H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) (hws_w hw).2 h1 hnb) fun u ⟨Lu, ku, Ru⟩ =>
    ⟨h.1, h.2.next Lu ku.2.2 Ru hw ⟨fb, hf, hfb⟩⟩

include hH in
theorem body2_wp {a : HA} {j : Nat} {t : State} (hj : j < a.nbm) (h : HL H 1 a j t) :
    WP isa (seqs [.block (compArgs H), .call H.compN H.compC, .block nextBlock]) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < a.nbm)) ∧ (j + 1 < a.nbm → HL H 1 a (j + 1) t') ∧
      (j + 1 = a.nbm → HD H 1 a t') := by
  have hbB := hb_bound (H := H) 1 (p := (a, j)) ⟨hj, h⟩
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.W
  obtain ⟨w21, w28, w29⟩ := hl_w hw
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2
  refine WP.seq_assoc (WP.seq (WP.mono (compCall_ok hH h.2.L R hbB w29)
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ => ?_))
  refine WP.mono (nextBlock_ok Lv Rv (b := j) (nbm := a.nbm) w29 w28 (by omega) (by omega))
    fun u' ⟨hz, Lu', hk', Ru'⟩ => ⟨eval_ne_cnt hj hz, fun _ => ⟨h.1, Lu', hk'.2.2.trans
      (hwrv.trans h.2.wr), ⟨_, _, Ru', fun q hq => ?_, fb, by simp [upd, hf], hfb⟩, fun _ hp => by cases hp⟩,
      fun _ => ⟨h.1, Lu', hk'.2.2.trans (hwrv.trans h.2.wr),
        ⟨_, _, Ru', fun q hq => by rw [List.mem_singleton.mp hq]; simp [upd, w21], trivial⟩, fun _ hp => by cases hp⟩⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq => hw q (List.mem_append_left _ hq)) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

include hH in
theorem compAll_ct (hc : HashChecks H.P H.D 1) (hfx : FixedChecks 1) :
    RelCT isa (Two (HF H 1)) (compAll H) (Two (HD H 1)) := by
  refine RelCT.seq (startB_ct 1 hfx) (two_loop (Φ := HL H 1) HA.nbm ?_ fun a j t hj h => body2_wp hH hj h)
  simp only [seqs]
  exact RelCT.assoc (RelCT.seq (compA_ct hH 1 hc) (nextB_ct 1 hfx))

theorem digestSt_ct (hc : HashChecks H.P H.D 1) :
    RelCT isa (Two (HD H 1)) (.block (digestAt H oSt)) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hc.digestState
  exact two_pub 1 [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => []) (fun a t h => ⟨_, h.2⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH K in
theorem fixedHash_ct (hc : HashChecks H.P H.D 1) (hv : VerifyChecks H.P H.D) (hfx : FixedChecks 1) :
    RelCT isa (Two (HE H 1)) (fixedHash H) fun _ _ => True := by
  unfold fixedHash seqs seqs seqs seqs
  exact (ctInit_ct hH K 1 hfx).seq ((lenField_ct hH 1 hc).seq ((lenLast_ct hH hv).seq
    ((compAll_ct hH hc hfx).seq (digestSt_ct hc))))

def fixedHashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 3, a.wr, fixedNb H a⟩

include hH in
theorem fixedN_he {a t : State} (h : VAt (extra := extra) G (JFixedN H) a t) :
    HE H 1 (fixedHashA H a) t := by
  obtain ⟨s, S, v, _, hok, hfit⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hf : (stackArg a 1).toNat < vdb H.D a := by rwa [S.arg1, S.vdb] at hfit
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg a 1).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg a 1).toNat + H.P.L) H.P.B
  refine ⟨⟨S.rest, Nat.succ_pos _, by
    simp only [fixedHashA, fixedNb]; rw [Nat.succ_mul]; unfold vdb veml at hf; omega⟩, ?_⟩
  obtain ⟨L, wr, ⟨V, W, R, hw, h27, h28⟩, regs⟩ := vs_pub S v
  refine ⟨L, wr, ⟨V, W, R, fun p hp => ?_, 8 + H.D + (stackArg s 1).toNat, h27, ?_⟩, regs⟩
  · simp only [hws, fixedHashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hw (21, stackArg a 3) (by simp [pw, KM, vw])
    · simpa only [fixedNb, S.arg1] using h28
  · simp only [fixedHashA, fixedNb, S.arg1]; rw [Nat.succ_mul]; omega

include hH K in
theorem fixedMhash_ct (hc : HashChecks H.P H.D 1) (hv : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JFixedN H))) (fixedHash H)
      (Two (VAt (extra := extra) G (JT H))) := by
  refine two_post (two_map (fixedHashA H) (fun a t h => fixedN_he hH h)
    (fixedHash_ct hH K hc hv (fixedChecks (.inl rfl)))) fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, h27, h28⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg s 1).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg s 1).toNat + H.P.L) H.P.B
  refine WP.mono (fixedHash_gen hH K v.L R h27 h28 rfl
    (by unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hf; omega))
    fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ => ?_
  exact ⟨s, S, v.next L' wr' R' (fun k hk =>
    (hW' k (km_lt hk) (km_ne hk (by decide)) (km_ne hk (by decide))).trans (hw k hk)) trivial,
    rd'.trans hrd, hok⟩

include hH K in
theorem fixedSaltBack_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JFixed H))) (fixedSaltBack H)
      (Two (VAt (extra := extra) lk.G (JR H))) :=
  (fixedSaltPrefix_ct hH lk hc.verify).seq
    ((fixedMhash_ct hH K hc.hash1 hc.verify).seq (cmpH_ct hH hc.verify))

end VG.Proof.RsaPss.X86_64
