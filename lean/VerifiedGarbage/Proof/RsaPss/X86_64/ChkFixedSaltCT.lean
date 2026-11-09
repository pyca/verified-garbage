module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtBack
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! The fixed-salt tail leaks only the requested, public salt length. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

def fixedNb (H : Hash) (s : State) : Nat :=
  (8 + H.D + (s.gpr .r8).toNat + H.P.L) / H.P.B + 1

def JFixed (H : Hash) (s t : State) : Prop :=
  JM H (X7 H) s t ∧ (s.gpr .r8).toNat < vdb H.D s

def JFixedN (H : Hash) (s t : State) : Prop :=
  VS H s t KM [] (fun _ W => W 27 = BitVec.ofNat 64 (8 + H.D + (s.gpr .r8).toNat) ∧
    W 28 = BitVec.ofNat 64 (fixedNb H s)) ∧ t.rd = s.rd ∧
    H.D + 2 ≤ veml s ∧ (s.gpr .r8).toNat < vdb H.D s

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

/-- After `fixedHead`: `rcx` = `Y`. -/
def JFixedC (H : Hash) (s t : State) : Prop :=
  JFixedN H s t ∧ t.gpr .rcx = off (stackArg s 0) oY

include hH in
theorem fixedHead_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedHead T.H)
      (Two (VAt T (JFixedC T.H))) := by
  obtain ⟨_, hc⟩ := hc.fixedHead
  refine two_post (vtwo (T := T) (H := T.H) [21, 36, 37] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vs ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hfit⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  have hk2 := S.ps.k2
  have hB0 := hH.B_pos
  have hL := hH.dims.L
  have hBl := hH.B_le
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) T.H.P.B
  have hnb : fixedNb T.H s * T.H.P.B ≤ 2048 := by
    unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hfit; omega_arith
  unfold fixedHead seqs seqs
  refine WP.seq (X86_64.WP.mono_syms (hashSaltLen_ok hH v.L R (k := 36) (by decide)
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hfit; omega_arith)) fun u0 ⟨L0, k0, R0⟩ sy0 => ?_)
  refine WP.seq (X86_64.WP.mono_syms (clearNb_ok hH L0 R0 (nbm := fixedNb T.H s) (by simp [upd, fixedNb])
    (Nat.succ_pos _) hnb) fun u1 ⟨L1, k1, hcx1, R1⟩ sy1 => ?_)
  refine X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := s.gpr .rdi) (by simp [upd]; exact hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, k0.2.1, hrd]
      exact ⟨⟨s.gpr .rdi, T.H.D⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, k0.2.2, v.wr]) (by unfold oY oRsa; omega_arith))) fun u2 ⟨L2, k2, R2⟩ sy2 => ?_
  exact ⟨s, S, ⟨v.next L2 (k2.2.2.trans (k1.2.2.trans k0.2.2)) R2
    (km_upd (km_upd hw (by decide) _) (by decide) _) ⟨by simp [upd], by simp [upd, fixedNb]⟩
    (sy2.trans (sy1.trans sy0)), k2.2.1.trans (k1.2.1.trans (k0.2.1.trans hrd)), hok, hfit⟩,
    (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem fixedCopy_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedC T.H))) (copyFixedSalt T.H)
      (Two (VAt T (JFixedN T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyFixedSalt
  refine two_post (vtwo (T := T) (H := T.H) [23, 24, 36] [.rcx]
    (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _
      (fun p hp => by rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok, hf⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hlo := vlo_le s
  have hDN := hH.hDN
  have hN := hH.N_le
  refine X86_64.WP.mono_syms (copyFixedSalt_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s)
    (hw 23 (by decide)) (hw 24 (by decide))
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw]) hf
    (by unfold vdb veml oEm oY; omega_arith) (by unfold vdb veml at hf; omega_arith) hcx)
    fun u ⟨L, k, R⟩ sy => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx sy, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem padSalt_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedN T.H))) (.block (padSalt T.H))
      (Two (VAt T (JFixedN T.H))) := by
  obtain ⟨_, hc⟩ := hc.padSalt
  refine two_post (vtwo (T := T) (H := T.H) [21, 36] [] (fun _ => [])
    (fun a t ⟨s, S, v, hrd, hok, _⟩ => jm_vs (X := fun _ _ _ => True) ⟨s, S, v.sub (fun _ h => h) [] (fun _ h => by cases h)
      (fun _ _ _ => trivial), hrd, hok⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  refine X86_64.WP.mono_syms (padSalt_ok v.L R (sl := (s.gpr .r8).toNat)
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hf; omega_arith)) fun u ⟨L, k, R⟩ sy => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx sy, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem fixedSaltPrefix_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedSaltPrefix T.H)
      (Two (VAt T (JFixedN T.H))) := by
  unfold fixedSaltPrefix seqs seqs
  exact (fixedHead_ct hH hc).seq ((fixedCopy_ct hH hc).seq (padSalt_ct hH hc))

/-! ## `fixedHash` -/

include hH in
theorem lenLast_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (HF T.H T.dn T.f 1)) (lenLast T.H) (Two (HF T.H T.dn T.f 1)) := by
  obtain ⟨_, hp⟩ := hc.lenLast
  refine two_post (two_pub 1 [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws T.H T.dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨-, h1, hnb⟩ := h.1
  exact X86_64.WP.mono_syms (lenLast_ok hH h.2.1.L R (len := (List.range T.H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) (hws_w hw).2.1 h1 hnb) fun u ⟨Lu, ku, Ru⟩ sy =>
    ⟨h.1, h.2.1.next Lu ku.2.2 Ru hw ⟨fb, hf, hfb⟩, h.2.2.tr sy⟩

include hH in
theorem body2_wp {a : HA} {j : Nat} {t : State} (hj : j < a.nbm) (h : HL T.H T.dn T.f 1 a j t) :
    WP isa (seqs [.block (compArgs T.H), scall sCmpH T.f.comp, .block nextBlock]) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < a.nbm)) ∧ (j + 1 < a.nbm → HL T.H T.dn T.f 1 a (j + 1) t') ∧
      (j + 1 = a.nbm → HD T.H T.dn T.f 1 a t') := by
  have hbB := hb_bound (H := T.H) 1 (p := (a, j)) ⟨hj, h⟩
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨w21, w28, w29⟩ := hl_w hw
  have w10 : W 10 = a.sy T.dn := hw (10, a.sy T.dn) (by simp [hws])
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2
  refine WP.seq_assoc (WP.seq (X86_64.WP.mono_syms (compCall_ok hH h.2.1.L R hbB w29
      (hws_ht h.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ sv => ?_))
  refine X86_64.WP.mono_syms (nextBlock_ok Lv Rv (b := j) (nbm := a.nbm) w29 w28 (by omega_arith) (by omega_arith))
    fun u' ⟨hz, Lu', hk', Ru'⟩ su => ⟨eval_ne_cnt hj hz, fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans
      (hwrv.trans h.2.1.wr), ⟨_, _, Ru', fun q hq => ?_, fb, by simp [upd, hf], hfb⟩, fun _ hp => by cases hp⟩,
      (h.2.2.tr sv).tr su⟩,
      fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans (hwrv.trans h.2.1.wr),
        ⟨_, _, Ru', fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> simp [upd, w21, w10], trivial⟩, fun _ hp => by cases hp⟩,
        (h.2.2.tr sv).tr su⟩⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq => hw q (List.mem_append_left _ hq)) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

include hH in
theorem compAll_ct (hc : HashChecks T.H.P T.H.D 1) (hfx : FixedChecks 1) :
    RelCT isa (Two (HF T.H T.dn T.f 1)) (compAll T.f T.H) (Two (HD T.H T.dn T.f 1)) := by
  refine RelCT.seq (startB_ct 1 hfx) (two_loop (Φ := HL T.H T.dn T.f 1) HA.nbm ?_
    fun a j t hj h => body2_wp hH hj h)
  simp only [seqs]
  exact RelCT.assoc (RelCT.seq (compA_ct hH 1 hc hfx) (nextB_ct 1 hfx))

include hH hdk in
theorem digestSt_ct (hfx : FixedChecks 1) :
    RelCT isa (Two (HD T.H T.dn T.f 1)) (digestAt T.f oSt) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hfx.digSt
  have hN := hH.N_le
  unfold digestAt
  refine RelCT.seq (two_post (Ψ := fun a t => DA (H := T.H) a.F a.S oSt t ∧ HD T.H T.dn T.f 1 a t)
    (two_pub 1 [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
      (fun a t h => ⟨_, h.2.1.sub (mem21 (by simp)) (fun _ h => h) fun _ _ x => x⟩)
      (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_)
    (two_scall 1 (s := sDigH) (by decide) HA.F HA.S HA.rest (fun a => a.sy T.dn)
      (fun a t h => ⟨h.1.1, h.2.2.1.wr, h.2.1.1, pub_slot h.2.2.1 (k := 10) rfl (by decide) (by simp),
        h.2.2.2.2.2.2, h.2.2.2.1.fd⟩)
      (hfx.ld _ (.inr (.inr (.inl rfl))))
      (dig_rel hH hdk fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨a.F, a.S, oSt, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))
  have L := h.2.1.L
  exact X86_64.WP.mono_syms (digArgs_ok L (src := oSt) (by decide)) fun u ⟨h1, h2, hm, hk⟩ sy =>
    ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, by unfold oSt oDig; omega_arith⟩,
      h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, h.2.2.tr sy⟩

include hH K hdk in
theorem fixedHash_ct (hc : HashChecks T.H.P T.H.D 1) (hv : VerifyChecks T.H.P T.H.D) (hfx : FixedChecks 1) :
    RelCT isa (Two (HE T.H T.dn T.f 1)) (fixedHash T.f T.H) fun _ _ => True := by
  unfold fixedHash seqs seqs seqs seqs
  exact (ctInit_ct hH K 1 hfx).seq ((lenField_ct hH 1 hc).seq ((lenLast_ct hH hv).seq
    ((compAll_ct hH hc hfx).seq (digestSt_ct hH hdk hfx))))

def fixedHashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, fixedNb H a, a.syms⟩

include hH in
theorem fixedN_he {a t : State} (h : VAt T (JFixedN T.H) a t) :
    HE T.H T.dn T.f 1 (fixedHashA T.H a) t := by
  obtain ⟨s, S, v, _, hok, hfit⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have tb := S.pa.tabs
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by rwa [S.rsl, S.vdb] at hfit
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (a.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (a.gpr .r8).toNat + T.H.P.L) T.H.P.B
  refine ⟨⟨S.rest, Nat.succ_pos _, by
    simp only [fixedHashA, fixedNb]; rw [Nat.succ_mul]; unfold vdb veml at hf; omega_arith⟩, ?_, S.syH.tr v.sy⟩
  obtain ⟨L, wr, ⟨V, W, R, hw, h27, h28⟩, regs⟩ := vs_pub S v
  refine ⟨L, wr, ⟨V, W, R, fun p hp => ?_, 8 + T.H.D + (s.gpr .r8).toNat, h27, ?_⟩, regs⟩
  · simp only [hws, fixedHashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hw (21, stackArg a 0) (by simp [pw, KM, vw])
    · simpa only [fixedNb, S.rsl] using h28
    · exact (pw_w hw (k := 8) (by decide)).trans tb.h0
    · exact (pw_w hw (k := 9) (by decide)).trans tb.h3
    · exact (pw_w hw (k := 10) (by decide)).trans tb.h4
  · simp only [fixedHashA, fixedNb, S.rsl]; rw [Nat.succ_mul]; omega_arith

include hH K hdk in
theorem fixedMhash_ct (hc : HashChecks T.H.P T.H.D 1) (hv : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedN T.H))) (fixedHash T.f T.H)
      (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (fixedHashA T.H) (fun a t h => fixedN_he hH h)
    (fixedHash_ct hH K hdk hc hv (fixedChecks (.inl rfl)))) fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, h27, h28⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) T.H.P.B
  refine X86_64.WP.mono_syms (fixedHash_gen hH K v.L R h27 h28 rfl
    (by unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hf; omega_arith) (vs_ht S.ps v hw) hdk)
    fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ sy => ?_
  exact ⟨s, S, v.next L' wr' R' (fun k hk =>
    (hW' k (km_lt hk) (km_ne hk (by decide)) (km_ne hk (by decide))).trans (hw k hk)) trivial sy,
    rd'.trans hrd, hok⟩

include hH K hdk in
theorem fixedSaltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedSaltBack T.f T.H)
      (Two (VAt T (JR T.H))) :=
  (fixedSaltPrefix_ct hH hc.verify).seq
    ((fixedMhash_ct hH K hdk hc.hash1 hc.verify).seq (cmpH_ct hH hc.verify))

end VG.Proof.RsaPss.X86_64.Chk
