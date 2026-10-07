import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBack
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack

/-! The fixed-salt tail leaks only the requested, public salt length. -/
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

def JFixed8 (H : Hash) (s t : State) : Prop :=
  JC8 H s t ∧ (stackArg s 1).toNat < vdb H.D s

include hH in
theorem fixedCyd_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JFixed H))) (.seq clearY (copyDigest H))
      (Two (VAt (extra := extra) lk.G (JFixed8 H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwo (G := lk.G) (H := H) [21, 37] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vs ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hfit⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hD : lk.G.len = H.D := lk.len
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ => ?_)
  refine WP.mono (copyDigest_ok hH L1 R1 (p := s.gpr .r8) (hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, hrd]
      exact hp.hrd.left _ _ ⟨⟨s.gpr .r8, lk.G.len⟩, by simp,
        Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega) (by omega))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega))) fun u2 ⟨L2, k2, R2⟩ => ?_
  exact ⟨s, S, ⟨⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx,
    k2.2.1.trans (k1.2.1.trans hrd), hok⟩, (k2.gpr (by decide)).trans hcx1⟩, hfit⟩

include hH in
theorem fixedCopy_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JFixed8 H))) (copyFixedSalt H)
      (Two (VAt (extra := extra) G (JFixed H))) := by
  obtain ⟨_, hc⟩ := hc.copyFixedSalt
  refine two_post (vtwo (G := G) (H := H) [23, 24, 36] [.rcx]
    (fun a => [(.rcx, off (stackArg a 3) oY)])
    (fun a t ⟨s, S, ⟨⟨v, _⟩, hcx⟩, _⟩ => ⟨s, _, S, v.sub (by decide) _
      (fun p hp => by rw [List.mem_singleton.mp hp, ← S.arg3]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨⟨v, hrd, hok⟩, hcx⟩, hf⟩ => ?_
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
  exact ⟨s, S, ⟨v.next L k.2.2 R hw hx, k.2.1.trans hrd, hok⟩, hf⟩

include hH in
theorem fixedLen_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) G (JFixed H))) (.block (hashSaltLen H 36))
      (Two (VAt (extra := extra) G (JFixedN H))) := by
  obtain ⟨_, hc⟩ := hc.fixedSaltLen
  refine two_post (vtwo (G := G) (H := H) [36] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vs ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hf⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.mono (hashSaltLen_ok hH v.L R (k := 36) (by decide)
    (show W 36 = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hf; omega)) fun u ⟨L, k, R⟩ => ?_
  exact ⟨s, S, v.next L k.2.2 R (km_upd (km_upd hw (by decide) _) (by decide) _)
    ⟨by simp [upd], by simp [upd, fixedNb]⟩, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem fixedSaltPrefix_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt (extra := extra) lk.G (JFixed H))) (fixedSaltPrefix H)
      (Two (VAt (extra := extra) lk.G (JFixedN H))) :=
  RelCT.assoc ((fixedCyd_ct hH lk hc).seq ((fixedCopy_ct hH hc).seq (fixedLen_ct hH hc)))

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
theorem fixedMhash_ct (hc : HashChecks H.P H.D 1) :
    RelCT isa (Two (VAt (extra := extra) G (JFixedN H))) (ctHash H)
      (Two (VAt (extra := extra) G (JT H))) := by
  refine two_post (two_map (fixedHashA H) (fun a t h => fixedN_he hH h)
    (ctHash_ct hH K 1 hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, h27, h28⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + (stackArg s 1).toNat + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + (stackArg s 1).toNat + H.P.L) H.P.B
  refine WP.mono (ctHash_gen hH K v.L R h27 h28 (by unfold fixedNb; rw [Nat.succ_mul]; omega)
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
    ((fixedMhash_ct hH K hc.hash1).seq (cmpH_ct hH hc.verify))

end VG.Proof.RsaPss.X86_64
