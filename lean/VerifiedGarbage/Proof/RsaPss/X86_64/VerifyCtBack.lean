import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtMid

/-!
# RSASSA-PSS verification on x86-64: `M'` and its hash in two runs

`mHash`, `DB` and the shift by the salt's position into `Y`, the hash of
`M'` over the blocks the longest salt needs (`vnb`), and the comparison:
each constant time from the public words of both runs. The shift's ten
passes and the hash's blocks do not depend on the salt's position.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

variable (H) in
/-- After `mHash`: `rcx` is `Y`. -/
def JC8 (s t : State) : Prop := JM H (X7 H) s t ∧ t.gpr .rcx = off (stackArg s 3) oY

variable (H) in
/-- Before pass `j` of the shift. -/
def JS (j : Nat) (s t : State) : Prop :=
  VS H s t KM [] (fun V W => X7 H s V W ∧ W 46 = BitVec.ofNat 64 (2 ^ j) ∧ W 44 = BitVec.ofNat 64 (10 - j) ∧
    ∃ x, W 45 = BitVec.ofNat 64 x ∧ x < 2 ^ 64) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

variable (H) in
/-- After `nbm`. -/
def JN (s t : State) : Prop := VS H s t (KM ++ [28]) [] (X7 H s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

variable (H) in
/-- At the end. -/
def JR (s t : State) : Prop := VS H s t [] [] fun _ _ => True

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH in
theorem cyd_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt lk.G (JM H (X7 H)))) (.seq clearY (copyDigest H)) (Two (VAt lk.G (JC8 H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwo (G := lk.G) (H := H) [21, 37] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hD : lk.G.len = H.D := lk.len
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ => ?_)
  refine WP.mono (copyDigest_ok hH L1 R1 (p := s.gpr .r8) (hw 37 (by decide)) hcx1
    (fun i hi => ⟨⟨s.gpr .r8, lk.G.len⟩, List.mem_append_left _ (by rw [k1.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega) (by omega))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega))) fun u2 ⟨L2, k2, R2⟩ =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx, k2.2.1.trans (k1.2.1.trans hrd), hok⟩,
      (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem copyDb_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt G (JC8 H))) (copyDb H) (Two (VAt G (JM H (X7 H)))) := by
  obtain ⟨_, hc⟩ := hc.copyDb
  refine two_post (vtwo (G := G) (H := H) [23, 24] [.rcx] (fun a => [(.rcx, off (stackArg a 3) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg3]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have := vlo_le s
  exact WP.mono (copyDb_ok v.L R (e := oEm + vlo s) (db := vdb H.D s) (hw 23 (by decide)) (hw 24 (by decide)) hcx
    (by unfold vdb; omega) (by unfold vdb veml oEm oY; omega) (by unfold vdb veml; omega)) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx, k'.2.1.trans hrd, hok⟩

/-- `shift`'s first slots. -/
theorem shiftPro_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pos : Nat} (hpos : W 34 = BitVec.ofNat 64 pos) :
    WP isa (.block shiftPro) u fun v => Lay v F S ∧ Keep [.rax] u v ∧
      Rep v.mem F S V (upd (upd (upd W 45 (BitVec.ofNat 64 (pos + 1))) 46 (BitVec.ofNat 64 1)) 44
        (BitVec.ofNat 64 10)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 45) (by decide) (BitVec.ofNat 64 (pos + 1))
  rw [show off F (8 * 45) = off F sA from rfl] at R1
  have R2 := R1.wf G' (k := 46) (by decide) (BitVec.ofNat 64 1)
  rw [show off F (8 * 46) = off F sD from rfl] at R2
  have R3 := R2.wf G' (k := 44) (by decide) (BitVec.ofNat 64 10)
  rw [show off F (8 * 44) = off F sJ from rfl] at R3
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (pos + 1))).writeW
      (off F sD) (BitVec.ofNat 64 1)).writeW (off F sJ) (BitVec.ofNat 64 10)) ?_ rfl) fun v ⟨hm, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R3) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R3⟩
  xrun [shiftPro, ea_sp, L.rsp, L.ld (d := sPos) (by decide), R.rd (d := sPos) 34 rfl (by decide), hpos,
    L.st (d := sA) (by decide), L.st (d := sD) (by decide), L.st (d := sJ) (by decide), ofNat_add_lit]
  rfl

theorem shiftPro_ct : RelCT isa (Two (VAt G (JM H (X7 H)))) (.block shiftPro) (Two (VAt G (JS H 0))) := by
  obtain ⟨_, hc⟩ := vFixed.shiftPro
  refine two_post (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, h34⟩ := v.W
  have hk2 := S.ps.k2
  have := vlo_le s
  have hp1 : pos + 1 < 2 ^ 64 := by unfold vdb veml at hpos; omega
  exact WP.mono (shiftPro_ok v.L R h34) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩, by simp [upd], by simp [upd], pos + 1, by simp [upd], hp1⟩,
      k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two fun (p : State × Nat) t => p.2 < 10 ∧ VAt G (JS H p.2) p.1 t)
      (.seq (shiftPass H) (.block nextPass)) fun _ _ => True := by
  obtain ⟨_, hs⟩ := hc.shiftPass
  obtain ⟨_, hn⟩ := vFixed.nextPass
  refine RelCT.seq (two_post (Ψ := fun p t => VAt G (JS H p.2) p.1 t)
    (vtwoX (G := G) (H := H) Prod.fst [21, 24] (fun p => [(46, BitVec.ofNat 64 (2 ^ p.2))]) [46] [] (fun _ => [])
      (fun p t ⟨_, s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ ⟨_, h46, _⟩ q hq => by rw [List.mem_singleton.mp hq]; exact h46⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hs) fun p t ⟨_, s, S, ⟨v, hrd, hok⟩⟩ => ?_)
    (vtwoX (G := G) (H := H) Prod.fst [] (fun _ => []) [] [] (fun _ => [])
      (fun p t ⟨s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ _ q hq => by cases hq⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hn)
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have := vlo_le s
  have hpp : 2 ^ p.2 ≤ 512 := by
    calc 2 ^ p.2 ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 512 := rfl
  exact WP.mono (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow (by unfold vdb; omega)
    (by unfold vdb veml oY oRsa; omega)) fun u ⟨L', k', R'⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw ⟨hx, h46, h44, x, h45, hxl⟩, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_wp {a : State} {j : Nat} {t : State} (hj : j < 10) (h : VAt G (JS H j) a t) :
    WP isa (.seq (shiftPass H) (.block nextPass)) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < 10)) ∧ (j + 1 < 10 → VAt G (JS H (j + 1)) a t') ∧
      (j + 1 = 10 → VAt G (JM H (X7 H)) a t') := by
  obtain ⟨s, S, v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have := vlo_le s
  have hpp : 2 ^ j ≤ 512 := by
    calc 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 512 := rfl
  refine WP.seq (WP.mono (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega) (by unfold vdb veml oY oRsa; omega)) fun u ⟨Lu, ku, Ru⟩ => ?_)
  refine WP.mono (nextPass_ok Lu Ru h45 h46 h44 hxl (by omega) (by omega)) fun y ⟨Ly, ky, Ry, hzy⟩ => ?_
  obtain ⟨pos, hpos, h27, h34⟩ := hx
  have hw' := km_upd (j := 44) (km_upd (j := 46) (km_upd (j := 45) hw (by decide) (BitVec.ofNat 64 (x / 2)))
    (by decide) (BitVec.ofNat 64 (2 * 2 ^ j))) (by decide) (BitVec.ofNat 64 (10 - j - 1))
  have hX : X7 H s (shV V (decide (x % 2 = 1)) (2 ^ j) (oY + 8 + H.D) (vdb H.D s))
      (upd (upd (upd W 45 (BitVec.ofNat 64 (x / 2))) 46 (BitVec.ofNat 64 (2 * 2 ^ j))) 44
        (BitVec.ofNat 64 (10 - j - 1))) := ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩
  have hwr : y.wr = t.wr := ky.2.2.trans ku.2.2
  have hrd' : y.rd = s.rd := ky.2.1.trans (ku.2.1.trans hrd)
  refine ⟨eval_ne_cnt hj (by rw [hzy]; simp only [Option.some.injEq, decide_eq_decide]; omega), fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' ⟨hX, by simp [upd, Nat.pow_succ, Nat.mul_comm], by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; congr 1,
      x / 2, by simp [upd], by have := Nat.div_le_self x 2; omega⟩, hrd', hok⟩, fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' hX, hrd', hok⟩⟩

include hH in
theorem shift_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt G (JM H (X7 H)))) (shift H) (Two (VAt G (JM H (X7 H)))) := by
  rw [shift_eq]
  exact RelCT.seq shiftPro_ct ((two_loop (Φ := fun a j t => VAt G (JS H j) a t) (fun _ => 10) (pass_ct hH hc)
    fun a j t hj h => pass_wp hH hj h).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨by decide, h₁⟩, by decide, h₂⟩)
    fun _ _ h => h)

include hH in
theorem verifyNb_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt G (JM H (X7 H)))) (.block (verifyNb H)) (Two (VAt G (JN H))) := by
  obtain ⟨_, hc⟩ := hc.verifyNb
  refine two_post (vtwo (G := G) (H := H) [24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  exact WP.mono (verifyNb_ok hH v.L R (db := vdb H.D s) (hw 24 (by decide)) (by unfold vdb veml; omega))
    fun u ⟨L', k', R'⟩ => ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      rcases List.mem_append.mp hk with hk | hk
      · exact km_upd hw (by decide) _ k hk
      · rw [List.mem_singleton.mp hk]; simp [upd, vw, vnb])
      (by obtain ⟨pos, hpos, h27, h34⟩ := hx; exact ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩),
      k'.2.1.trans hrd, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def hashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 3, a.wr, vnb H a⟩

include hH in
theorem jn_he {a t : State} (h : VAt G (JN H) a t) : HE H 1 (hashA H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb H.D a + (7 + H.D + H.P.L)) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb H.D a + (7 + H.D + H.P.L)) H.P.B
  have hdb : vdb H.D a ≤ 1024 := by unfold vdb veml; omega
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [hashA, vnb]; rw [Nat.succ_mul]; omega⟩,
    (vs_pub S v).sub (fun p hp => ?_) (fun _ h => h) fun _ _ ⟨pos, hpos, h27, _⟩ =>
      ⟨vdb H.D s - pos - 1 + (8 + H.D), h27, ?_⟩⟩
  · simp only [hws, hashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [pw, KM, vw]
  · simp only [hashA, vnb]; rw [S.vdb] at hpos ⊢; rw [Nat.succ_mul]; omega

include hH K in
theorem mhash_ct (hc : HashChecks H.P H.D 1) :
    RelCT isa (Two (VAt G (JN H))) (ctHash H) (Two (VAt G (JT H))) := by
  refine two_post (two_map (hashA H) (fun a t h => jn_he hH h) (ctHash_ct hH K 1 hc (fixedChecks (.inl rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, _⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb H.D s + (7 + H.D + H.P.L)) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb H.D s + (7 + H.D + H.P.L)) H.P.B
  have hdb : vdb H.D s ≤ 1024 := by unfold vdb veml; omega
  exact WP.mono (ctHash_gen hH K v.L R h27 (hw 28 (by simp)) (by unfold vnb; rw [Nat.succ_mul]; omega)
    (by unfold vnb; rw [Nat.succ_mul]; omega)) fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (km_ne hk (by decide))
      (km_ne hk (by decide))).trans (hw k (List.mem_append_left _ hk)), trivial⟩, fun _ hp => by cases hp⟩,
      rd'.trans hrd, hok⟩

include hH in
theorem cmpH_ct (hc : VerifyChecks H.P H.D) :
    RelCT isa (Two (VAt G (JT H))) (cmpH H) (Two (VAt G (JR H))) := by
  obtain ⟨_, hc⟩ := hc.cmpH
  refine two_post (vtwo (G := G) (H := H) [21, 23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have := vlo_le s
  exact WP.mono (cmpH_ok hH v.L R (e := oEm + vlo s) (db := vdb H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    (by unfold vdb veml oEm oRsa; omega)) fun u ⟨k', hm', _⟩ =>
    ⟨s, S, (v.keep k' hm' (by decide) (fun _ hp => by cases hp)).sub (fun _ hk => by cases hk) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86_64
