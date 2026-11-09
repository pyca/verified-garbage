module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtMid
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFixed
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# RSASSA-PSS verification on x86-64: `M'` and its hash in two runs

`mHash`, `DB` and the shift by the salt's position into `Y`, the hash of
`M'` over the blocks the longest salt needs (`vnb`), and the comparison:
each constant time from the public words of both runs. The shift's ten
passes and the hash's blocks do not depend on the salt's position.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- After `mHash`: `rcx` is `Y`. -/
def JC8 (H : Hash) (s t : State) : Prop := JM H (X7 H) s t ∧ t.gpr .rcx = off (stackArg s 0) oY

/-- Before pass `j` of the shift. -/
def JS (H : Hash) (j : Nat) (s t : State) : Prop :=
  VS H s t KM [] (fun V W => X7 H s V W ∧ W 46 = BitVec.ofNat 64 (2 ^ j) ∧ W 44 = BitVec.ofNat 64 (10 - j) ∧
    ∃ x, W 45 = BitVec.ofNat 64 x ∧ x < 2 ^ 64) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- After `nbm`. -/
def JN (H : Hash) (s t : State) : Prop := VS H s t (KM ++ [28]) [] (X7 H s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- At the end. -/
def JR (H : Hash) (s t : State) : Prop := VS H s t [] [] fun _ _ => True

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

include hH in
theorem cyd_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.seq clearY (copyDigest T.H)) (Two (VAt T (JC8 T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwo (T := T) (H := T.H) [21, 37] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ sy1 => ?_)
  refine X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := s.gpr .rdi) (hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, hrd]
      exact ⟨⟨s.gpr .rdi, T.H.D⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith))) fun u2 ⟨L2, k2, R2⟩ sy2 =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx (sy2.trans sy1), k2.2.1.trans (k1.2.1.trans hrd), hok⟩,
      (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem copyDb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC8 T.H))) (copyDb T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.copyDb
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [.rcx] (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (copyDb_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide)) hcx
    (by unfold vdb; omega_arith) (by unfold vdb veml oEm oY; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx sy, k'.2.1.trans hrd, hok⟩

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

theorem shiftPro_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block shiftPro) (Two (VAt T (JS T.H 0))) := by
  obtain ⟨_, hc⟩ := vFixed.shiftPro
  refine two_post (vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, h34⟩ := v.W
  have hk2 := S.ps.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hp1 : pos + 1 < 2 ^ 64 := by unfold vdb veml at hpos; omega_arith
  exact X86_64.WP.mono_syms (shiftPro_ok v.L R h34) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩, by simp [upd], by simp [upd], pos + 1, by simp [upd], hp1⟩
      sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two fun (p : State × Nat) t => p.2 < 10 ∧ VAt T (JS T.H p.2) p.1 t)
      (.seq (shiftPass T.H) (.block nextPass)) fun _ _ => True := by
  obtain ⟨_, hs⟩ := hc.shiftPass
  obtain ⟨_, hn⟩ := vFixed.nextPass
  refine RelCT.seq (two_post (Ψ := fun p t => VAt T (JS T.H p.2) p.1 t)
    (vtwoX (T := T) (H := T.H) Prod.fst [21, 24] (fun p => [(46, BitVec.ofNat 64 (2 ^ p.2))]) [46] [] (fun _ => [])
      (fun p t ⟨_, s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ ⟨_, h46, _⟩ q hq => by rw [List.mem_singleton.mp hq]; exact h46⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hs) fun p t ⟨_, s, S, ⟨v, hrd, hok⟩⟩ => ?_)
    (vtwoX (T := T) (H := T.H) Prod.fst [] (fun _ => []) [] [] (fun _ => [])
      (fun p t ⟨s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ _ q hq => by cases hq⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hn)
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ p.2 ≤ 512 := by
    calc 2 ^ p.2 ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  exact X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw ⟨hx, h46, h44, x, h45, hxl⟩ sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_wp {a : State} {j : Nat} {t : State} (hj : j < 10) (h : VAt T (JS T.H j) a t) :
    WP isa (.seq (shiftPass T.H) (.block nextPass)) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < 10)) ∧ (j + 1 < 10 → VAt T (JS T.H (j + 1)) a t') ∧
      (j + 1 = 10 → VAt T (JM T.H (X7 T.H)) a t') := by
  obtain ⟨s, S, v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ j ≤ 512 := by
    calc 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  refine WP.seq (X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨Lu, ku, Ru⟩ syu => ?_)
  refine X86_64.WP.mono_syms (nextPass_ok Lu Ru h45 h46 h44 hxl (by omega_arith) (by omega_arith))
    fun y ⟨Ly, ky, Ry, hzy⟩ syy => ?_
  obtain ⟨pos, hpos, h27, h34⟩ := hx
  have hw' := km_upd (j := 44) (km_upd (j := 46) (km_upd (j := 45) hw (by decide) (BitVec.ofNat 64 (x / 2)))
    (by decide) (BitVec.ofNat 64 (2 * 2 ^ j))) (by decide) (BitVec.ofNat 64 (10 - j - 1))
  have hX : X7 T.H s (shV V (decide (x % 2 = 1)) (2 ^ j) (oY + 8 + T.H.D) (vdb T.H.D s))
      (upd (upd (upd W 45 (BitVec.ofNat 64 (x / 2))) 46 (BitVec.ofNat 64 (2 * 2 ^ j))) 44
        (BitVec.ofNat 64 (10 - j - 1))) := ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩
  have hwr : y.wr = t.wr := ky.2.2.trans ku.2.2
  have hrd' : y.rd = s.rd := ky.2.1.trans (ku.2.1.trans hrd)
  refine ⟨eval_ne_cnt hj (by rw [hzy]; simp only [Option.some.injEq, decide_eq_decide]; omega_arith), fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' ⟨hX, by simp [upd, Nat.pow_succ, Nat.mul_comm], by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; congr 1,
      x / 2, by simp [upd], by have := Nat.div_le_self x 2; omega_arith⟩ (syy.trans syu), hrd', hok⟩, fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' hX (syy.trans syu), hrd', hok⟩⟩

include hH in
theorem shift_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (shift T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  rw [shift_eq]
  exact RelCT.seq shiftPro_ct ((two_loop (Φ := fun a j t => VAt T (JS T.H j) a t) (fun _ => 10) (pass_ct hH hc)
    fun a j t hj h => pass_wp hH hj h).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨by decide, h₁⟩, by decide, h₂⟩)
    fun _ _ h => h)

include hH in
theorem verifyNb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block (verifyNb T.H)) (Two (VAt T (JN T.H))) := by
  obtain ⟨_, hc⟩ := hc.verifyNb
  refine two_post (vtwo (T := T) (H := T.H) [24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  exact X86_64.WP.mono_syms (verifyNb_ok hH v.L R (db := vdb T.H.D s) (hw 24 (by decide))
    (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      rcases List.mem_append.mp hk with hk | hk
      · exact km_upd hw (by decide) _ k hk
      · rw [List.mem_singleton.mp hk]; simp [upd, vw, vnb])
      (by obtain ⟨pos, hpos, h27, h34⟩ := hx; exact ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩) sy,
      k'.2.1.trans hrd, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def hashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, vnb H a, a.syms⟩

include hH in
theorem jn_he {a t : State} (h : VAt T (JN T.H) a t) : HE T.H T.dn T.f 1 (hashA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D a + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D a + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D a ≤ 1024 := by unfold vdb veml; omega_arith
  have tb := S.pa.tabs
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [hashA, vnb]; rw [Nat.succ_mul]; omega_arith⟩,
    (vs_pub S v).sub (fun p hp => ?_) (fun _ h => h) (fun _ _ ⟨pos, hpos, h27, _⟩ =>
      ⟨vdb T.H.D s - pos - 1 + (8 + T.H.D), h27, ?_⟩), S.syH.tr v.sy⟩
  · simp only [hws, hashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · simp [pw, KM, vw]
    · simp [pw, KM, vw]
    · rw [← tb.h0]; exact List.mem_map.mpr ⟨8, by decide, rfl⟩
    · rw [← tb.h3]; exact List.mem_map.mpr ⟨9, by decide, rfl⟩
    · rw [← tb.h4]; exact List.mem_map.mpr ⟨10, by decide, rfl⟩
  · simp only [hashA, vnb]; rw [S.vdb] at hpos ⊢; rw [Nat.succ_mul]; omega_arith

include hH K hdk in
theorem mhash_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JN T.H))) (ctHash T.f T.H) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (hashA T.H) (fun a t h => jn_he hH h)
    (ctHash_ct hH K hdk 1 hc (fixedChecks (.inl rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, _⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D s + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D s + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D s ≤ 1024 := by unfold vdb veml; omega_arith
  exact X86_64.WP.mono_syms (ctHash_gen hH K v.L R h27 (hw 28 (by simp))
    (by unfold vnb; rw [Nat.succ_mul]; omega_arith) (by unfold vnb; rw [Nat.succ_mul]; omega_arith)
    (vs_ht S.ps v hw) hdk) fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (km_ne hk (by decide))
      (km_ne hk (by decide))).trans (hw k (List.mem_append_left _ hk)), trivial⟩, (fun _ hp => by cases hp),
      sy.trans v.sy⟩, rd'.trans hrd, hok⟩

include hH in
theorem cmpH_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (cmpH T.H) (Two (VAt T (JR T.H))) := by
  obtain ⟨_, hc⟩ := hc.cmpH
  refine two_post (vtwo (T := T) (H := T.H) [21, 23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (cmpH_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', _⟩ sy =>
    ⟨s, S, (v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy).sub (fun _ hk => by cases hk) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86_64.Chk
