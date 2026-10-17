module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignFixed
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtEnc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed

/-!
# RSASSA-PSS signing on x86-64: the encoding in two runs

`signEnc`'s pieces, each constant time from the public words of both runs:
`DB`'s place and length, the salt's length and so the length and blocks of
`M'`, are public; the digest, the salt and everything derived from them are
not (`signEnc_ctA`). Each piece keeps the memory outside the writable regions
(`Frame`), for the private-key operation after it.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {k g : Nat} {H : Hash}

/-- The public words after the checks. -/
def KS6A : List Nat := [15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 37, 39, 40, 47, 48]

/-- And `DB`'s. -/
def KSMA : List Nat := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 37, 39, 40, 47, 48]

/-- And the length and blocks of `M'`. -/
def KSLA : List Nat := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 37, 39, 40, 47, 48]

theorem ksm_neA {k j : Nat} (h : k ∈ KSMA) (hj : j ∉ KSMA) : k ≠ j := fun e => hj (e ▸ h)

theorem ksm_ltA {k : Nat} (h : k ∈ KSMA) : k < nW := by
  simp only [KSMA, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega_arith

variable (H) in
/-- After the checks: the salt fits, `rax = emLen - hLen - 2`. -/
def SJ6A (s t : State) : Prop :=
  SSA H s t KS6A [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrRA s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (seml s - (H.D + 2)) ∧ t.cf = some (decide (seml s - (H.D + 2) < sslA s)) ∧
    H.D + 2 ≤ seml s

variable (H) in
/-- In the encoding: the public words `ks`. -/
def SEA (ks : List Nat) (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  SSA H s t ks [] (X s) ∧ t.rd = s.rd ∧ Frame (wrRA s) s.mem t.mem ∧ H.D + sslA s + 2 ≤ seml s

/-- `SEA` as a public piece's start. -/
theorem se_ssA {ks : List Nat} {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State}
    (h : SAtA G k g (SEA H ks X) a t) (ks' : List Nat) (hks : ∀ k ∈ ks', k ∈ ks := by decide) :
    ∃ s X', SSibA G k g a s ∧ SSA H s t ks' [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem ksm_updA {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KSMA, W k = swA H s k) {j : Nat} (hj : j ∉ KSMA)
    (v : BitVec 64) : ∀ k ∈ KSMA, upd W j v k = swA H s k := fun k hk => by
  simp only [upd]; rw [ifn (ksm_neA hk hj)]; exact hw k hk

theorem sdb_ctA : RelCT isa (Two fun a t => SAtA G k g (SJ6A H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.dbSlots
  refine two_post (stwoA (G := G) (H := H) [26] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hcf, hok⟩ := h
  have hfit : H.D + sslA s + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega_arith
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  refine WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R (hw 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial, k1.2.1.trans hrd, frame_keepA hp v.wr L.rsp hM f1, hfit⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, swA]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, swA, sdb]
    congr 1; omega_arith
  simp only [upd]; rw [ifn h23, ifn h24]
  exact hw k (by simp only [KSMA, KS6A, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega_arith)

variable (H) in
/-- After `mHash`: `rcx` is `Y`. -/
def SC2A (s t : State) : Prop := SEA H KSMA (fun _ _ _ => True) s t ∧ t.gpr .rcx = off (stackArg s 14) oY

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH in
theorem scyd_ctA (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) (.seq clearY (copyDigest H)) (Two (SAtA lk.G k g (SC2A H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (stwoA (G := lk.G) (H := H) [21, 37] [] (fun _ => []) (fun a t h => se_ssA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hD : lk.G.len = H.D := lk.len
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 8)
    (clearY_ok v.L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ => ?_)
  have hM1 := frame_keepA hp v.wr v.L.rsp hM f1
  refine WP.mono (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 8)
    (copyDigest_ok hH L1 R1 (p := stackArg s 10) (hw 37 (by decide)) hcx1
    (fun i hi => ⟨⟨stackArg s 10, lk.G.len⟩, List.mem_append_left _ (by rw [k1.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.dOdg hp.ddgs hp.dKdg (a := stackArg s 10 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith)))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx, k2.2.1.trans (k1.2.1.trans hrd),
      frame_keepA hp (k1.2.2.trans v.wr) L1.rsp hM1 f2, hok⟩, (k2.gpr (by decide)).trans hcx1⟩

theorem w40A {s : State} {W : Nat → BitVec 64} (h : W 40 = swA H s 40) : W 40 = BitVec.ofNat 64 (sslA s) := by
  rw [h]; show stackArg s 13 = _; rw [sslA, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ssl_leA {s : State} (h : H.D + sslA s + 2 ≤ seml s) (hk : (s.gpr .rcx).toNat ≤ 1024) : sslA s ≤ 1024 := by
  unfold seml at h; omega_arith

include hH in
theorem copySaltY_ctA (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAtA lk.G k g (SC2A H))) (copySaltY H) (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.copySaltY
  refine two_post (stwoA (G := lk.G) (H := H) [39, 40] [.rcx] (fun a => [(.rcx, off (stackArg a 14) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (i := 14) (by decide)]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hM, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have hsl := ssl_leA hok hk2
  have hss : sslA s = (stackArg s 13).toNat := rfl
  have hDN := hH.hDN
  have hN := hH.N_le
  exact WP.mono (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 8)
    (copySaltY_ok hH v.L R (q := stackArg s 12) (sl := sslA s) (hw 39 (by decide)) (w40A (hw 40 (by decide)))
      (by omega_arith) hcx
      (fun i hi => ⟨⟨stackArg s 12, (stackArg s 13).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold sslA at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 12 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold sslA at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold oY oRsa; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx, k'.2.1.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

include hH in
theorem signLen_ctA (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) (.block (signLen H))
      (Two (SAtA G k g (SEA H KSLA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.signLen
  refine two_post (stwoA (G := G) (H := H) [40] [] (fun _ => []) (fun a t h => se_ssA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hsl := ssl_leA hok hp.k2
  exact WP.mono (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 8)
    (signLen_ok hH v.L R (sl := sslA s) (w40A (hw 40 (by decide))) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      by_cases h27 : k = 27
      · subst h27; simp [upd, swA]
      by_cases h28 : k = 28
      · subst h28; simp [upd, swA, snbA]
      simp only [upd]; rw [ifn h28, ifn h27]
      exact hw k (by simp only [KSLA, KSMA, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega_arith)) trivial,
      k'.2.1.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def shashAA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 14, a.wr, snbA H a⟩

include hH in
theorem sl_heA {a t : State} (h : SAtA G k g (SEA H KSLA fun _ _ _ => True) a t) : HE H 2 (shashAA H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hk2 := S.pa.k2
  rw [S.sslA, S.seml] at hok
  have hsl := ssl_leA hok hk2
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + sslA a + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + sslA a + H.P.L) H.P.B
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pubA S v
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [shashAA, snbA]; rw [Nat.succ_mul]; omega_arith⟩,
    L, w, ⟨V, W, R, fun p hp => hw p ?_, 8 + H.D + sslA a, hw (27, BitVec.ofNat 64 (8 + H.D + sslA a)) (by simp [spwA, KSLA, swA]), ?_⟩, rg⟩
  · simp only [hws, shashAA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [spwA, KSLA, swA]
  · simp only [shashAA, snbA]; rw [Nat.succ_mul]; omega_arith

include hH K in
theorem shash_ctA (hc : HashChecks H.P H.D 2) :
    RelCT isa (Two (SAtA G k g (SEA H KSLA fun _ _ _ => True))) (ctHash H) (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) := by
  refine two_post (two_map (shashAA H) (fun a t h => sl_heA hH h) (ctHash_ct hH K 2 hc (fixedChecks (.inr rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hsl := ssl_leA hok hp.k2
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + sslA s + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + sslA s + H.P.L) H.P.B
  have hks : ∀ k ∈ KSMA, k ∈ KSLA := by decide
  exact WP.mono (WP.keepIn (ctHash_safe hH K) (by rw [ctHash_xd K])
    (ctHash_gen hH K v.L R (hw 27 (by decide)) (hw 28 (by decide)) (by unfold snbA; rw [Nat.succ_mul]; omega_arith)
      (by unfold snbA; rw [Nat.succ_mul]; omega_arith))) fun u ⟨⟨L', rd', wr', _, V', W', R', _, hW', _⟩, f⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_ltA hk) (ksm_neA hk (by decide))
      (ksm_neA hk (by decide))).trans (hw k (hks k hk)), trivial⟩, fun _ hp => by cases hp⟩, rd'.trans hrd,
      frame_keepA hp v.wr v.L.rsp hM f, hok⟩

theorem sclearEm_ctA : RelCT isa (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) clearEm
    (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearEm
  refine two_post (stwoA (G := G) (H := H) [17, 21] [] (fun _ => []) (fun a t h => se_ssA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (clearEm_ok v.L R (k := (s.gpr .rcx).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

theorem sputSalt_ctA (hH : HashOK H) (lk : MgfLink H hH) :
    RelCT isa (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) putSalt (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.putSalt
  refine two_post (stwoA (G := lk.G) (H := H) [23, 24, 39, 40] [] (fun _ => []) (fun a t h => se_ssA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have := slo_le s
  have hss : sslA s = (stackArg s 13).toNat := rfl
  exact WP.mono (WP.keepIn (by safe_by [putSalt]) (by exact Nat.zero_le 8)
    (putSalt_ok v.L R (e := oEm + slo s) (db := sdb H.D s) (q := stackArg s 12) (sl := sslA s) (hw 23 (by decide))
      (hw 24 (by decide)) (hw 39 (by decide)) (w40A (hw 40 (by decide))) (by unfold sdb; omega_arith)
      (by unfold sdb seml oEm oRsa at *; omega_arith)
      (fun i hi => ⟨⟨stackArg s 12, (stackArg s 13).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold sslA at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 12 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold sslA at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold sdb seml oEm oRsa at *; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

include hH in
theorem sputH_ctA (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) (putH H) (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, h1⟩ := hc.putH
  obtain ⟨_, h2⟩ := sFixed.putHTail
  have hDN := hH.hDN
  have hN := hH.N_le
  refine two_post ?_ fun a t ⟨s, S, h⟩ => ?_
  · rw [putH_eq]
    refine RelCT.assoc (RelCT.seq (two_post (Ψ := SAtA G k g (SEA H KSMA fun _ _ _ => True))
      (stwoA (G := G) (H := H) [21, 23, 24] [] (fun _ => [])
      (fun a t h => se_ssA h _) (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, h⟩ => ?_)
      (stwoA (G := G) (H := H) [17, 21] [] (fun _ => [])
        (fun a t (h : SAtA G k g (SEA H KSMA fun _ _ _ => True) a t) => se_ssA h _) (fun _ => rfl) (by decide) h2))
    obtain ⟨v, hrd, hM, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hk2 := S.ps.k2
    have := slo_le s
    exact WP.mono (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 8)
      (putH1_ok hH v.L R (e := oEm + slo s) (db := sdb H.D s) (hw 23 (by decide)) (hw 24 (by decide))
        (by unfold sdb seml oEm oRsa at *; omega_arith) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keepA S.ps v.wr v.L.rsp hM f, hok⟩
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := slo_le s
  exact WP.mono (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 8)
    (putH_ok hH v.L R (e := oEm + slo s) (db := sdb H.D s) (k := (s.gpr .rcx).toNat) (hw 23 (by decide))
      (hw 24 (by decide)) (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) (by unfold sdb seml at *; omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def smgfAnyA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 14, a.wr, oEm + slo a, sdb H.D a⟩

theorem sw15 {a s : State} (S : SSibA G k g a s) (hGl : G.len = H.D) : stackArg a 11 = BitVec.ofNat 64 H.D := by
  rw [← hGl, ← S.pa.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem se_mea (hD0 : 0 < H.D) (hD64 : H.D ≤ 64) (hGl : G.len = H.D) {a t : State}
    (h : SAtA G k g (SEA H KSMA fun _ _ _ => True) a t) : MEA 2 H.D g (smgfAnyA H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hp := S.pa
  have hk2 := hp.k2
  have := slo_le a
  rw [S.seml, S.sslA] at hok
  refine ⟨⟨S.rest, ⟨by simp only [smgfAnyA]; omega_arith, by simp only [smgfAnyA, sdb]; omega_arith, ?_⟩, hD0, hD64⟩,
    (ss_pubA S v).sub (fun p hp => ?_) (fun _ h => h) fun _ _ _ => trivial⟩
  · simp only [smgfAnyA, sdb, seml] at hok ⊢; omega_arith
  · simp only [mwsE, smgfAnyA, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [spwA, KSMA, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · left; rw [swA, sw15 S hGl]
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; right; right; right; right; right; right; right;
        right; rw [swA, S.2.2.2.2.1]

theorem sclearTop_ctA : RelCT isa (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) (.block clearTop)
    (Two (SAtA G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearTop
  refine two_post (stwoA (G := G) (H := H) [23] [] (fun _ => []) (fun a t h => se_ssA h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have := slo_le s
  exact WP.mono (WP.keepIn (by safe_by [clearTop]) (by exact Nat.zero_le 8)
    (clearTop_ok v.L R (e := oEm + slo s) (c := (maskV (sn0v s)).setWidth 8) (hw 23 (by decide))
      (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (by unfold oEm oRsa; omega_arith)))
    fun u ⟨⟨L', k', R'⟩, f⟩ => ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd,
      frame_keepA S.ps v.wr v.L.rsp hM f, hok⟩

end VG.Proof.RsaPss.X86_64.Any
