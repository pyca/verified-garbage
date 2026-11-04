module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# EMSA-PSS's encoding on x86-64: `signEnc` in two runs

`signEnc`'s pieces (`SignCtEnc`), each constant time from the public words of
both runs of `encode`: `DB`'s place and length, the salt's length and so the
length and blocks of `M'`, are public; the digest, the salt and everything
derived from them are not (`enc_signEnc_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

theorem slo_le (s : State) : slo s ≤ 1 := Nat.zero_le 1

/-- The public words after the checks. -/
def KS6 : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 25, 26, 37, 39, 40]

/-- And `DB`'s. -/
def KSM : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 23, 24, 25, 26, 37, 39, 40]

/-- And the length and blocks of `M'`. -/
def KSL : List Nat := [8, 9, 10, 11, 12, 13, 14, 16, 17, 21, 23, 24, 25, 26, 27, 28, 37, 39, 40]

theorem ksm_ne {k j : Nat} (h : k ∈ KSM) (hj : j ∉ KSM) : k ≠ j := fun e => hj (e ▸ h)

theorem ksm_lt {k : Nat} (h : k ∈ KSM) : k < nW := by
  simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega_arith

/-- After the checks: the salt fits, `rax = emLen - hLen - 2`. -/
def SJ6 (H : Hash) (s t : State) : Prop :=
  SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (seml s - (H.D + 2)) ∧ t.cf = some (decide (seml s - (H.D + 2) < ssl s)) ∧
    H.D + 2 ≤ seml s

/-- In the encoding: the public words `ks`. -/
def SE (H : Hash) (ks : List Nat) (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  SS H s t ks [] (X s) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ H.D + ssl s + 2 ≤ seml s

/-- `SE` as a public piece's start. -/
theorem se_ss {ks : List Nat} {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State}
    (h : At T (SE T.H ks X) a t) (ks' : List Nat) (hks : ∀ k ∈ ks', k ∈ ks := by decide) :
    ∃ s X', Sib T a s ∧ SS T.H s t ks' [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem sdb_ct : RelCT isa (Two fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.dbSlots
  refine two_post (stwo (T := T) (H := T.H) [26] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a - (T.H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hcf, hok⟩ := h
  have hfit : T.H.D + ssl s + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega_arith
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  refine X86_64.WP.mono_syms (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 16)
    (dbSlots_ok L R (hw 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ sy =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial sy, k1.2.1.trans hrd, frame_keep hp v.wr L.rsp hM f1, hfit⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, sw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, sw, sdb]
    congr 1; omega_arith
  simp only [upd]; rw [ifn h23, ifn h24]
  exact hw k (by simp only [KSM, KS6, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega_arith)

/-- After `mHash`: `rcx` is `Y`. -/
def SC2 (H : Hash) (s t : State) : Prop := SE H KSM (fun _ _ _ => True) s t ∧ t.gpr .rcx = off (stackArg s 0) oY

variable (hH : HashOK T.H) (K : Callees T.H)

include hH in
theorem scyd_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.seq clearY (copyDigest T.H)) (Two (At T (SC2 T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (stwo (T := T) (H := T.H) [21, 37] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearY]) (by exact Nat.zero_le 16)
    (clearY_ok v.L R)) fun u1 ⟨⟨L1, k1, hcx1, R1⟩, f1⟩ sy1 => ?_)
  have hM1 := frame_keep hp v.wr v.L.rsp hM f1
  refine X86_64.WP.mono_syms (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 16)
    (copyDigest_ok hH L1 R1 (p := s.gpr .rdx) (hw 37 (by decide)) hcx1
    (fun i hi => ⟨⟨s.gpr .rdx, T.H.D⟩, List.mem_append_left _ (by rw [k1.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.dOdg hp.ddgs hp.dKdg (a := s.gpr .rdx + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith)))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ sy2 =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx (sy2.trans sy1), k2.2.1.trans (k1.2.1.trans hrd),
      frame_keep hp (k1.2.2.trans v.wr) L1.rsp hM1 f2, hok⟩, (k2.gpr (by decide)).trans hcx1⟩

theorem w40 {s : State} {W : Nat → BitVec 64} (h : W 40 = sw T.H s 40) : W 40 = BitVec.ofNat 64 (ssl s) := by
  rw [h]; show s.gpr .r8 = _; rw [ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ssl_le {s : State} (h : T.H.D + ssl s + 2 ≤ seml s) (hk : (s.gpr .rsi).toNat ≤ 1024) : ssl s ≤ 1024 := by
  unfold seml at h; omega_arith

include hH in
theorem copySaltY_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SC2 T.H))) (copySaltY T.H) (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.copySaltY
  refine two_post (stwo (T := T) (H := T.H) [39, 40] [.rcx] (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hM, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have hsl := ssl_le hok hk2
  have hss : ssl s = (s.gpr .r8).toNat := rfl
  have hDN := hH.hDN
  have hN := hH.N_le
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 16)
    (copySaltY_ok hH v.L R (q := s.gpr .rcx) (sl := ssl s) (hw 39 (by decide)) (w40 (hw 40 (by decide)))
      (by omega_arith) hcx
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold oY oRsa; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
theorem signLen_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.block (signLen T.H))
      (Two (At T (SE T.H KSL fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.signLen
  refine two_post (stwo (T := T) (H := T.H) [40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hsl := ssl_le hok hp.k2
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 16)
    (signLen_ok hH v.L R (sl := ssl s) (w40 (hw 40 (by decide))) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      by_cases h27 : k = 27
      · subst h27; simp [upd, sw]
      by_cases h28 : k = 28
      · subst h28; simp [upd, sw, snb]
      simp only [upd]; rw [ifn h28, ifn h27]
      exact hw k (by simp only [KSL, KSM, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega_arith)) trivial sy,
      k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- A public word of the entry state `a`. -/
theorem spw_w {H : Hash} {a : State} {ks : List Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ spw H a ks, W p.1 = p.2)
    {k : Nat} (hk : k ∈ ks) : W k = sw H a k :=
  hw (k, sw H a k) (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The slots of the table of `MdHash`, in a run. -/
theorem ss_ht {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : SS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = sw T.H s k) (h8 : 8 ∈ ks := by decide) (h9 : 9 ∈ ks := by decide)
    (h10 : 10 ∈ ks := by decide) : HT T.H T.dn T.f W t.syms := by
  rw [v.sy]; exact hp.tabs.hf.ht ((hw 8 h8).trans hp.tabs.h0) ((hw 9 h9).trans hp.tabs.h3) ((hw 10 h10).trans hp.tabs.h4)

/-- The slots of the table of `Hash`, in a run. -/
theorem ss_gt {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : SS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = sw T.H s k) (h11 : 11 ∈ ks := by decide) (h12 : 12 ∈ ks := by decide)
    (h13 : 13 ∈ ks := by decide) (h14 : 14 ∈ ks := by decide) : GT T.G T.g W t.syms := by
  rw [v.sy]
  exact hp.tabs.gf.gt ((hw 11 h11).trans hp.tabs.g0) ((hw 12 h12).trans hp.tabs.g1) ((hw 13 h13).trans hp.tabs.g2)
    ((hw 14 h14).trans hp.tabs.g4)

/-- The hash's anchor: the blocks of `M'`. -/
def shashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, snb H a, a.syms⟩

include hH in
theorem sl_he {a t : State} (h : At T (SE T.H KSL fun _ _ _ => True) a t) :
    HE T.H T.dn T.f 2 (shashA T.H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hk2 := S.pa.k2
  have tb := S.pa.tabs
  rw [S.ssl, S.seml] at hok
  have hsl := ssl_le hok hk2
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + ssl a + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + ssl a + T.H.P.L) T.H.P.B
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pub S v
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [shashA, snb]; rw [Nat.succ_mul]; omega_arith⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, 8 + T.H.D + ssl a, spw_w hw (k := 27) (by decide), ?_⟩, rg⟩, S.syH.tr v.sy⟩
  · simp only [hws, shashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact spw_w hw (k := 21) (by decide)
    · exact spw_w hw (k := 28) (by decide)
    · exact (spw_w hw (k := 8) (by decide)).trans tb.h0
    · exact (spw_w hw (k := 9) (by decide)).trans tb.h3
    · exact (spw_w hw (k := 10) (by decide)).trans tb.h4
  · simp only [shashA, snb]; rw [Nat.succ_mul]; omega_arith

variable (hdk : DigOK T.H) (hf : MdFnsSafe T.f) (hg : FnsSafe T.g)

include hH K hdk hf in
theorem shash_ct (hc : HashChecks T.H.P T.H.D 2) :
    RelCT isa (Two (At T (SE T.H KSL fun _ _ _ => True))) (ctHash T.f T.H)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  refine two_post (two_map (shashA T.H) (fun a t h => sl_he hH h)
    (ctHash_ct hH K hdk 2 hc (fixedChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hsl := ssl_le hok hp.k2
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + ssl s + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + ssl s + T.H.P.L) T.H.P.B
  have hks : ∀ k ∈ KSM, k ∈ KSL := by decide
  exact X86_64.WP.mono_syms (WP.keepIn (ctHash_safe hH hf) (by have := ctHash_xd (H := T.H) hf; omega)
    (ctHash_gen hH K v.L R (hw 27 (by decide)) (hw 28 (by decide)) (by unfold snb; rw [Nat.succ_mul]; omega_arith)
      (by unfold snb; rw [Nat.succ_mul]; omega_arith) (ss_ht hp v hw) hdk))
    fun u ⟨⟨L', rd', wr', _, V', W', R', _, hW', _⟩, f⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (ksm_ne hk (by decide))
      (ksm_ne hk (by decide))).trans (hw k (hks k hk)), trivial⟩, (fun _ hp => by cases hp), sy.trans v.sy⟩,
      rd'.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearEm_ct : RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) clearEm
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearEm
  refine two_post (stwo (T := T) (H := T.H) [17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hk1 : 1 ≤ (s.gpr .rsi).toNat := by unfold seml at hok; omega_arith
  exact X86_64.WP.mono_syms (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (clearEm_ok v.L R (k := (s.gpr .rsi).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sputSalt_ct :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) putSalt (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.putSalt
  refine two_post (stwo (T := T) (H := T.H) [23, 24, 39, 40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  have hss : ssl s = (s.gpr .r8).toNat := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putSalt]) (by exact Nat.zero_le 16)
    (putSalt_ok v.L R (e := oEm + slo s) (db := sdb T.H.D s) (q := s.gpr .rcx) (sl := ssl s) (hw 23 (by decide))
      (hw 24 (by decide)) (hw 39 (by decide)) (w40 (hw 40 (by decide))) (by unfold sdb; omega_arith)
      (by unfold sdb seml oEm oRsa at *; omega_arith)
      (fun i hi => ⟨⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside hp.dOsa hp.dsas hp.dKsa (a := s.gpr .rcx + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega_arith) (by omega_arith))
        rwa [v.wr]) (by unfold sdb seml oEm oRsa at *; omega_arith)))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
/-- `putH`'s copy of the digest. -/
theorem putH1_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hend : e + db + T.H.D ≤ oRsa) (he1 : oEm ≤ e) :
    WP isa (.seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
      scr .rsi oDig ++ ([.mov32 .r8 (.imm 0)] : List Instr)))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 T.H.D)))) u fun w =>
      Lay w F S ∧ Keep [.rdi, .rsi, .rax, .r8] u w ∧ Rep w.mem F S (cpV V (fun i => V (oDig + i)) (e + db) T.H.D) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .r8, .rax] (Q := fun v => v.gpr .rdi = off S (e + db) ∧
      v.gpr .rsi = off S oDig ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), he, hdb, off_plus,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (copy_ok Lv Rv (d := .rdi) (by decide) (p := off S oDig) (o := e + db) (disp := 0)
    (n := T.H.D) (stepI_ok (show T.H.D < 2 ^ 31 by omega_arith) v [.rax, .r8]) hD (by unfold oRsa at *; omega_arith) h₂ h₁ h₃
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega_arith))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega_arith) (by omega_arith) (by omega_arith)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa at *; omega_arith)]
  · rfl

include hH in
theorem sputH_ct (hc : SignChecks T.H.P T.H.D) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (putH T.H) (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, h1⟩ := hc.putH
  obtain ⟨_, h2⟩ := sFixed.putHTail
  have hDN := hH.hDN
  have hN := hH.N_le
  refine two_post ?_ fun a t ⟨s, S, h⟩ => ?_
  · rw [putH_eq]
    refine RelCT.assoc (RelCT.seq (two_post (Ψ := At T (SE T.H KSM fun _ _ _ => True))
      (stwo (T := T) (H := T.H) [21, 23, 24] [] (fun _ => [])
      (fun a t h => se_ss h _) (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, h⟩ => ?_)
      (stwo (T := T) (H := T.H) [17, 21] [] (fun _ => [])
        (fun a t (h : At T (SE T.H KSM fun _ _ _ => True) a t) => se_ss h _) (fun _ => rfl) (by decide) h2))
    obtain ⟨v, hrd, hM, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hk2 := S.ps.k2
    have : slo s = 0 := rfl
    exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 16)
      (putH1_ok hH v.L R (e := oEm + slo s) (db := sdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
        (by unfold sdb seml oEm oRsa at *; omega_arith) (by omega_arith))) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
      ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep S.ps v.wr v.L.rsp hM f, hok⟩
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 16)
    (putH_ok hH v.L R (e := oEm + slo s) (db := sdb T.H.D s) (k := (s.gpr .rsi).toNat) (hw 23 (by decide))
      (hw 24 (by decide)) (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_arith) (by unfold sdb seml at *; omega_arith) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def smgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 0, a.wr, oEm + slo a, sdb H.D a, a.syms⟩

theorem se_me {a t : State} (h : At T (SE T.H KSM fun _ _ _ => True) a t) :
    ME T.G T.g 2 T.H (smgfA T.H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hp := S.pa
  have hk2 := hp.k2
  have tb := hp.tabs
  have : slo a = 0 := rfl
  rw [S.seml, S.ssl] at hok
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pub S v
  refine ⟨⟨S.rest, ⟨by simp only [smgfA]; omega_arith, by simp only [smgfA, sdb]; omega_arith, ?_⟩⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, trivial⟩, rg⟩, S.syG.tr v.sy⟩
  · simp only [smgfA, sdb, seml] at hok ⊢; omega_arith
  · simp only [smgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact spw_w hw (k := 21) (by decide)
    · exact spw_w hw (k := 23) (by decide)
    · exact spw_w hw (k := 24) (by decide)
    · exact (spw_w hw (k := 14) (by decide)).trans tb.g4
    · exact (spw_w hw (k := 11) (by decide)).trans tb.g0
    · exact (spw_w hw (k := 12) (by decide)).trans tb.g1
    · exact (spw_w hw (k := 13) (by decide)).trans tb.g2

variable (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D)
  (hGv : Proof.Mgf1.Valid Gs)

include hG hGh hGl hGv hg in
theorem smgf_ct (hc : HashChecks T.H.P T.H.D 2) :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (mgfXor T.H T.g)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  refine two_post (two_map (smgfA T.H) (fun a t h => se_me h)
    (mgfXor_ct hG hGh hGl hGv hc (fixedChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (mgfXor_safe hg) (mgfXor_xd hg)
    (mgfXor_ok hG hGh hGl hGv T.H v.L R (ss_gt hp v hw) (e := oEm + slo s) (db := sdb T.H.D s)
      ⟨by omega_arith, by unfold sdb; omega_arith, by unfold sdb seml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
      (hw 24 (by decide)))) fun u ⟨⟨L', rd', wr', _, V', W', R', hW', _⟩, f⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (by
      simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      (fun _ hp => by cases hp), sy.trans v.sy⟩, rd'.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearTop_ct : RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) (.block clearTop)
    (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearTop
  refine two_post (stwo (T := T) (H := T.H) [23] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have : slo s = 0 := rfl
  exact X86_64.WP.mono_syms (WP.keepIn (by safe_by [clearTop]) (by exact Nat.zero_le 16)
    (clearTop_ok v.L R (e := oEm + slo s) (c := smask s) (hw 23 (by decide))
      (by rw [hw 25 (by decide)]; rfl) (by unfold oEm oRsa; omega_arith)))
    fun u ⟨⟨L', k', R'⟩, f⟩ sy => ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd,
      frame_keep S.ps v.wr v.L.rsp hM f, hok⟩

include hH K hdk hf hG hGh hGl hGv hg in
theorem enc_signEnc_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some false) (signEnc T.f T.H T.g)
      (Two (At T (SE T.H KSM fun _ _ _ => True))) := by
  unfold signEnc
  simp only [seqs]
  exact sdb_ct.seq (RelCT.assoc ((scyd_ct hH hc.sign).seq ((copySaltY_ct hH hc.sign).seq
    ((signLen_ct hH hc.sign).seq ((shash_ct hH K hdk hf hc.hash2).seq (sclearEm_ct.seq (sputSalt_ct.seq
      ((sputH_ct hH hc.sign).seq ((smgf_ct hg hG hGh hGl hGv hc.hash2).seq sclearTop_ct)))))))))

end VG.Proof.RsaPss.X86_64.Enc
