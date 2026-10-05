import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtBase

/-!
# RSASSA-PSS signing on x86-64: the encoding in two runs

`signEnc`'s pieces, each constant time from the public words of both runs:
`DB`'s place and length, the salt's length and so the length and blocks of
`M'`, are public; the digest, the salt and everything derived from them are
not (`signEnc_ct`). Each piece keeps the memory outside the writable regions
(`Frame`), for the private-key operation after it.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The public words after the checks. -/
def KS6 : List Nat := [16, 17, 18, 19, 20, 21, 22, 25, 26, 37, 39, 40]

/-- And `DB`'s. -/
def KSM : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 37, 39, 40]

/-- And the length and blocks of `M'`. -/
def KSL : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 37, 39, 40]

theorem ksm_ne {k j : Nat} (h : k ∈ KSM) (hj : j ∉ KSM) : k ≠ j := fun e => hj (e ▸ h)

theorem ksm_lt {k : Nat} (h : k ∈ KSM) : k < nW := by
  simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega

variable (H) in
/-- After the checks: the salt fits, `rax = emLen - hLen - 2`. -/
def SJ6 (s t : State) : Prop :=
  SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (seml s - (H.D + 2)) ∧ t.cf = some (decide (seml s - (H.D + 2) < ssl s)) ∧
    H.D + 2 ≤ seml s

variable (H) in
/-- In the encoding: the public words `ks`. -/
def SE (ks : List Nat) (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  SS H s t ks [] (X s) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ H.D + ssl s + 2 ≤ seml s

/-- `SE` as a public piece's start. -/
theorem se_ss {ks : List Nat} {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State}
    (h : SAt G (SE H ks X) a t) (ks' : List Nat) (hks : ∀ k ∈ ks', k ∈ ks := by decide) :
    ∃ s X', SSib G a s ∧ SS H s t ks' [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem ksm_upd {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KSM, W k = sw H s k) {j : Nat} (hj : j ∉ KSM)
    (v : BitVec 64) : ∀ k ∈ KSM, upd W j v k = sw H s k := fun k hk => by
  simp only [upd]; rw [ifn (ksm_ne hk hj)]; exact hw k hk

theorem sdb_ct : RelCT isa (Two fun a t => SAt G (SJ6 H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (SAt G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.dbSlots
  refine two_post (stwo (G := G) (H := H) [26] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hcf, hok⟩ := h
  have hfit : H.D + ssl s + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  refine WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R (hw 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial, k1.2.1.trans hrd, frame_keep hp v.wr L.rsp hM f1, hfit⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, sw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, sw, sdb]
    congr 1; omega
  simp only [upd]; rw [ifn h23, ifn h24]
  exact hw k (by simp only [KSM, KS6, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)

variable (H) in
/-- After `mHash`: `rcx` is `Y`. -/
def SC2 (s t : State) : Prop := SE H KSM (fun _ _ _ => True) s t ∧ t.gpr .rcx = off (stackArg s 13) oY

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH in
theorem scyd_ct (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) (.seq clearY (copyDigest H)) (Two (SAt lk.G (SC2 H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (stwo (G := lk.G) (H := H) [21, 37] [] (fun _ => []) (fun a t h => se_ss h _)
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
  have hM1 := frame_keep hp v.wr v.L.rsp hM f1
  refine WP.mono (WP.keepIn (by safe_by [copyDigest]) (by exact Nat.zero_le 8)
    (copyDigest_ok hH L1 R1 (p := stackArg s 10) (hw 37 (by decide)) hcx1
    (fun i hi => ⟨⟨stackArg s 10, lk.G.len⟩, List.mem_append_left _ (by rw [k1.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside lk.G hp.dOdg hp.ddgs hp.dKdg (a := stackArg s 10 + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega) (by omega))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega)))) fun u2 ⟨⟨L2, k2, R2⟩, f2⟩ =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx, k2.2.1.trans (k1.2.1.trans hrd),
      frame_keep hp (k1.2.2.trans v.wr) L1.rsp hM1 f2, hok⟩, (k2.gpr (by decide)).trans hcx1⟩

theorem w40 {s : State} {W : Nat → BitVec 64} (h : W 40 = sw H s 40) : W 40 = BitVec.ofNat 64 (ssl s) := by
  rw [h]; show stackArg s 12 = _; rw [ssl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ssl_le {s : State} (h : H.D + ssl s + 2 ≤ seml s) (hk : (s.gpr .rcx).toNat ≤ 1024) : ssl s ≤ 1024 := by
  unfold seml at h; omega

include hH in
theorem copySaltY_ct (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAt lk.G (SC2 H))) (copySaltY H) (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.copySaltY
  refine two_post (stwo (G := lk.G) (H := H) [39, 40] [.rcx] (fun a => [(.rcx, off (stackArg a 13) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (i := 13) (by decide)]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hM, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have hsl := ssl_le hok hk2
  have hss : ssl s = (stackArg s 12).toNat := rfl
  have hDN := hH.hDN
  have hN := hH.N_le
  exact WP.mono (WP.keepIn (by safe_by [copySaltY]) (by exact Nat.zero_le 8)
    (copySaltY_ok hH v.L R (q := stackArg s 11) (sl := ssl s) (hw 39 (by decide)) (w40 (hw 40 (by decide)))
      (by omega) hcx
      (fun i hi => ⟨⟨stackArg s 11, (stackArg s 12).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega) (by omega)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 11 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega) (by omega))
        rwa [v.wr]) (by unfold oY oRsa; omega)))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
theorem signLen_ct (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAt G (SE H KSM fun _ _ _ => True))) (.block (signLen H))
      (Two (SAt G (SE H KSL fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := hc.signLen
  refine two_post (stwo (G := G) (H := H) [40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hsl := ssl_le hok hp.k2
  exact WP.mono (WP.keepIn (by safe_by [signLen]) (by exact Nat.zero_le 8)
    (signLen_ok hH v.L R (sl := ssl s) (w40 (hw 40 (by decide))) (by omega))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      by_cases h27 : k = 27
      · subst h27; simp [upd, sw]
      by_cases h28 : k = 28
      · subst h28; simp [upd, sw, snb]
      simp only [upd]; rw [ifn h28, ifn h27]
      exact hw k (by simp only [KSL, KSM, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)) trivial,
      k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def shashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 13, a.wr, snb H a⟩

include hH in
theorem sl_he {a t : State} (h : SAt G (SE H KSL fun _ _ _ => True) a t) : HE H 2 (shashA H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hk2 := S.pa.k2
  rw [S.ssl, S.seml] at hok
  have hsl := ssl_le hok hk2
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + ssl a + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + ssl a + H.P.L) H.P.B
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := ss_pub S v
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [shashA, snb]; rw [Nat.succ_mul]; omega⟩,
    L, w, ⟨V, W, R, fun p hp => hw p ?_, 8 + H.D + ssl a, hw (27, BitVec.ofNat 64 (8 + H.D + ssl a)) (by simp [spw, KSL, sw]), ?_⟩, rg⟩
  · simp only [hws, shashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [spw, KSL, sw]
  · simp only [shashA, snb]; rw [Nat.succ_mul]; omega

include hH K in
theorem shash_ct (hc : HashChecks H.P H.D 2) :
    RelCT isa (Two (SAt G (SE H KSL fun _ _ _ => True))) (ctHash H) (Two (SAt G (SE H KSM fun _ _ _ => True))) := by
  refine two_post (two_map (shashA H) (fun a t h => sl_he hH h) (ctHash_ct hH K 2 hc (fixedChecks (.inr rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have hsl := ssl_le hok hp.k2
  have h1 := Nat.lt_div_mul_add (a := 8 + H.D + ssl s + H.P.L) (b := H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + H.D + ssl s + H.P.L) H.P.B
  have hks : ∀ k ∈ KSM, k ∈ KSL := by decide
  exact WP.mono (WP.keepIn (ctHash_safe hH K) (by rw [ctHash_xd K])
    (ctHash_gen hH K v.L R (hw 27 (by decide)) (hw 28 (by decide)) (by unfold snb; rw [Nat.succ_mul]; omega)
      (by unfold snb; rw [Nat.succ_mul]; omega))) fun u ⟨⟨L', rd', wr', _, V', W', R', _, hW', _⟩, f⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (ksm_ne hk (by decide))
      (ksm_ne hk (by decide))).trans (hw k (hks k hk)), trivial⟩, fun _ hp => by cases hp⟩, rd'.trans hrd,
      frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearEm_ct : RelCT isa (Two (SAt G (SE H KSM fun _ _ _ => True))) clearEm
    (Two (SAt G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearEm
  refine two_post (stwo (G := G) (H := H) [17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (clearEm_ok v.L R (k := (s.gpr .rcx).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sputSalt_ct (hH : HashOK H) (lk : MgfLink H hH) :
    RelCT isa (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) putSalt (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.putSalt
  refine two_post (stwo (G := lk.G) (H := H) [23, 24, 39, 40] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have wSa := hp.wSa
  have hk2 := hp.k2
  have := slo_le s
  have hss : ssl s = (stackArg s 12).toNat := rfl
  exact WP.mono (WP.keepIn (by safe_by [putSalt]) (by exact Nat.zero_le 8)
    (putSalt_ok v.L R (e := oEm + slo s) (db := sdb H.D s) (q := stackArg s 11) (sl := ssl s) (hw 23 (by decide))
      (hw 24 (by decide)) (hw 39 (by decide)) (w40 (hw 40 (by decide))) (by unfold sdb; omega)
      (by unfold sdb seml oEm oRsa at *; omega)
      (fun i hi => ⟨⟨stackArg s 11, (stackArg s 12).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
        Offset.contains_base _ (by unfold ssl at hi; omega) (by omega)⟩)
      (fun i hi j hj => Outside.ne v.L (by
        have := hp.outside lk.G hp.dOsa hp.dsas hp.dKsa (a := stackArg s 11 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by unfold ssl at hi; omega) (by omega))
        rwa [v.wr]) (by unfold sdb seml oEm oRsa at *; omega)))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

include hH in
/-- `putH`'s copy of the digest. -/
theorem putH1_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hend : e + db + H.D ≤ oRsa) (he1 : oEm ≤ e) :
    WP isa (.seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
      scr .rsi oDig ++ ([.mov32 .r8 (.imm 0)] : List Instr)))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.imm (BitVec.ofNat 32 H.D)))) u fun w =>
      Lay w F S ∧ Keep [.rdi, .rsi, .rax, .r8] u w ∧ Rep w.mem F S (cpV V (fun i => V (oDig + i)) (e + db) H.D) W := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c5 : oRsa = 8192 := rfl
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
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
    (n := H.D) (stepI_ok (show H.D < 2 ^ 31 by omega) v [.rax, .r8]) hD (by unfold oRsa at *; omega) h₂ h₁ h₃
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa at *; omega)]
  · rfl

include hH in
theorem sputH_ct (hc : SignChecks H.P H.D) :
    RelCT isa (Two (SAt G (SE H KSM fun _ _ _ => True))) (putH H) (Two (SAt G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, h1⟩ := hc.putH
  obtain ⟨_, h2⟩ := sFixed.putHTail
  have hDN := hH.hDN
  have hN := hH.N_le
  refine two_post ?_ fun a t ⟨s, S, h⟩ => ?_
  · rw [putH_eq]
    refine RelCT.assoc (RelCT.seq (two_post (Ψ := SAt G (SE H KSM fun _ _ _ => True))
      (stwo (G := G) (H := H) [21, 23, 24] [] (fun _ => [])
      (fun a t h => se_ss h _) (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, h⟩ => ?_)
      (stwo (G := G) (H := H) [17, 21] [] (fun _ => [])
        (fun a t (h : SAt G (SE H KSM fun _ _ _ => True) a t) => se_ss h _) (fun _ => rfl) (by decide) h2))
    obtain ⟨v, hrd, hM, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hk2 := S.ps.k2
    have := slo_le s
    exact WP.mono (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 8)
      (putH1_ok hH v.L R (e := oEm + slo s) (db := sdb H.D s) (hw 23 (by decide)) (hw 24 (by decide))
        (by unfold sdb seml oEm oRsa at *; omega) (by omega))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keep S.ps v.wr v.L.rsp hM f, hok⟩
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := slo_le s
  exact WP.mono (WP.keepIn (by safe_by [putH]) (by exact Nat.zero_le 8)
    (putH_ok hH v.L R (e := oEm + slo s) (db := sdb H.D s) (k := (s.gpr .rcx).toNat) (hw 23 (by decide))
      (hw 24 (by decide)) (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) (by unfold sdb seml at *; omega) hk2)) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def smgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 13, a.wr, oEm + slo a, sdb H.D a⟩

theorem se_me {a t : State} (h : SAt G (SE H KSM fun _ _ _ => True) a t) : ME H 2 (smgfA H a) t := by
  obtain ⟨s, S, v, -, -, hok⟩ := h
  have hp := S.pa
  have hk2 := hp.k2
  have := slo_le a
  rw [S.seml, S.ssl] at hok
  refine ⟨⟨S.rest, ⟨by simp only [smgfA]; omega, by simp only [smgfA, sdb]; omega, ?_⟩⟩,
    (ss_pub S v).sub (fun p hp => ?_) (fun _ h => h) fun _ _ _ => trivial⟩
  · simp only [smgfA, sdb, seml] at hok ⊢; omega
  · simp only [smgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [spw, KSM, sw]

include hH K in
theorem smgf_ct (hc : HashChecks H.P H.D 2) :
    RelCT isa (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) (mgfXor H)
      (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) := by
  have hG := validG hH lk.hash lk.len
  refine two_post (two_map (smgfA H) (fun a t h => se_me h)
    (mgfXor_ct hH K 2 lk.hash lk.len hG hc (fixedChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := slo_le s
  exact WP.mono (WP.keepIn (mgfXor_safe hH K) (by rw [mgfXor_xd K])
    (mgfXor_ok hH K lk.hash lk.len hG v.L R (e := oEm + slo s) (db := sdb H.D s)
      ⟨by omega, by unfold sdb; omega, by unfold sdb seml at *; unfold oEm; omega⟩ (hw 23 (by decide))
      (hw 24 (by decide)))) fun u ⟨⟨L', rd', wr', _, V', W', R', hW', _⟩, f⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_lt hk) (by
      simp only [KSM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega)).trans (hw k hk), trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, frame_keep hp v.wr v.L.rsp hM f, hok⟩

theorem sclearTop_ct : RelCT isa (Two (SAt G (SE H KSM fun _ _ _ => True))) (.block clearTop)
    (Two (SAt G (SE H KSM fun _ _ _ => True))) := by
  obtain ⟨_, hc⟩ := sFixed.clearTop
  refine two_post (stwo (G := G) (H := H) [23] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have := slo_le s
  exact WP.mono (WP.keepIn (by safe_by [clearTop]) (by exact Nat.zero_le 8)
    (clearTop_ok v.L R (e := oEm + slo s) (c := (maskV (sn0v s)).setWidth 8) (hw 23 (by decide))
      (by rw [hw 25 (by decide)]; exact maskV_byte (BitVec.isLt _)) (by unfold oEm oRsa; omega)))
    fun u ⟨⟨L', k', R'⟩, f⟩ => ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd,
      frame_keep S.ps v.wr v.L.rsp hM f, hok⟩

include hH K in
theorem signEnc_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two fun a t => SAt lk.G (SJ6 H) a t ∧ isa.eval .b t = some false) (signEnc H)
      (Two (SAt lk.G (SE H KSM fun _ _ _ => True))) := by
  unfold signEnc
  simp only [seqs]
  exact sdb_ct.seq (RelCT.assoc ((scyd_ct hH lk hc.sign).seq ((copySaltY_ct hH lk hc.sign).seq
    ((signLen_ct hH hc.sign).seq ((shash_ct hH K hc.hash2).seq (sclearEm_ct.seq ((sputSalt_ct hH lk).seq
      ((sputH_ct hH hc.sign).seq ((smgf_ct hH K lk hc.hash2).seq sclearTop_ct)))))))))

end VG.Proof.RsaPss.X86_64
