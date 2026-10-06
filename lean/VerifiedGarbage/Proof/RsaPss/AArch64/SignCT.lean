import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTEnc

/-!
# RSASSA-PSS signing on AArch64: constant time

`code_ct`: two runs of `sign` from entry states with the same public data
leak the same trace. The checks branch on the modulus' first byte and the
lengths, public (`chk1_ok`, `chk2_ok`); a failure loads `out` from its slot,
public by correctness (`fail_ct`); the encoding is `signEnc_ct`; the
private-key operation is related by its callee's contract (`call_ct`).
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two Pins two_taint two_post two_map two_ite two_alloc privCallCT
  wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV two_taintE zH PssChecks)

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem k : (s.gpr .x3).toNat = kA a := by rw [h.gpr (r := .x3) (by decide)]

theorem nx : nx s = nx a := congrArg BitVec.toNat h.n0

theorem argv : argv s = argv a := by
  unfold Sgn.argv
  rw [h.gpr (r := .x6) (by decide), h.gpr (r := .x7) (by decide), h.2.args 0 (by decide), h.2.args 1 (by decide),
    h.2.args 2 (by decide), h.2.args 3 (by decide), h.2.args 4 (by decide), h.2.args 5 (by decide),
    h.2.args 6 (by decide), h.2.args 7 (by decide), h.2.args 12 (by decide), h.scr]

end E

/-- Our working space and the frame, laid out. -/
theorem lay_of {D K : Nat} {s w : State} (hp : PreS D K s) (hK : 16 ≤ K) (hsp : w.sp = fb s)
    (h20 : w.gpr .x20 = scr s) (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (scr s) := by
  have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hws : (scr s).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr]; exact List.mem_cons_of_mem _ hp.hws,
      ⟨rfl, show oRsa ≤ (stackArg s 12).toNat * 8 by unfold oRsa; omega⟩⟩
    Fw := by omega
    Sw := by unfold oRsa; omega
    dFS := (hp.ks.sub_left (frame_sub0 K s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)).sub_right (rsa_sub hp) }

/-! ## A failed check -/

/-- Zeros to `out`: its address is loaded from its slot, the caller's. -/
theorem fail_ct {D K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E D K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
    RelCT isa (Two Φ) signFail (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => ?_
  rotate_left
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    exact WP.mono (fail_ok e.1 m h23) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]
  unfold signFail
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x14 sOut]) ?_
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x14 = a.gpr .x0 ∧ t.gpr .x23 = a.gpr .x3)
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => ?_) (by taint_decide)) (fun a u h => ?_)
    (two_taint [.x14, .x23] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.1, h₂.1], fun r hr => ?_⟩) (by taint_decide))
  · obtain ⟨_, e₁, m₁, _⟩ := hΦ a s₁ h₁
    obtain ⟨_, e₂, m₂, _⟩ := hΦ a s₂ h₂
    exact ⟨by rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb], fun _ h => absurd h List.not_mem_nil⟩
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    unfold ld
    refine wp_ldrSp (by decide) (by
      rw [m.sp, m.rd, m.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))) fun u' o x =>
      wp_nil ⟨by rw [o.sp, m.sp, e.fb], ?_, by rw [o.get .x23, h23, e.gpr (by decide)]⟩
    rw [x, m.sp]
    exact (m.fr.rs (.x0, sOut) (by simp [regSlots])).trans (e.gpr (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

/-! ## The private-key operation -/

theorem call_ct (c : PrivChecked) {D K : Nat} (hK : 16 ≤ K) (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, E D K a s ∧ AtCall s em t) (.call c.name c.code) fun _ _ => True := by
  refine privCallCT c fun t₁ t₂ ⟨a, ⟨s₁, em₁, h₁, c₁⟩, ⟨s₂, em₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  refine ⟨privOk_of c h₁.1 hcK c₁, privOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.scr, h₂.scr]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rw [c₁.args i hi, c₂.args i hi, h₁.argv, h₂.argv]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_wrS hK c₁.mem h₁.1.kn h₁.1.ns (by have := h₁.1.wn; omega),
      bytes_wrS hK c₂.mem h₂.1.kn h₂.1.ns (by have := h₂.1.wn; omega), h₁.2.bn, h₂.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_wrS hK c₁.mem h₁.1.ke h₁.1.es (by have := h₁.1.we; omega),
      bytes_wrS hK c₂.mem h₂.1.ke h₂.1.es (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H) (c : PrivChecked) {K : Nat}
  (hK : 16 ≤ K) (hcK : c.stack ≤ K)

include hK in
/-- After the checks: the encoding's start. -/
theorem sr_of {a w : State} (h : (∃ s, E H.D K a s ∧ AtS H.D s w) ∧ isa.eval (.nonzero .x .x10) w = some false) :
    SR H.D K (sregs0 H.D) sslots a w := by
  obtain ⟨⟨s, e, hS⟩, hb⟩ := h
  have hp := e.1
  have hk1 := hp.k1; have hk2 := hp.k2
  rw [eval_nonzero, hS.x10, Option.some.injEq, decide_eq_false_iff_not] at hb
  have hk := hS.hk
  have hx := e.nx
  have h3 := e.k
  have L := lay_of hp hK hS.m.sp hS.m.x20 hS.m.wr
  rw [e.fb, e.scr] at L
  refine ⟨⟨s, e, hS.m.rd, hS.m.wr⟩, L, fun q hq => ?_, fun q hq => ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [sregs0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [hS.m.x19, e.scr]
    · rw [hS.m.x21, e.scr]
    · rw [hS.m.x23, e.gpr (by decide)]
    · rw [hS.m.x9, h3, hx]
  · simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact hS.m.fr.dig.trans (e.2.args 8 (by decide))
    · rw [← e.fb]; exact hS.m.fr.salt.trans (e.2.args 9 (by decide))
    · rw [← e.fb]; exact hS.m.fr.sl.trans (e.2.args 10 (by decide))
    · rw [← e.fb]; exact hS.m.lo.trans (by rw [hx])
  · rw [← hx]; exact hS.h0
  · rw [← h3]; exact hk1
  · rw [← h3]; exact hk2
  · show H.D + (stackArg a 10).toNat + 2 ≤ (a.gpr .x3).toNat - loV (nx a)
    rw [← e.2.args 10 (by decide), ← hx, ← e.gpr (r := .x3) (by decide)]
    omega

include hH hGh hGl hG hc hK hcK in
theorem main_ct :
    RelCT isa (Two fun a w => (∃ s, E H.D K a s ∧ AtS H.D s w) ∧ isa.eval (.nonzero .x .x10) w = some false)
      (signMain H c.name c.code) (Two fun a t => t.sp = fb a) := by
  unfold signMain seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E H.D K a s ∧ Main s em t)
    (two_map (fun a => a) (fun a w h => sr_of hK h) (signEnc_ct hH hGh hGl hG hc))
    fun a w ⟨⟨s, e, hS⟩, hb⟩ => ?_) ?_
  · have hp := e.1
    rw [eval_nonzero, hS.x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    have hk := hS.hk
    exact WP.mono (enc_ok hH hGh hGl hG hp hK hS.m (by unfold loV; split <;> omega) (by omega))
      fun t ht => ⟨s, _, e, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E H.D K a s ∧ AtCall s em t)
    (two_taint [] (fun a t₁ t₂ ⟨s₁, _, h₁, m₁⟩ ⟨s₂, _, h₂, m₂⟩ =>
      ⟨by rw [m₁.sp, m₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨s, em, e, hM⟩ => WP.mono (privArgs_ok e.1 hK hM) fun t' h' => ⟨s, em, e, h'⟩) ?_
  exact two_post (call_ct c hK hcK) fun a t ⟨s, em, e, hA⟩ =>
    WP.mono (call_ok c e.1 hK hcK hA) fun t' h' => by rw [h'.sp, e.fb]

include hH hGh hGl hG hc hK hcK in
theorem code_ct : RelCT isa (Two (E H.D K)) (sign H c.name c.code) fun _ _ => True := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  unfold sign
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signBody seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := At H.D K AtChk)
    (two_taint [.x2] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp],
      fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]
        simp only [allocated]
        rw [h₁.gpr (by decide), h₂.gpr (by decide)]⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated]))
      fun t ht => ⟨s, h, ht⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ => ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩)
    (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.n0, h₂.n0])
    (fail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs seqs
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun a u => ∃ s, E H.D K a s ∧ AtE H.D s u)
    (two_taintE [.x10] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ => ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb],
      fun r hr => by rw [List.mem_singleton.mp hr, j₁.x10, j₂.x10, h₁.n0, h₂.n0]⟩)
      (c' := Code.eraseOff (.seq (.block smear) (emLen zH))) rfl (by taint_decide))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_)
  · refine WP.mono (chk1_ok H hD h.1 j fun h0 => ?_) fun u' h' => ⟨s, h, h'⟩
    have : s.mem (s.gpr .x2) = 0 := BitVec.eq_of_toNat_eq h0
    rw [eval_zero, j.x10, this] at hb
    exact absurd hb (by decide)
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.k, h₂.k, h₁.nx, h₂.nx])
    (fail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, j.m, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, E H.D K a s ∧ AtS H.D s w)
    (two_taintE [] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.m.sp, j₂.m.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block ([ld .x12 sSaltLen] ++ saltFits zH))) rfl (by taint_decide))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_
  · rw [eval_nonzero, j.x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    exact WP.mono (chk2_ok H hD h.1 j hb) fun w h' => ⟨s, h, h'⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.k, h₂.k, h₁.nx, h₂.nx, h₁.2.args 10 (by decide),
        h₂.2.args 10 (by decide)])
    (fail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.m.sp, j.m.rd, j.m.wr, j.m.v, j.m.fr⟩, j.m.x23⟩)
    (main_ct hH hGh hGl hG hc c hK hcK)

end

end VG.Proof.RsaPss.AArch64.Sgn
