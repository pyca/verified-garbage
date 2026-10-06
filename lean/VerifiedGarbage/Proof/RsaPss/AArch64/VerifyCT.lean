import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTMain

/-!
# RSASSA-PSS verification on AArch64: constant time

`code_ct`: two runs of `verifyPrecomputed` from entry states with the same
public data leak the same trace. The checks branch on public values only
(`chk1_ok`, `chk2_ok`), the precomputed public operation is related by its
callee's contract (`call_ct`), and the checks of `EM` are `check_ct`.
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two two_taint two_post two_map two_ite two_alloc pdCallCT)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0)

/-- A buffer of the caller, apart from the stack. -/
theorem bytes_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {len : Nat}
    (hk : (kR K s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm) hl (List.mem_range.mp hi)

/-- Words of the caller, apart from the stack. -/
theorem words_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {n : Nat}
    (hk : (kR K s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm

/-! ## The precomputed public operation -/

theorem call_ct (c : PdChecked) {D K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => VOk D a ∧ ∃ s, E D K a s ∧ AtCall D s (loV (nxV s)) (cbA s) t)
      (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨_, s₁, h₁, c₁⟩, ⟨_, s₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  have g : ∀ i, 0 < i → i < 5 → stackArg s₁ i = stackArg s₂ i := fun i h h' =>
    (h₁.2.args i h h').trans (h₂.2.args i h h').symm
  refine ⟨pdOk_of c h₁.1 hcK c₁, pdOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, h₁.scr, h₂.scr]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, g 3 (by decide) (by decide)]
    · rw [c₁.x3, c₂.x3, g 4 (by decide) (by decide)]
    · rw [c₁.x4, c₂.x4, e .x2 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x3 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x5 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x1 (by decide)]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.scr, h₂.scr]
    · rw [c₁.a1, c₂.a1, g 2 (by decide) (by decide)]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, words_f c₁.mem h₁.1.kP h₁.1.wP, words_f c₂.mem h₂.1.kP h₂.1.wP, h₁.2.w, h₂.2.w]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_f c₁.mem h₁.1.ke (by have := h₁.1.we; omega),
      bytes_f c₂.mem h₂.1.ke (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

/-- After the call: the checks' start. -/
theorem vr_of {D K : Nat} (hK : 16 ≤ K) {a s t : State} (ok : VOk D a) (e : E D K a s)
    (ha : AfterCall D K s (loV (nxV s)) (cbA s) t) : VR D K (vregs D) vslots a t := by
  have L := rsa_lay e.1 hK ha.sp ha.wr ha.x20
  rw [e.fb, e.scr] at L
  have hx := e.nx
  have hk := e.k
  refine ⟨⟨s, e, ha.rd, ha.wr⟩, L, fun q hq => ?_, fun q hq => ?_, ok⟩
  · simp only [vregs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [ha.x19, e.scr]
    · rw [ha.x21, e.scr]
    · rw [ha.x23, e.gpr (by decide)]
    · rw [ha.x24, e.scr, hx]
    · rw [ha.x25, hk, hx]
  · simp only [vslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact ha.lo.trans (by rw [hx])
    · rw [← e.fb]
      exact ha.c.trans (by
        show ((maskV (nxV s)).setWidth 8).setWidth 64 = ((maskV (nxV a)).setWidth 8).setWidth 64; rw [hx])
    · rw [← e.fb]; exact ha.fr.any.trans e.any
    · rw [← e.fb]; exact (ha.fr.rs (.x7, sSaltLen) (by simp [regSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact (ha.fr.rs (.x4, sDig) (by simp [regSlots])).trans (e.gpr (by decide))

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H) (c : PdChecked) {K : Nat}
  (hK : 16 ≤ K) (hcK : c.stack ≤ K)

include hH hGh hGl hG hc hK hcK in
theorem main_ct :
    RelCT isa (Two fun a w => (∃ s, E H.D K a s ∧ AtSV H.D s w) ∧ isa.eval (.nonzero .x .x10) w = some false)
      (verifyMain H c.name c.code) (Two fun a t => t.sp = fb a) := by
  unfold verifyMain seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := fun a u => VOk H.D a ∧ ∃ s, E H.D K a s ∧ PreCall H.D s (loV (nxV s)) (cbA s) u)
    (two_taint [] (fun a w₁ w₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.m.sp, j₂.m.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a w ⟨⟨s, e, hS⟩, _⟩ => ?_) ?_
  · have hk := hS.hk
    have hp := e.1
    have hk1 := hp.k1; have hk2 := hp.k2
    have ok : VOk H.D a := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · show 64 ≤ (a.gpr .x1).toNat; rw [← e.k]; exact hk1
      · show (a.gpr .x1).toNat ≤ 1024; rw [← e.k]; exact hk2
      · show H.D + 2 ≤ (a.gpr .x1).toNat - loV (nxV a); rw [← e.k, ← e.nx]; omega
      · show loV (nxV a) ≤ 1; unfold loV; split <;> omega
    exact WP.mono (pre_ok hp hK hS.m (by omega)) fun u hu => ⟨ok, s, e, hu⟩
  refine RelCT.seq (two_post (Ψ := fun a u => VOk H.D a ∧ ∃ s, E H.D K a s ∧ AtCall H.D s (loV (nxV s)) (cbA s) u)
    (two_taint [] (fun a w₁ w₂ ⟨_, s₁, h₁, j₁⟩ ⟨_, s₂, h₂, j₂⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨ok, s, e, hP⟩ => WP.mono (pubArgs_ok hP) fun t ht => ⟨ok, s, e, ht⟩) ?_
  refine RelCT.seq (two_post (Ψ := VR H.D K (vregs H.D) vslots) (call_ct c hcK)
    fun a t ⟨ok, s, e, ha⟩ => WP.mono (call_ok c e.1 hcK ha) fun t' h' => vr_of hK ok e h') ?_
  exact check_ct hH hGh hGl hG hc

include hH hGh hGl hG hc hK hcK in
theorem code_ct : RelCT isa (Two (E H.D K)) (verifyPrecomputed H c.name c.code) fun _ _ => True := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  unfold verifyPrecomputed
  refine two_alloc (R := fun _ _ => True) ?_
  unfold verifyBody seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := At H.D K AtChk)
    (two_taint [.x0] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp],
      fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]
        simp only [allocated]
        rw [h₁.gpr (by decide), h₂.gpr (by decide)]⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated]))
      fun t ht => ⟨s, h, ht⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.n0, h₂.n0])
    (vfail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩⟩) ?_
  unfold seqs seqs seqs
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun a u => ∃ s, E H.D K a s ∧ AtEV H.D s u)
    (two_taintE [.x10] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ => ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb],
      fun r hr => by rw [List.mem_singleton.mp hr, j₁.x10, j₂.x10, h₁.n0, h₂.n0]⟩)
      (c' := Code.eraseOff (.seq (.block smear) (emLen zH))) rfl (by taint_decide))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_)
  · refine WP.mono (chk1_ok H hD h.1 j fun h0 => ?_) fun u' h' => ⟨s, h, h'⟩
    have : s.mem (s.gpr .x0) = 0 := BitVec.eq_of_toNat_eq h0
    rw [eval_zero, j.x10, this] at hb
    exact absurd hb (by decide)
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.k, h₂.k, h₁.nx, h₂.nx])
    (vfail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, j.m⟩) ?_
  unfold seqs seqs
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun a w => ∃ s, E H.D K a s ∧ AtSV H.D s w)
    (RelCT.seq (expLen_ct hK) (two_taintE [] (fun a t₁ t₂ h₁ h₂ =>
      ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (saltFits zH))) rfl (by taint_decide)))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_)
  · rw [eval_nonzero, j.x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    exact WP.mono (chk2_ok H hD h.1 hK j hb) fun w h' => ⟨s, h, h'⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by
      rw [eval_nonzero, eval_nonzero, j₁.x10, j₂.x10, h₁.k, h₂.k, h₁.nx, h₂.nx, h₁.sLen, h₂.sLen])
    (vfail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.m.sp, j.m.rd, j.m.wr, j.m.v, j.m.fr⟩⟩)
    (main_ct hH hGh hGl hG hc c hK hcK)

end

end VG.Proof.RsaPss.AArch64.Vfy
