import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_bounded_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ, 544)` (`J6`), the branch on `η`, and the loop for `η`, iteration `t` of
which starts from `LAt σ t` with the coefficients `rbFold` samples from the
first `t` bytes of output stored.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the `u32` argument in `esi`. -/
abbrev etaOf (s : State) : Nat := ((s.gpr .rsi).setWidth 32).toNat

/-- `vg_mldsa_rej_bounded_poly(seed = rdi, eta = esi, a = rdx, scratch = rcx) -> eax`, with
16 bytes of stack below `rsp`. -/
def rbK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 66⟩] ∧ s.wr = [pR (s.gpr .rdx), ⟨s.gpr .rcx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 66⟩ (pR (s.gpr .rdx)) ∧ Region.Disjoint ⟨s.gpr .rdi, 66⟩ ⟨s.gpr .rcx, 2048⟩ ∧
    (pR (s.gpr .rdx)).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rdx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧ (s.gpr .rcx).toNat + 2048 ≤ 2 ^ 64 ∧
    (VG.Proof.MlDsa.X86_64.Sample.etaOf s = 2 ∨ VG.Proof.MlDsa.X86_64.Sample.etaOf s = 4)
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (rbFold (VG.Proof.MlDsa.X86_64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256 then 1 else 0) ∧
      ((rbFold (VG.Proof.MlDsa.X86_64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544)).length = 256 →
        PolyIs s'.mem (s.gpr .rdx) (VG.Proof.MlDsa.Sample.toPoly (rbFold (VG.Proof.MlDsa.X86_64.Sample.etaOf s) [] (H (bytesAt s.mem (s.gpr .rdi) 66) 544))))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    Spec.MlDsa.rejBoundedLeak (VG.Proof.MlDsa.X86_64.Sample.etaOf s₁) (bytesAt s₁.mem (s₁.gpr .rdi) 66) =
      Spec.MlDsa.rejBoundedLeak (VG.Proof.MlDsa.X86_64.Sample.etaOf s₂) (bytesAt s₂.mem (s₂.gpr .rdi) 66)

namespace RejBounded

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, 66, σ.gpr .rcx, σ.gpr .rdx, BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32)⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (VG.Proof.MlDsa.X86_64.Sample.RejBounded.B σ) 544

section
variable {σ : State} (hp : rbK.pre σ)
include hp

theorem spOk : SpOk (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (66 : Nat) < 2 ^ 64; decide⟩

theorem eta : VG.Proof.MlDsa.X86_64.Sample.etaOf σ = 2 ∨ VG.Proof.MlDsa.X86_64.Sample.etaOf σ = 4 := hp.2.2.2.2.2.2.2.2.2.2.2.2

omit hp in
theorem sx66 : BitVec.signExtend 64 (66 : BitVec 32) = BitVec.ofNat 64 66 := by decide

theorem pro_ok : WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.pro .rcx .rdx (.reg .rsi) (.imm 66))) σ (J0 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold VG.Impl.MlDsa.X86_64.Sample.pro; xrun [inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp) (a := 2040) (n := 8) (by omega), VG.Proof.MlDsa.X86_64.Sample.RejBounded.sx66])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rbFold (VG.Proof.MlDsa.X86_64.Sample.etaOf σ) [] ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ).take t)

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 840) 544 = VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ
  rsi : s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 840 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (544 - t)
  stored : VG.Proof.MlDsa.Sample.Stored s.mem (σ.gpr .rdx) (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ t)

omit hp in
theorem X_length : (VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ).length = 544 := VG.Proof.MlDsa.Sample.H_length _ _

omit hp in
theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

omit hp in
theorem out_byte {t : Nat} {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ t s) (ht : t < 544) : s.mem (s.gpr .rsi) = (VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ).getD t 0 := by
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ ht] at this
  rw [h.rsi]; exact this

omit hp in
theorem Lt_length_le (t : Nat) : (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 544) (h : VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ t s) :
    WP isa (rbBody (VG.Proof.MlDsa.X86_64.Sample.etaOf σ)) s fun s' => VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (544 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rdx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hp' := VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp
  refine WP.mono (rbBody_ok (VG.Proof.MlDsa.X86_64.Sample.RejBounded.eta hp) s (aP := σ.gpr .rdx) h.env.rbp h.rdi (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt_length_le t) (.of_mem hw) h.stored
    (by rw [h.rsi, at_add]; exact inScrRd hp' h.env (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have ht1 : VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ (t + 1) = rbStep (VG.Proof.MlDsa.X86_64.Sample.etaOf σ) (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ t) ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ).getD t 0) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt]
    rw [VG.Proof.MlDsa.X86_64.Sample.RejBounded.take_succ' _ (by rw [VG.Proof.MlDsa.X86_64.Sample.RejBounded.X_length]; omega), rbFold_snoc]
  rw [VG.Proof.MlDsa.X86_64.Sample.RejBounded.out_byte h ht, ← ht1] at hdi hst
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' k) 64 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 544) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, offAdd],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : J6 136 544 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s' ∧ bytesAt s'.mem ((VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 840) 544 = VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ ∧ s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 840 ∧
        s'.gpr .rdi = 0 := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, VG.Proof.MlDsa.X86_64.Sample.sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1⟩
  rw [hm1, h.out]; exact (VG.Proof.MlDsa.Sample.H_eq _ _).symm

/-- The loop: `LAt σ 544` at the end. -/
theorem loop_ok {s : State} (h : J6 136 544 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s) : WP isa (rbLoop (VG.Proof.MlDsa.X86_64.Sample.etaOf σ)) s (VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ 544) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejBounded.lat0 h) fun s1 ⟨he, hout, hsi, hdi⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 544)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 544) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ) (fun t ht s hI _ =>
    WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejBounded.lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok {s : State} (h : J6 136 544 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s) :
    WP isa (.seq (.block [.alu32 .cmp .r12 (.imm 2)]) (.ite .e (rbLoop 2) (rbLoop 4))) s (VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ 544) := by
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 2 == 0)) (by xrun) (by rfl))
    fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ?_)
  have k1' : Keep [] s s1 := ⟨fun r hr => by
    by_cases e : r = .r12
    · subst e; exact h12
    · exact k1.gpr (by simp [e]), k1.2⟩
  have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (VG.Proof.MlDsa.X86_64.Sample.etaOf σ) := by
    rw [h.env.r12]; rw [VG.Proof.MlDsa.X86_64.Sample.sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hJ : J6 136 544 (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOf σ) σ s1 := ⟨h.env.keep hm1 (k1'.mono (by decide)), by rw [hm1]; exact h.out⟩
  rcases VG.Proof.MlDsa.X86_64.Sample.RejBounded.eta hp with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [← he]; exact VG.Proof.MlDsa.X86_64.Sample.RejBounded.loop_ok hp hJ
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [← he]; exact VG.Proof.MlDsa.X86_64.Sample.RejBounded.loop_ok hp hJ

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.RejBounded.LAt σ 544 s) :
    WP isa (.block (retJ ++ VG.Impl.MlDsa.X86_64.Sample.epi)) s fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  have hL : VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt σ 544 = rbFold (VG.Proof.MlDsa.X86_64.Sample.etaOf σ) [] (VG.Proof.MlDsa.X86_64.Sample.RejBounded.X σ) := by
    simp only [VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt]; rw [List.take_of_length_le (by rw [VG.Proof.MlDsa.X86_64.Sample.RejBounded.X_length])]
  refine WP.mono (retEpi_ok (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp) h.env h.rdi (VG.Proof.MlDsa.X86_64.Sample.RejBounded.Lt_length_le 544)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm, ← hL]
    rw [← hL] at hf
    exact stored_polyIs h.stored hf

end

end RejBounded

theorem rejBounded_correct (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.rejBounded σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' := by
  open RejBounded in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejBounded.pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (VG.Proof.MlDsa.X86_64.Sample.RejBounded.spOk hp) (rate := 136) (outlen := 544) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.RejBounded.sel_ok hp h2) fun s3 h3 => VG.Proof.MlDsa.X86_64.Sample.RejBounded.end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly`

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ′, 640)` (`J6`), the branch on `γ₁`, and the loop for `c = 1 + bitlen (γ₁ -
1)`, iteration `g` of which starts from `EAt σ c g` with the coefficients of
the first `g` groups stored. It is constant time: the taint analysis proves
each piece but the sponge, whose proof is `sponge_ct`, from the pointers and
`γ₁`.
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- `γ₁`, the `u32` argument in `esi`. -/
abbrev gOf (s : State) : Nat := ((s.gpr .rsi).setWidth 32).toNat

/-- `vg_mldsa_expand_mask_poly(seed = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 16 bytes of stack below `rsp`. -/
def emK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 66⟩] ∧ s.wr = [pR (s.gpr .rdx), ⟨s.gpr .rcx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 66⟩ (pR (s.gpr .rdx)) ∧ Region.Disjoint ⟨s.gpr .rdi, 66⟩ ⟨s.gpr .rcx, 2048⟩ ∧
    (pR (s.gpr .rdx)).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 66⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rdx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rcx, 2048⟩ ∧ (s.gpr .rcx).toNat + 2048 ≤ 2 ^ 64 ∧
    (VG.Proof.MlDsa.X86_64.Sample.gOf s = 2 ^ 17 ∨ VG.Proof.MlDsa.X86_64.Sample.gOf s = 2 ^ 19)
  post s s' :=
    PolyIs s'.mem (s.gpr .rdx) (toRq (bitUnpack (H (bytesAt s.mem (s.gpr .rdi) 66) (32 * (1 + bitlen (VG.Proof.MlDsa.X86_64.Sample.gOf s - 1))))
      (VG.Proof.MlDsa.X86_64.Sample.gOf s - 1) (VG.Proof.MlDsa.X86_64.Sample.gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace ExpandMask

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, 66, σ.gpr .rcx, σ.gpr .rdx, BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32)⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.B σ) 640

section
variable {σ : State} (hp : emK.pre σ)
include hp

theorem spOk : SpOk (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (66 : Nat) < 2 ^ 64; decide⟩

theorem gamma : VG.Proof.MlDsa.X86_64.Sample.gOf σ = 2 ^ 17 ∨ VG.Proof.MlDsa.X86_64.Sample.gOf σ = 2 ^ 19 := hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem pro_ok : WP isa (.block (VG.Impl.MlDsa.X86_64.Sample.pro .rcx .rdx (.reg .rsi) (.imm 66))) σ (J0 (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rsi).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold VG.Impl.MlDsa.X86_64.Sample.pro; xrun [inScrσ (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) (a := 2024) (n := 8) (by omega),
      inScrσ (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) (a := 2032) (n := 8) (by omega), inScrσ (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) (a := 2040) (n := 8) (by omega),
      RejBounded.sx66])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ => pro_J0 hm hbx hbp h12 hcx h8 k

/-! ## The loop -/

/-- At the start of iteration `g` of the loop for `c`. -/
structure EAt (σ : State) (c g : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.X86_64.Sample.Env (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 840) 640 = VG.Proof.MlDsa.X86_64.Sample.ExpandMask.X σ
  rsi : s.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 840 + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = σ.gpr .rdx + BitVec.ofNat 64 (16 * g)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (64 - g)
  st : ∀ i < 4 * g, coeffAt s.mem (σ.gpr .rdx) i = emV (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.X σ) c i

theorem gpre {c g : Nat} (hg : g < 64) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ c g s) :
    GPre c (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.X σ) ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 840) (σ.gpr .rdx) g s := by
  have hp' := VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp
  refine ⟨h.rsi, h.rdi, hg, fun j hj => ?_, fun j hj => ?_,
    fun i hi => ⟨_, by rw [h.env.wr, hp.2.1]; simp, coeff_contains _ hi⟩, fun j hj hc => ?_⟩
  · have := congrArg (fun L => L.getD j 0) h.out
    rw [MlKem.bytesAt_getD _ _ hj] at this
    exact this
  · rw [at_add]; exact inScrRd hp' h.env (by omega)
  · rw [at_add] at hc
    exact a_scr' hp' (a := 840 + j) (n := 1) (by omega) _ hc (Region.contains_self _ _)

/-- An iteration, from `EAt`. -/
theorem eat_step {c g : Nat} (hc : emOk c) (hg : g < 64) {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ c g s) :
    WP isa (.block (emBody c)) s fun s' => VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ c (g + 1) s' ∧
      s'.zf = some (BitVec.ofNat 64 (64 - g) - 1 == 0) := by
  have hp' := VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp
  refine WP.mono (emBody_ok hc (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.gpre hp hg h)) fun s' ⟨hk, hf, hst, hsame, hsi, hdi, hcx, hz⟩ => ?_
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' k) 64 = s.mem.readW ((VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 640) (by omega)).symm)
      (by omega)]; exact h.out, hsi, hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    fun i hi => ?_⟩, by rw [hz, h.rcx]⟩
  by_cases hlo : i < 4 * g
  · rw [hsame i (by omega) (.inl hlo)]; exact h.st i hlo
  · have := hst (i - 4 * g) (by omega)
    rwa [show 4 * g + (i - 4 * g) = i by omega] at this

/-- The loop for `c`, from the sponge's output. -/
theorem loop_ok {c : Nat} (hc : emOk c) {s : State} (h : J6 136 640 (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ s) :
    WP isa (emLoop c) s (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ c 64) := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ).at' 840 ∧ s'.gpr .rdi = σ.gpr .rdx) (by xrun [h.env.rbx, h.env.rbp, VG.Proof.MlDsa.X86_64.Sample.sx840])
    (by decide)) fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 64)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  refine wp_countdown (N := 64) (by decide) (by decide) (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ c) (fun g hg s hI _ =>
    WP.mono (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.eat_step hp hc hg hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1, h.out]; exact (VG.Proof.MlDsa.Sample.H_eq _ _).symm,
      by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1]; simp, hcx,
      fun i hi => absurd hi (by omega)⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

omit hp in
theorem sx17 : BitVec.signExtend 64 (0x20000 : BitVec 32) = BitVec.ofNat 64 0x20000 := by decide

/-- The branch on `γ₁`, and the loop for it. -/
theorem sel_ok {s : State} (h : J6 136 640 (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ s) :
    WP isa (.seq (.block [.alu32 .cmp .r12 (.imm 0x20000)]) (.ite .e (emLoop 18) (emLoop 20))) s
      (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ (emC (VG.Proof.MlDsa.X86_64.Sample.gOf σ)) 64) := by
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.zf = some (BitVec.setWidth 32 (s.gpr .r12) - 0x20000 == 0)) (by xrun) (by rfl))
    fun s1 ⟨⟨hm1, h12, hz1⟩, k1⟩ => ?_)
  have k1' : Keep [] s s1 := ⟨fun r hr => by
    by_cases e : r = .r12
    · subst e; exact h12
    · exact k1.gpr (by simp [e]), k1.2⟩
  have hr12 : BitVec.setWidth 32 (s.gpr .r12) = BitVec.ofNat 32 (VG.Proof.MlDsa.X86_64.Sample.gOf σ) := by
    rw [h.env.r12]; rw [VG.Proof.MlDsa.X86_64.Sample.sw32_64, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hJ : J6 136 640 (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ s1 := ⟨h.env.keep hm1 (k1'.mono (by decide)), by rw [hm1]; exact h.out⟩
  rcases VG.Proof.MlDsa.X86_64.Sample.ExpandMask.gamma hp with he | he
  · refine WP.ite true (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun _ => ?_) (fun hb => absurd hb (by decide))
    rw [show emC (VG.Proof.MlDsa.X86_64.Sample.gOf σ) = 18 by rw [he]; rfl]; exact VG.Proof.MlDsa.X86_64.Sample.ExpandMask.loop_ok hp (.inl rfl) hJ
  · refine WP.ite false (by show s1.zf = _; rw [hz1, hr12, he]; rfl) (fun hb => absurd hb (by decide)) (fun _ => ?_)
    rw [show emC (VG.Proof.MlDsa.X86_64.Sample.gOf σ) = 20 by rw [he]; rfl]; exact VG.Proof.MlDsa.X86_64.Sample.ExpandMask.loop_ok hp (.inr rfl) hJ

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.X86_64.Sample.ExpandMask.EAt σ (emC (VG.Proof.MlDsa.X86_64.Sample.gOf σ)) 64 s) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Sample.epi) s fun s' => emK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sample.epi_ok (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) h.env) fun s' ⟨⟨hbx, hbp, h12, hm⟩, k⟩ =>
    ⟨?_, gpr_end (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) h.env hbx hbp h12 (k.mono (by simp)) hm⟩
  obtain ⟨_, _, hγ⟩ := emC_eq (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.gamma hp)
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [expandMask_getElem _ (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.gamma hp) hi, hm, h.st i (by omega)]
  simp only [emV]
  congr 3
  rw [← hγ]

end

end ExpandMask

theorem expandMask_correct (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.expandMask σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' := by
  open ExpandMask in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp) (rate := 136) (outlen := 640) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.sel_ok hp h2) fun s3 h3 => VG.Proof.MlDsa.X86_64.Sample.ExpandMask.end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

namespace ExpandMask

theorem hok : ∀ σ, emK.pre σ → SpOk (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ := fun _ hp => VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOk hp

theorem hpub : ∀ σ₁ σ₂, emK.pre σ₁ → emK.pre σ₂ → emK.pub σ₁ σ₂ → SpPub (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ₁) (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => ⟨hq.1, rfl, hq.2.2.2.1, hq.2.2.1, by simp only [hq.2.1], hq.2.2.2.2⟩

end ExpandMask

open ExpandMask in
theorem expandMask_ct : ConstantTime isa emK.pre emK.pub Impl.MlDsa.X86_64.Sample.expandMask := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (VG.Proof.MlDsa.X86_64.Sample.ExpandMask.spOf σ) σ)
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.X86_64.Sample.ExpandMask.pro_ok hp)
    (taintRel [.rdi, .rdx, .rcx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]) (by taint_decide))) ?_)
  refine RelCT.seq (sponge_ct VG.Proof.MlDsa.X86_64.Sample.ExpandMask.hok VG.Proof.MlDsa.X86_64.Sample.ExpandMask.hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact taintSp VG.Proof.MlDsa.X86_64.Sample.ExpandMask.hpub (J := J6 136 640) (fun _ _ h => h.env) [] VG.Proof.MlDsa.X86_64.Sample.nil_regs (by taint_decide)

/-- A state satisfying the precondition. -/
def emSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x20000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem expandMask_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.expandMask (Spec.MlDsa.expandMaskContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Sample.expandMask_correct VG.Proof.MlDsa.X86_64.Sample.expandMask_ct
    { pre := by sig_implies_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.X86_64.Sample.emK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.X86_64.Sample.emK, X86_64.abi, X86_64.argRegs]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.X86_64.Sample.emK, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨hsp, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp⟩
      sat := by sig_implies_sat [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.X86_64.Sample.emK, X86_64.abi,
        X86_64.argRegs] [emSat] using VG.Proof.MlDsa.X86_64.Sample.emSat }

end VG.Proof.MlDsa.X86_64.Sample

end
