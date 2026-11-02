module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtEnc
import VerifiedGarbage.Proof.RsaPss.X86_64.EncFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Params

/-!
# EMSA-PSS's encoding on x86-64: constant time, and `Verified`

The prologue, the checks of `emLen` and the salt's length (their branches
are on public values), the encoding (`enc_signEnc_ct`), its copy to `em` and
the epilogue, in two runs whose entry states agree on the public data
(`enc_ct`). With `enc_correct`, `encode` meets
`Proof.RsaPss.encodeContract` (`enc_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Enc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The entry of the frame. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

variable (H) in
/-- After the prologue. -/
def EJ1 (s t : State) : Prop := SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem

variable (H) in
/-- After `fitH`: CF set if `emLen` is too short. -/
def EJ2 (s t : State) : Prop :=
  EJ1 H s t ∧ t.gpr .rax = BitVec.ofNat 64 (seml s) ∧ t.cf = some (decide (seml s < H.D + 2))

variable (H) in
/-- At the end. -/
def EJR (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem pro_ct : RelCT isa (Two (At G J0)) (.block encPrologue) (Two (At G (EJ1 H))) := by
  obtain ⟨_, hc⟩ := eFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 2 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  refine WP.mono (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ =>
    ⟨s, S, ⟨L1, k1.2.2, ⟨_, _, R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k1.2.1, frame_wrR f1⟩
  have hel := hp.hel
  simp only [KS6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [proW', proW, upd, sw, smask, seml, slo, hel]

theorem fit_ct (hc : HashChecks H.P H.D 2) (hH : HashOK H) :
    RelCT isa (Two (At G (EJ1 H))) (.block (fitH H)) (Two (At G (EJ2 H))) := by
  obtain ⟨_, hc⟩ := hc.fit
  refine two_post (stwo (G := G) (H := H) [17] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN; have hN := hH.N_le
  refine WP.mono (fitH_ok (H := H) (by omega) v.L R (k := seml s)
    (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [seml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by unfold seml; omega)) fun t' ⟨k', hm, hax, hcf⟩ =>
    ⟨s, S, ⟨v.keep k' hm (by decide) (fun _ hp => by cases hp), k'.2.1.trans hrd, hm ▸ hM⟩, hax, hcf⟩

/-- A refusal: 0. -/
theorem ret0_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, Sib G a s ∧ SS H s t [] [] X) :
    RelCT isa (Two Φ) ret0 (Two (At G (EJR H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret0
  refine two_post (stwo (G := G) (H := H) [] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun [ret0]) rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp)).sub (by decide) [] (fun _ hp => by cases hp)
      fun _ _ _ => trivial⟩

theorem salt_ct (hc : SignChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two fun a t => At G (EJ2 H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits H)) (Two (At G (SJ6 H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (stwo (G := G) (H := H) [40] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨⟨v, hrd, hM⟩, hax, hcf⟩ := h
  have hok : H.D + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = s.gpr .r8 ∧ u.mem = t.mem) ?_ rfl)
    fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sSaltLen) (by decide), R.rd (d := sSaltLen) 40 rfl (by decide),
      hw 40 (by decide)]
    rfl
  refine WP.mono (saltFits_ok (H := H) (by omega) t5 (a := seml s) (b := s.gpr .r8) hok
    (by unfold seml; omega) (by rw [k5.gpr (by decide)]; exact hax) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ => ?_
  have hm : t6.mem = t.mem := by rw [hm6, hm5]
  exact ⟨s, S, (v.keep (k5.trans k6) hm (by decide) (fun _ hp => by cases hp)).sub (by decide) []
    (fun _ hp => by cases hp) fun _ _ x => x, k6.2.1.trans (k5.2.1.trans hrd), hm ▸ hM, hax6, hc6, hok⟩

theorem copyOut_ct : RelCT isa (Two (At G (SE H KSM fun _ _ _ => True))) copyOut (Two (At G (EJR H))) := by
  obtain ⟨_, hc⟩ := eFixed.copyOut
  refine two_post (stwo (G := G) (H := H) [16, 17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact WP.mono (copyOut_ok hp v.L R v.wr (hw 16 (by decide)) (hw 17 (by decide)) (by unfold seml at hok; omega))
    fun u ⟨L', k', R', _⟩ => ⟨s, S, v.next L' k'.2.2 R' (fun _ hk => by cases hk) trivial⟩

theorem ret1_ct : RelCT isa (Two (At G (EJR H))) (.block [.mov32 .rax (.imm 1)]) (Two (At G (EJR H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret1
  refine two_post (stwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, v⟩ => ?_
  exact WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun) rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp)⟩

theorem restore_ct : RelCT isa (Two (At G (EJR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH) (hc : PssChecks H.P H.D)

include K hc in
theorem body_ct : RelCT isa (Two (At lk.G J0)) (encBody H) fun _ _ => True := by
  unfold encBody encMain
  simp only [seqs]
  exact (RelCT.block_append (pro_ct.seq (fit_ct hc.hash2 hH))).seq ((two_ite
      (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
        rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2, h₂.2.2,
          S₁.seml, S₂.seml])
      (ret0_ct (Φ := fun a t => At lk.G (EJ2 H) a t ∧ isa.eval .b t = some true)
        fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      ((salt_ct hc.sign hH).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
            h₂.2.2.2.2.1, S₁.seml, S₂.seml, S₁.ssl, S₂.ssl])
        (ret0_ct (Φ := fun a t => At lk.G (SJ6 H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        ((enc_signEnc_ct hH K lk hc).seq (copyOut_ct.seq ret1_ct))))).seq restore_ct)

include K hc in
/-- `encode` is constant time. -/
theorem enc_ct : ConstantTime isa (encK lk.G).pre (encK lk.G).pub (encode H) :=
  RelCT.constantTime (valloc ((body_ct hH K lk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl lk.G s₁, h₁⟩, e₁⟩,
      ⟨s₂, ⟨h₁, hpub, h₂⟩, e₂⟩⟩) fun _ _ h => h))

include K hc in
/-- `encode` meets `Proof.RsaPss.encodeContract`. -/
theorem enc_verified : Verified X86_64.target (encode H) (Proof.RsaPss.encodeContract lk.G lk.G abi encStack) :=
  Verified.of_correct (k := encK lk.G) (enc_correct hH K lk) (enc_ct hH K lk hc) (enc_implies lk.G (enc_sat lk.G lk.mem))

end VG.Proof.RsaPss.X86_64.Enc
