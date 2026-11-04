module

public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtEnc
import VerifiedGarbage.Proof.RsaPss.X86_64.EncFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.Framework.X86_64.Syms

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

variable {T : Tabs}

/-- The entry of the frame. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The public words the prologue stores. -/
def KS0 : List Nat := [16, 17, 21, 25, 26, 37, 39, 40]

/-- And the slots of the table of `MdHash`. -/
def KS1 : List Nat := [8, 9, 10, 16, 17, 21, 25, 26, 37, 39, 40]

/-- After the prologue: `r11` is the table `hash`. -/
def EJa (H : Hash) (s t : State) : Prop :=
  SS H s t KS0 [(.r11, stackArg s 2)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem

/-- After its slots: `r11` is the table `mgf1`. -/
def EJb (H : Hash) (s t : State) : Prop :=
  SS H s t KS1 [(.r11, stackArg s 3)] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame [frR s] s.mem t.mem

/-- After the tables' slots. -/
def EJ1 (H : Hash) (s t : State) : Prop :=
  SS H s t KS6 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem

/-- After `fitH`: CF set if `emLen` is too short. -/
def EJ2 (H : Hash) (s t : State) : Prop :=
  EJ1 H s t ∧ t.gpr .rax = BitVec.ofNat 64 (seml s) ∧ t.cf = some (decide (seml s < H.D + 2))

/-- At the end. -/
def EJR (H : Hash) (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem pro_ct : RelCT isa (Two (At T J0)) (.block (encPrologue ++ [.mov .r11 (.mem (arg 2))]))
    (Two (At T (EJa T.H))) := by
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
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (encPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ s1 => ?_
  refine X86_64.WP.mono_syms (argR11_ok hp L1.rsp k1.2.1 f1 (j := 2) (by decide)) fun t2 ⟨k2, hm2, h11⟩ s2 =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun p hp => by rw [List.mem_singleton.mp hp]; exact h11,
      s2.trans s1⟩, k2.2.1.trans k1.2.1, hm2 ▸ f1⟩
  have hel := hp.hel
  simp only [KS0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [proW', proW, upd, sw, smask, seml, slo, hel]

theorem hsl_ct : RelCT isa (Two (At T (EJa T.H))) (.block (hSlots ++ [.mov .r11 (.mem (arg 3))]))
    (Two (At T (EJb T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.hSl
  refine two_post (stwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 2)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (hSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', h11, f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩,
      fun p hp => by rw [List.mem_singleton.mp hp]; exact h11, sy.trans v.sy⟩, k.2.1.trans hrd, f'⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | h | h | h | h | h | h | h | h
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  all_goals
    simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega)]
    exact hw _ (by simp only [KS0, List.mem_cons, List.not_mem_nil, or_false]; omega)

theorem gsl_ct : RelCT isa (Two (At T (EJb T.H))) (.block gSlots) (Two (At T (EJ1 T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.gSl
  refine two_post (stwo (T := T) (H := T.H) [] [.r11] (fun a => [(.r11, stackArg a 3)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (fun _ hk => by cases hk) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg (by decide)]; exact h.1.regs _ (List.mem_singleton_self _))
      fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hf⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine X86_64.WP.mono_syms (gSl_ok S.ps v.L R hrd hf (v.regs _ (List.mem_singleton_self _)))
    fun u ⟨k, L', f', R'⟩ sy =>
    ⟨s, S, ⟨L', k.2.2.trans v.wr, ⟨_, _, R', fun j hj => ?_, trivial⟩, (fun _ hp => by cases hp), sy.trans v.sy⟩,
      k.2.1.trans hrd, frame_wrR f'⟩
  simp only [KS6, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h | rfl | rfl | rfl | rfl | h | h | h | h | h | h | h | h
  rotate_left 3
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  · simp [upd, sw]
  all_goals
    simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
    exact hw _ (by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false]; omega)

theorem fit_ct (hc : HashChecks T.H.P T.H.D 2) (hH : HashOK T.H) :
    RelCT isa (Two (At T (EJ1 T.H))) (.block (fitH T.H)) (Two (At T (EJ2 T.H))) := by
  obtain ⟨_, hc⟩ := hc.fit
  refine two_post (stwo (T := T) (H := T.H) [17] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN; have hN := hH.N_le
  refine X86_64.WP.mono_syms (fitH_ok (H := T.H) (by omega) v.L R (k := seml s)
    (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [seml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by unfold seml; omega)) fun t' ⟨k', hm, hax, hcf⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hm ▸ hM⟩, hax, hcf⟩

/-- A refusal: 0. -/
theorem ret0_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, Sib T a s ∧ SS T.H s t [] [] X) :
    RelCT isa (Two Φ) ret0 (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret0
  refine two_post (stwo (T := T) (H := T.H) [] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun [ret0]) rfl)
    fun t' ⟨hm, k⟩ sy => ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp) sy).sub (by decide) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

theorem salt_ct (hc : SignChecks T.H.P T.H.D) (hH : HashOK T.H) :
    RelCT isa (Two fun a t => At T (EJ2 T.H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits T.H)) (Two (At T (SJ6 T.H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (stwo (T := T) (H := T.H) [40] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨⟨v, hrd, hM⟩, hax, hcf⟩ := h
  have hok : T.H.D + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = s.gpr .r8 ∧ u.mem = t.mem) ?_ rfl)
    fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ sy5 => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sSaltLen) (by decide), R.rd (d := sSaltLen) 40 rfl (by decide),
      hw 40 (by decide)]
    rfl
  refine X86_64.WP.mono_syms (saltFits_ok (H := T.H) (by omega) t5 (a := seml s) (b := s.gpr .r8) hok
    (by unfold seml; omega) (by rw [k5.gpr (by decide)]; exact hax) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ sy6 => ?_
  have hm : t6.mem = t.mem := by rw [hm6, hm5]
  exact ⟨s, S, (v.keep (k5.trans k6) hm (by decide) (fun _ hp => by cases hp) (sy6.trans sy5)).sub (by decide) []
    (fun _ hp => by cases hp) fun _ _ x => x, k6.2.1.trans (k5.2.1.trans hrd), hm ▸ hM, hax6, hc6, hok⟩

theorem copyOut_ct :
    RelCT isa (Two (At T (SE T.H KSM fun _ _ _ => True))) copyOut (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.copyOut
  refine two_post (stwo (T := T) (H := T.H) [16, 17, 21] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact X86_64.WP.mono_syms (copyOut_ok hp v.L R v.wr (hw 16 (by decide)) (hw 17 (by decide))
    (by unfold seml at hok; omega))
    fun u ⟨L', k', R', _⟩ sy => ⟨s, S, v.next L' k'.2.2 R' (fun _ hk => by cases hk) trivial sy⟩

theorem ret1_ct : RelCT isa (Two (At T (EJR T.H))) (.block [.mov32 .rax (.imm 1)]) (Two (At T (EJR T.H))) := by
  obtain ⟨_, hc⟩ := eFixed.ret1
  refine two_post (stwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, v⟩ => ?_
  exact X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun) rfl) fun t' ⟨hm, k⟩ sy =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp) sy⟩

theorem restore_ct : RelCT isa (Two (At T (EJR T.H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
    (by decide) hc

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)
  (hf : MdFnsSafe T.f) (hg : FnsSafe T.g) (hdk : DigOK T.H) (hc : PssChecks T.H.P T.H.D)

include hH K hG hGh hGl hGv hf hg hdk hc in
theorem body_ct : RelCT isa (Two (At T J0)) (encBody T.f T.H T.g) fun _ _ => True := by
  unfold encBody encMain
  simp only [seqs]
  exact pro_ct.seq (hsl_ct.seq (gsl_ct.seq ((fit_ct hc.hash2 hH).seq ((two_ite
      (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
        rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2, h₂.2.2,
          S₁.seml, S₂.seml])
      (ret0_ct (Φ := fun a t => At T (EJ2 T.H) a t ∧ isa.eval .b t = some true)
        fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      ((salt_ct hc.sign hH).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
            h₂.2.2.2.2.1, S₁.seml, S₂.seml, S₁.ssl, S₂.ssl])
        (ret0_ct (Φ := fun a t => At T (SJ6 T.H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        ((enc_signEnc_ct hH K hdk hf hg hG hGh hGl hGv hc).seq (copyOut_ct.seq ret1_ct))))).seq restore_ct))))

include hH K hG hGh hGl hGv hf hg hdk hc in
/-- `encode` is constant time. -/
theorem enc_ct (Hs : Spec.Mgf1.Hash) :
    ConstantTime isa (encK T Hs Gs).pre (encK T Hs Gs).pub (encode T.f T.H T.g) :=
  RelCT.constantTime (valloc ((body_ct hH K hG hGh hGl hGv hf hg hdk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨Pre.of T h₁, pub_refl s₁, Pre.of T h₁⟩, e₁⟩,
      ⟨s₂, ⟨Pre.of T h₁, hpub, Pre.of T h₂⟩, e₂⟩⟩) fun _ _ h => h))

end VG.Proof.RsaPss.X86_64.Enc
