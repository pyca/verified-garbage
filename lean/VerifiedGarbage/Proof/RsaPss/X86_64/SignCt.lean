import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtEnc
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCt

/-!
# RSASSA-PSS signing on x86-64: constant time, and `Verified`

The prologue, the checks on the modulus and the salt's length (their
branches are on public values), the encoding (`signEnc_ct`), the private-key
operation's arguments and the call (constant time by its contract: its
public data, the key's place and lengths, the modulus and the exponent,
agree), and the epilogue, in two runs whose entry states agree on the public
data (`sign_ct`). With `sign_correct`, `sign` meets
`Spec.RsaPss.signContract` (`sign_verified`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The words the prologue stores. -/
def KS1 : List Nat := [16, 17, 18, 19, 20, 21, 22, 37, 39, 40]

variable (H) in
/-- After the prologue: the modulus' first byte, and ZF set if it is zero. -/
def SJ1 (s t : State) : Prop :=
  SS H s t KS1 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

variable (H) in
/-- After `emLen`: CF set if it is too short. -/
def SJ4 (s t : State) : Prop :=
  SS H s t (KS1 ++ [25, 26]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (seml s) ∧ t.cf = some (decide (seml s < H.D + 2))

variable (H) in
/-- At the end. -/
def SJR (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem spro_ct : RelCT isa (Two (SAt G J0)) (.block (signPrologue ++ n0)) (Two (SAt G (SJ1 H))) := by
  obtain ⟨_, hc⟩ := sFixed.pro
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
  refine WP.mono (signPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  refine WP.mono (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1)) fun t2 ⟨k2, hm2, hax2, hz2⟩ =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k2.2.1.trans k1.2.1,
      hm2 ▸ frame_wrR f1, hax2, hz2⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [proW, upd, sw]

/-- A refusal: zeros to `out`. -/
theorem sfail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib G a s ∧ SS H s t [16, 17] [] X) :
    RelCT isa (Two Φ) signFail (Two (SAt G (SJR H))) := by
  obtain ⟨_, hc⟩ := sFixed.fail
  refine two_post (stwo (G := G) (H := H) [16, 17] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [v.wr, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  exact WP.mono (signFail_ok v.L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) (hw 16 (by decide))
    (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) hk2
    hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega)))
    (hO.sub_right (frame_sub s))) fun u ⟨L', k', R', _⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial⟩

theorem semLen_ct (hc : SignChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two fun a t => SAt G (SJ1 H) a t ∧ isa.eval .e t = some false) (.seq (.block smear) (emLen H))
      (Two (SAt G (SJ4 H))) := by
  obtain ⟨_, hc⟩ := hc.emLen
  refine two_post (stwo (G := G) (H := H) [17] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (sn0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.sn0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have h0 : sn0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine WP.seq (WP.mono (smear_ok t (x := sn0v s) (BitVec.isLt _) h0 hax) fun t3 ⟨k3, hm3, hdx3, hz3⟩ => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 13) := v.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 13) V W := hm3 ▸ R
  refine WP.mono (WP.keepIn (by safe_by [emLen]) (by exact Nat.zero_le 8)
    (emLen_ok (H := H) (by omega) L3 R3 (x := sn0v s) (k := (s.gpr .rcx).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) (by omega) hdx3 hz3)) fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ =>
    ⟨s, S, ⟨L4, k4.2.2.trans (k3.2.2.trans v.wr), ⟨V, _, R4, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
      k4.2.1.trans (k3.2.1.trans hrd), frame_keep hp (k3.2.2.trans v.wr) L3.rsp (hm3 ▸ hM) f4, hax4, hc4⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 25 ∧ k ≠ 26 := by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp only [upd]; rw [ifn this.2, ifn this.1]; exact hw k hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp [upd, sw, slo]

theorem ssalt_ct (hc : SignChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two fun a t => SAt G (SJ4 H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits H)) (Two (SAt G (SJ6 H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (stwo (G := G) (H := H) [40] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (seml a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.seml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hcf⟩ := h
  have hok : H.D + 2 ≤ seml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.gpr .rdx = stackArg s 12 ∧ u.mem = t.mem) ?_ rfl)
    fun t5 ⟨⟨hdx5, hm5⟩, k5⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sSaltLen) (by decide), R.rd (d := sSaltLen) 40 rfl (by decide),
      hw 40 (by decide)]
    rfl
  refine WP.mono (saltFits_ok (H := H) (by omega) t5 (a := seml s) (b := stackArg s 12) hok
    (by unfold seml; omega) (by rw [k5.gpr (by decide)]; exact hax) hdx5) fun t6 ⟨k6, hm6, hax6, hc6⟩ => ?_
  have hm : t6.mem = t.mem := by rw [hm6, hm5]
  exact ⟨s, S, (v.keep (k5.trans k6) hm (by decide) (fun _ hp => by cases hp)).sub (by decide) []
    (fun _ hp => by cases hp) fun _ _ x => x, k6.2.1.trans (k5.2.1.trans hrd), hm ▸ hM, hax6, hc6, hok⟩

variable (H) in
/-- Before the call. -/
def SJP (s t : State) : Prop :=
  SS H s t [] [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem privArgs_ct : RelCT isa (Two (SAt G (SE H KSM fun _ _ _ => True))) (.block privArgs) (Two (SAt G (SJP H))) := by
  obtain ⟨_, hc⟩ := sFixed.privArgs
  refine two_post (stwo (G := G) (H := H) [] [] (fun _ => []) (fun a t h => se_ss h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, _⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (privArgs_ok hp v.L hrd (argsKept_of hp hM) R (hw 16 (by decide)) (hw 17 (by decide)) (hw 18 (by decide))
      (hw 19 (by decide)) (hw 20 (by decide)) (hw 22 (by decide))))
    fun u ⟨⟨k', L', ⟨W', R', ha, _⟩, di, si, dx, cx, r8, r9⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
      fun i hi => (R'.fr i (by unfold nW frameBytes; omega)).trans (ha i hi), di, si, dx, cx, r8, r9⟩

/-- An input, at the call, as on entry. -/
theorem sentry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem)
    {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R) (hS : R.Disjoint (scrR s))
    (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  exact bytesAt_frame fSE (in_apart hK hO hS) hl

theorem pArg_sib {a s : State} (S : SSib G a s) {i : Nat} (hi : i < 14) : pArg s i = pArg a i := by
  unfold pArg
  split
  · rw [S.arg (i := 13) (by decide)]
  · rw [S.gpr (r := .rcx) (by decide)]
  · rw [S.arg (i := 13) (by decide)]
  · rw [S.arg (i := 14) (by decide)]
  · exact S.arg (by omega)

/-- The call's public data agree. -/
theorem scall_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : SSib G a s₁) (h₁ : SJP H s₁ t₁) (S₂ : SSib G a s₂)
    (h₂ : SJP H s₂ t₂) :
    chkContract.pub (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 14, stackArg (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) i = pArg a i :=
    fun i hi => ((stackArg_call p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (pArg_sib S₁ hi)
  have hE₂ : ∀ i < 14, stackArg (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) i = pArg a i :=
    fun i hi => ((stackArg_call p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (pArg_sib S₂ hi)
  have bn : ∀ {s t : State}, SSib G a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.nB]
    exact sentry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKn hp.dOn hp.dns
      (by have := hp.wN; dsimp only; omega)
  have be : ∀ {s t : State}, SSib G a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.eB]
    exact sentry_bytes (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hst hM hp.dKe hp.dOe hp.des
      (by have := hp.wE; dsimp only; omega)
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.gpr (r := .rdi) (by decide),
        S₂.gpr (r := .rdi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .r8) (by decide),
        S₂.gpr (r := .r8) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .r9) (by decide),
        S₂.gpr (r := .r9) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · have hi := List.mem_range.mp hi
    rw [hE₁ i hi, hE₂ i hi]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn S₁ v₁.L.rsp hM₁, bn S₂ v₂.L.rsp hM₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be S₁ v₁.L.rsp hM₁, be S₂ v₂.L.rsp hM₂]

variable {privN : String} {privC : Prog isa}
  (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
  (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
  (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)

include hv hct hspC hdC in
theorem scall_ct : RelCT isa (Two (SAt G (SJP H))) (.call privN privC) (Two (SAt G (SJR H))) := by
  refine two_post (RelCT.callEx (k := chkContract) hv hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := priv_covers S₁.ps h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := priv_covers S₂.ps h₂.2.1 h₂.1.wr
    have hpub := scall_pub S₁ h₁ S₂ h₂
    obtain ⟨v₁, -, -, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, -, -, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    exact ⟨_, _, _, _, priv_pre S₁.ps v₁.L.rsp ha₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁,
      priv_pre S₂.ps v₂.L.rsp ha₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂, hpub, c₁, w₁, c₂, w₂,
      by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    refine WP.mono (priv_call hv hspC hdC hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ => ?_
    have R' := R.of_keep v.L.geo fun x hx => hk' x hx
    exact ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw trivial⟩

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH) (hc : PssChecks H.P H.D)

include hv hct hspC hdC K hc in
theorem smain_ct :
    RelCT isa (Two fun a t => SAt lk.G (SJ6 H) a t ∧ isa.eval .b t = some false) (signMain H privN privC)
      (Two (SAt lk.G (SJR H))) := by
  unfold signMain
  simp only [seqs]
  exact (signEnc_ct hH K lk hc).seq (privArgs_ct.seq (scall_ct hv hct hspC hdC))

theorem srestore_ct : RelCT isa (Two (SAt G (SJR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hv hct hspC hdC K hc in
theorem sbody_ct : RelCT isa (Two (SAt lk.G J0)) (signBody H privN privC) fun _ _ => True := by
  unfold signBody
  simp only [seqs]
  refine spro_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.sn0v, S₂.sn0v])
    (sfail_ct (Φ := fun a t => SAt lk.G (SJ1 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (RelCT.assoc ((semLen_ct hc.sign hH).seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
            S₁.seml, S₂.seml])
        (sfail_ct (Φ := fun a t => SAt lk.G (SJ4 H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        ((ssalt_ct hc.sign hH).seq (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
            rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
              h₂.2.2.2.2.1, S₁.seml, S₂.seml, S₁.ssl, S₂.ssl])
          (sfail_ct (Φ := fun a t => SAt lk.G (SJ6 H) a t ∧ isa.eval .b t = some true)
            fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
          (smain_ct hv hct hspC hdC hH K lk hc))))))).seq srestore_ct)

include hv hct hspC hdC K hc in
/-- `sign` is constant time. -/
theorem sign_ct : ConstantTime isa (signK lk.G).pre (signK lk.G).pub (sign H privN privC) :=
  RelCT.constantTime (valloc ((sbody_ct hv hct hspC hdC hH K lk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, spub_refl lk.G s₁, h₁⟩, e₁⟩,
      ⟨s₂, ⟨h₁, hpub, h₂⟩, e₂⟩⟩) fun _ _ h => h))

include hct hdC K hc in
/-- `sign` meets `Spec.RsaPss.signContract`. -/
theorem sign_verified (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧
      chkContract.post s s') (hC : SpSafe privC) :
    Verified X86_64.target (sign H privN privC) (Spec.RsaPss.signContract lk.G lk.G abi signStack) :=
  Verified.of_correct (k := signK lk.G) (sign_correct hH K lk hv hC hdC)
    (sign_ct hv hct hC hdC hH K lk hc) (sign_implies lk.G (sign_sat lk.G lk.mem))

end VG.Proof.RsaPss.X86_64
