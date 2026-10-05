import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBase

/-!
# RSASSA-PSS verification on x86-64: the public-key operation in two runs

After the checks (`J7`), `DB`'s slots and the public-key operation's
arguments (`dbPub_ct`), and the call (`call_ct`): its arguments are public in
both runs (the modulus, the exponent and their lengths, `EM`'s place and the
working space), and it is constant time by its contract.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The public words after the checks. -/
def K5 : List Nat := [17, 18, 19, 20, 21, 22, 25, 26, 35, 36, 37, 38]

/-- And with `DB`'s. -/
def KM : List Nat := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 35, 36, 37, 38]

theorem km_k5 {k : Nat} (h : k ∈ KM) (h23 : k ≠ 23) (h24 : k ≠ 24) : k ∈ K5 := by
  simp only [KM, K5, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega

theorem km_lt {k : Nat} (h : k ∈ KM) : k < nW := by
  simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega

variable (H) in
/-- After the checks: the salt's length fits, `rax = emLen - hLen - 2`. -/
def J7 (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s - (H.D + 2)) ∧
    t.cf = some (decide (veml s - (H.D + 2) < (vrdx s).toNat)) ∧ H.D + 2 ≤ veml s

variable (H) in
/-- Before the call. -/
def JC1 (s t : State) : Prop :=
  VS H s t KM [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) ∧ t.gpr .rdi = off (stackArg s 3) oEm ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx ∧ H.D + 2 ≤ veml s

variable (H) in
/-- After the call: the frame, the public words, what else `X` says. -/
def JM (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  VS H s t KM [] (X s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

theorem dbPub_ct : RelCT isa (Two fun a t => VAt G (J7 H) a t ∧ isa.eval .b t = some false)
    (.seq (.block dbSlots) (.block pubArgs)) (Two (VAt G (JC1 H))) := by
  obtain ⟨_, hc⟩ := vFixed.dbPub
  refine two_post (vtwo (G := G) (H := H) [17, 18, 19, 20, 21, 22, 26, 38] [.rax]
    (fun a => [(.rax, BitVec.ofNat 64 (veml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (fun k hk => by
      simp only [K5, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.veml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, hax, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have L := v.L
  have w : ∀ k ∈ K5, W k = vw H s k := hw
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R (w 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hM1 := vframe_keep hp v.wr L.rsp hM f1
  have g1 : ∀ j, j ≠ 23 → j ≠ 24 → upd (upd W 24 (BitVec.ofNat 64 (veml s - (H.D + 2) + 1))) 23
      (off (stackArg s 3) (oEm + vlo s)) j = W j := fun j h23 h24 => by simp [upd, h23, h24]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (pubArgs_ok L1 R1 (by rw [g1 17 (by decide) (by decide)]; exact w 17 (by decide))
      (by rw [g1 18 (by decide) (by decide)]; exact w 18 (by decide))
      (by rw [g1 19 (by decide) (by decide)]; exact w 19 (by decide))
      (by rw [g1 20 (by decide) (by decide)]; exact w 20 (by decide))
      (by rw [g1 22 (by decide) (by decide)]; exact w 22 (by decide))
      (by rw [g1 38 (by decide) (by decide)]; exact w 38 (by decide))))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_
  have hw1 : u1.wr = frR s :: s.wr := k1.2.2.trans v.wr
  refine ⟨s, S, ⟨L2, k2.2.2.trans hw1, ⟨V, W2, R2, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
    (k2.2.1.trans k1.2.1).trans hrd, vframe_keep hp hw1 L1.rsp hM1 f2,
    fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi), h2di, h2si, h2dx, h2cx, h2r8, h2r9,
    hok⟩
  have h4 : 4 ≤ k := by simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [hW2b k (km_lt hk) h4]
  by_cases h23 : k = 23
  · subst h23; simp [upd, vw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, vw, vdb]
    congr 1; omega
  rw [g1 k h23 h24]; exact w k (km_k5 hk h23 h24)

/-- The modulus and the exponent, at the call, as on entry. -/
theorem entry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (vwrR s) s.mem t.mem)
    {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact bytesAt_frame fSE (vin_apart hK hS) hl

theorem vArg_sib {a s : State} (S : VSib G a s) {i : Nat} : vArg s i = vArg a i := by
  unfold vArg
  split <;> simp only [S.gpr (r := .r9) (by decide), S.gpr (r := .rsi) (by decide), S.arg3, S.arg4]

theorem entry_n {a s t : State} (S : VSib G a s) (hst : t.gpr .rsp = fb s) (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat := by
  have hp := S.ps
  rw [← S.nB]
  exact entry_bytes (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) hst hM hp.dKn hp.dns
    (by have := hp.wN; dsimp only; omega)

theorem entry_e {a s t : State} (S : VSib G a s) (hst : t.gpr .rsp = fb s) (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  have hp := S.ps
  rw [← S.eB]
  exact entry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKe hp.des
    (by have := hp.wE; dsimp only; omega)

/-- The call's public data agree. -/
theorem call_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : VSib G a s₁) (h₁ : JC1 H s₁ t₁) (S₂ : VSib G a s₂)
    (h₂ : JC1 H s₂ t₂) :
    pubChkContract.pub (t₁.callEntry.withRegions (vRd s₁) (vWr s₁)) (t₂.callEntry.withRegions (vRd s₂) (vWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, -⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, -⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 4, stackArg (t₁.callEntry.withRegions (vRd s₁) (vWr s₁)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (vArg_sib S₁)
  have hE₂ : ∀ i < 4, stackArg (t₂.callEntry.withRegions (vRd s₂) (vWr s₂)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (vArg_sib S₂)
  have bn₁ := entry_n S₁ v₁.L.rsp hM₁
  have bn₂ := entry_n S₂ v₂.L.rsp hM₂
  have be₁ := entry_e S₁ v₁.L.rsp hM₁
  have be₂ := entry_e S₂ v₂.L.rsp hM₂
  rw [show pubChkContract.pub = VG.Proof.Bignum.X86_64.pubContract.pub from rfl]
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, by rw [hE₁ 0 (by decide), hE₂ 0 (by decide)], by rw [hE₁ 1 (by decide), hE₂ 1 (by decide)],
    by rw [hE₁ 2 (by decide), hE₂ 2 (by decide)], by rw [hE₁ 3 (by decide), hE₂ 3 (by decide)], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.arg3, S₂.arg3]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rsi) (by decide),
        S₂.gpr (r := .rsi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.gpr (r := .rdi) (by decide),
        S₂.gpr (r := .rdi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.gpr (r := .rsi) (by decide),
        S₂.gpr (r := .rsi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn₁, bn₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be₁, be₂]

variable {pubN : String} {pubC : Prog isa}
  (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
  (hct : ConstantTime isa pubContract.pre pubContract.pub pubC) (hspC : SpSafe pubC) (hdC : pubC.x86_64Depth = 0)

include hv hct hspC hdC in
theorem call_ct : RelCT isa (Two (VAt G (JC1 H))) (.call pubN pubC) (Two (VAt G (JM H fun _ _ _ => True))) := by
  refine two_post (RelCT.callEx (k := pubChkContract) hv hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := pub_covers S₁.ps h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := pub_covers S₂.ps h₂.2.1 h₂.1.wr
    exact ⟨_, _, _, _, pub_pre S₁.ps h₁.1.L.rsp h₁.2.2.2.1 h₁.2.2.2.2.1 h₁.2.2.2.2.2.1 h₁.2.2.2.2.2.2.1
      h₁.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.2.1,
      pub_pre S₂.ps h₂.1.L.rsp h₂.2.2.2.1 h₂.2.2.2.2.1 h₂.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1
      h₂.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.2.1, call_pub S₁ h₁ S₂ h₂, c₁, w₁, c₂, w₂,
      by rw [h₁.1.L.rsp, h₂.1.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    have hk2 := hp.k2
    refine WP.mono (pub_call hv hspC hdC hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ => ?_
    have hEm : oEm + (s.gpr .rsi).toNat ≤ oRsa := by unfold oEm oRsa; omega
    have R' := R.of_em v.L.geo hEm hk'
    exact ⟨s, S, ⟨v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr', wr'.trans v.wr, ⟨_, W, R', hw, trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, hok⟩

end VG.Proof.RsaPss.X86_64
