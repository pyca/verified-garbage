import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtBack

/-!
# RSASSA-PSS verification on x86-64: constant time, and `Verified`

The prologue, the checks on the modulus and the salt's length (their
branches are on public values: the modulus' first byte and length, the
expected salt length), what follows them (`main_ct`), and the epilogue, in
two runs whose entry states agree on the public data (`verify_ct`). With
`verify_correct`, `verify` meets `Spec.RsaPss.verifyContract`
(`verify_verified`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def K1 : List Nat := [17, 18, 19, 20, 21, 22, 37, 38]

variable (H) in
/-- After the prologue: the modulus' first byte, and ZF set if it is zero. -/
def J1 (s t : State) : Prop :=
  VS H s t K1 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

variable (H) in
/-- After `emLen`: CF set if it is too short. -/
def J4 (s t : State) : Prop :=
  VS H s t (K1 ++ [25, 26]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s) ∧ t.cf = some (decide (veml s < H.D + 2))

variable (H) in
/-- After the salt length's arguments. -/
def J5 (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧ t.gpr .rdx = vrdx s ∧
    H.D + 2 ≤ veml s

theorem pro_ct : RelCT isa (Two (VAt G J0)) (.block (verifyPrologue ++ n0)) (Two (VAt G (J1 H))) := by
  obtain ⟨_, hc⟩ := vFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 1 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
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
  refine WP.mono (verifyPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  have hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono (vn0_ok hp L1 R1 (by simp [vproW, upd]) k1.2.1 hM1) fun t2 ⟨k2, hm2, hax2, hz2⟩ =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k2.2.1.trans k1.2.1, hm2 ▸ hM1, hax2, hz2⟩
  simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vproW, upd, vw]

/-- A refusal. -/
theorem fail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s ks X, VSib G a s ∧ VS H s t ks [] X) :
    RelCT isa (Two Φ) verifyFail (Two (VAt G (JR H))) := by
  obtain ⟨_, hc⟩ := vFixed.fail
  have hv : ∀ a t, Φ a t → ∃ s, VSib G a s ∧ VS H s t [] [] fun _ _ => True := fun a t h => by
    obtain ⟨s, ks, X, S, v⟩ := hΦ a t h
    exact ⟨s, S, v.sub (fun _ h => by cases h) [] (fun _ hp => by cases hp) fun _ _ _ => trivial⟩
  refine two_post (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t h => let ⟨s, S, v⟩ := hv a t h; ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t h => ?_
  obtain ⟨s, S, v⟩ := hv a t h
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, v.keep k hm (by decide) fun _ hp => by cases hp⟩
  xrun [verifyFail]

theorem emLen_ct (hc : VerifyChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two fun a t => VAt G (J1 H) a t ∧ isa.eval .e t = some false) (.seq (.block smear) (emLen H))
      (Two (VAt G (J4 H))) := by
  obtain ⟨_, hc⟩ := hc.emLen
  refine two_post (vtwo (G := G) (H := H) [17] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (n0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.n0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have h0 : n0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine WP.seq (WP.mono (smear_ok t (x := n0v s) (BitVec.isLt _) h0 hax) fun t3 ⟨k3, hm3, hdx3, hz3⟩ => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 3) := v.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 3) V W := hm3 ▸ R
  refine WP.mono (WP.keepIn (by safe_by [emLen]) (by simp [emLen, Code.x86_64Depth])
    (emLen_ok (H := H) (by omega) L3 R3 (x := n0v s) (k := (s.gpr .rsi).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) (by omega) hdx3 hz3)) fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ =>
    ⟨s, S, ⟨L4, k4.2.2.trans (k3.2.2.trans v.wr), ⟨V, _, R4, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
      k4.2.1.trans (k3.2.1.trans hrd), vframe_keep hp (k3.2.2.trans v.wr) L3.rsp (hm3 ▸ hM) f4, hax4, hc4⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 25 ∧ k ≠ 26 := by simp only [K1, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp only [upd]; rw [ifn this.2, ifn this.1]; exact hw k hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp [upd, vw, vlo]

/-- `anyArgs`' first block. -/
theorem any1_ok {s : State} (hp : VPre G s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : Frame (vwrR s) s.mem u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) :
    WP isa (.block any1) u fun v => Lay v (fb s) S ∧ Keep [.rax] u v ∧ Rep v.mem (fb s) S V (upd W 36 (stackArg s 1)) ∧
      v.zf = some (decide ((stackArg s 2).setWidth 32 = 0)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 36) (by decide) (stackArg s 1)
  rw [show off (fb s) (8 * 36) = off (fb s) sSlen from rfl] at R1
  have hF := vfb_toNat hp
  have := hp.sp2
  have a1 := varg_read' hp hf (j := 1) (by decide)
  have a2 : (u.mem.writeW (off (fb s) sSlen) (stackArg s 1)).readW (off (fb s) (frameBytes + 8 + 8 * 2)) 32 =
      (stackArg s 2).setWidth 32 := by
    rw [readW32_low, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold sSlen frameBytes; omega))
      (by unfold frameBytes; omega) (by unfold sSlen; omega)) (by decide), varg_read' hp hf (j := 2) (by decide)]
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = u.mem.writeW (off (fb s) sSlen) (stackArg s 1) ∧
      v.zf = some (decide ((stackArg s 2).setWidth 32 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R1, hz⟩
  xrun [any1, arg, ea_sp, L.rsp, varg_in hp hrd (j := 1) (by decide), varg_in hp hrd (j := 2) (by decide) 4, a1, a2,
    L.st (d := sSlen) (by decide)]
  rw [BitVec.and_self, zext32_beq_zero]

variable (H) in
/-- Between `anyArgs`' blocks. -/
def JZ (s t : State) : Prop := VS H s t [] [] (fun _ _ => True) ∧ t.zf = some (decide ((stackArg s 2).setWidth 32 = 0))

theorem anyArgs_ct :
    RelCT isa (Two fun a t => VAt G (J4 H) a t ∧ isa.eval .b t = some false) anyArgs (Two (VAt G (J5 H))) := by
  obtain ⟨_, h1⟩ := vFixed.any1
  obtain ⟨_, hT⟩ := vFixed.anyT
  obtain ⟨_, hE⟩ := vFixed.anyE
  refine two_post ?_ fun a t ⟨⟨s, S, ⟨v, hrd, hM, _, hcf⟩⟩, hb⟩ => ?_
  · rw [anyArgs_eq]
    refine RelCT.seq (two_post (Ψ := VAt G (JZ H)) (vtwo (G := G) (H := H) [] [] (fun _ => [])
      (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (fun _ h => by cases h) _ (fun _ hp => by cases hp) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) h1) fun a t ⟨⟨s, S, ⟨v, hrd, hM, _⟩⟩, _⟩ => ?_)
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, _, z₁⟩ ⟨s₂, S₂, _, z₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, z₁, z₂, S₁.arg2, S₂.arg2])
        (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, v, _⟩, _⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
          (by decide) hT)
        (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, v, _⟩, _⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
          (by decide) hE))
    obtain ⟨V, W, R, -, -⟩ := v.W
    exact WP.mono (any1_ok S.ps v.L hrd hM R) fun u ⟨L', k', R', hz⟩ =>
      ⟨s, S, ⟨L', k'.2.2.trans v.wr, ⟨V, upd W 36 (stackArg s 1), R', (fun k (h : k ∈ ([] : List Nat)) => nomatch h),
        trivial⟩, fun _ hp => by cases hp⟩, hz⟩
  have hp := S.ps
  have hok : H.D + 2 ≤ veml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine WP.mono (WP.keepIn (by safe_by [anyArgs]) (by simp [anyArgs, Code.x86_64Depth])
    (anyArgs_ok hp v.L hrd hM R)) fun u ⟨⟨L', k', R', hdx⟩, f⟩ =>
    ⟨s, S, ⟨L', k'.2.2.trans v.wr, ⟨V, _, R', fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k'.2.1.trans hrd,
      vframe_keep hp v.wr v.L.rsp hM f, hdx, hok⟩
  by_cases h35 : k = 35
  · subst h35; simp [upd, vw]
  by_cases h36 : k = 36
  · subst h36; simp [upd, vw]
  simp only [upd]; rw [ifn h35, ifn h36]
  exact hw k (by simp only [K5, K1, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hk ⊢; omega)

theorem salt_ct (hc : VerifyChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two (VAt G (J5 H))) (.block ([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
      .alu .sub .rax (.reg .r8)] ++ saltFits H)) (Two (VAt G (J7 H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (vtwo (G := G) (H := H) [17, 26] [.rdx] (fun a => [(.rdx, vrdx a)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.vrdx]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hdx, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have := vlo_le s
  have L := v.L
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (veml s) ∧ u.mem = t.mem) ?_ rfl)
    fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), L.ld (d := sLo) (by decide), R.rd (d := sK) 17 rfl (by decide),
      R.rd (d := sLo) 26 rfl (by decide), hw 17 (by decide), hw 26 (by decide)]
    show s.gpr .rsi - BitVec.ofNat 64 (vlo s) = BitVec.ofNat 64 ((s.gpr .rsi).toNat - vlo s)
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .rsi).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.mono (saltFits_ok (H := H) (by omega) t6 (a := veml s) (b := vrdx s) hok (by unfold veml; omega) hax6
    (by rw [k6.gpr (by decide)]; exact hdx)) fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hm : t7.mem = t.mem := by rw [hm7, hm6]
  exact ⟨s, S, v.keep (k6.trans k7) hm (by decide) (fun _ hp => by cases hp), k7.2.1.trans (k6.2.1.trans hrd),
    hm ▸ hM, hax7, hc7, hok⟩

variable {pubN : String} {pubC : Prog isa}
  (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
  (hct : ConstantTime isa pubContract.pre pubContract.pub pubC) (hspC : SpSafe pubC) (hdC : pubC.x86_64Depth = 0)
  (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH) (hc : PssChecks H.P H.D)

include hv hct hspC hdC K hc in
theorem main_ct :
    RelCT isa (Two fun a t => VAt lk.G (J7 H) a t ∧ isa.eval .b t = some false) (verifyMain H pubN pubC)
      (Two (VAt lk.G (JR H))) := by
  unfold verifyMain
  simp only [seqs]
  exact RelCT.assoc (dbPub_ct.seq ((call_ct hv hct hspC hdC).seq (acc0_ct.seq ((mgf_ct hH K lk hc.hash1).seq
    (clearTop_ct.seq (posScan_ct.seq ((posCheck_ct hH hc.verify).seq (RelCT.assoc ((cyd_ct hH lk hc.verify).seq
      ((copyDb_ct hH hc.verify).seq ((shift_ct hH hc.verify).seq ((verifyNb_ct hH hc.verify).seq
        ((mhash_ct hH K hc.hash1).seq (cmpH_ct hH hc.verify))))))))))))))


theorem restore_ct : RelCT isa (Two (VAt G (JR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := vFixed.restore
  exact vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hv hct hspC hdC K hc in
theorem body_ct : RelCT isa (Two (VAt lk.G J0)) (verifyBody H pubN pubC) fun _ _ => True := by
  unfold verifyBody
  simp only [seqs]
  refine pro_ct.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.n0v, S₂.n0v])
    (fail_ct (Φ := fun a t => VAt lk.G (J1 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩) (RelCT.assoc ((emLen_ct hc.verify hH).seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
            S₁.veml, S₂.veml])
        (fail_ct (Φ := fun a t => VAt lk.G (J4 H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
        (anyArgs_ct.seq ((salt_ct hc.verify hH).seq (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
            rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
              h₂.2.2.2.2.1, S₁.veml, S₂.veml, S₁.vrdx, S₂.vrdx])
          (fail_ct (Φ := fun a t => VAt lk.G (J7 H) a t ∧ isa.eval .b t = some true)
            fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
          (main_ct hv hct hspC hdC hH K lk hc)))))))).seq restore_ct)

theorem valloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have a₁ : ∀ {s s' : State}, isa.push (.alloc frameBytes) s = some s' → s' = allocState frameBytes s :=
        fun h => by
          simp only [isa, push] at h
          split at h
          · cases h; rfl
          · cases h
      obtain rfl := a₁ p₁
      obtain rfl := a₁ p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

include hv hct hspC hdC K hc in
/-- `verify` is constant time. -/
theorem verify_ct : ConstantTime isa (verifyK lk.G).pre (verifyK lk.G).pub (verify H pubN pubC) :=
  RelCT.constantTime (valloc ((body_ct hv hct hspC hdC hH K lk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, vpub_refl lk.G s₁, h₁⟩, e₁⟩,
      ⟨s₂, ⟨h₁, hpub, h₂⟩, e₂⟩⟩) fun _ _ h => h))

include hct K hc in
/-- `verify` meets `Spec.RsaPss.verifyContract`. -/
theorem verify_verified (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧
      pubChkContract.post s s') (hC : pubC.allInstrs safeI = true) (hdC : pubC.x86_64Depth = 0) :
    Verified X86_64.target (verify H pubN pubC) (Spec.RsaPss.verifyContract lk.G lk.G abi verifyStack) :=
  Verified.of_correct (k := verifyK lk.G) (verify_correct hH K lk hv hC hdC)
    (verify_ct hv hct (safe_sp hC) hdC hH K lk hc) (verify_implies lk.G (verify_sat lk.G lk.mem))

include hH K in
/-- It writes `rsp` only in its frame's push and pop. -/
theorem verify_spSafe (hC : pubC.allInstrs safeI = true) :
    (verify H pubN pubC).all (fun i => !isa.writesSp i) = true := by
  have h := verify_safe hH K (pubN := pubN) hC
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at h
  exact Code.all_of_allInstrs h.1

end VG.Proof.RsaPss.X86_64
