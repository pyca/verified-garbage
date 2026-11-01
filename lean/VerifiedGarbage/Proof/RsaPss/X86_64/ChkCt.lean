module

public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkSaltBackCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.EncFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's check of an encoding on x86-64: constant time, and `Verified`

The prologue, the copy of the encoding, the salt length's arguments (the
branch on `any_salt_len`, which the runs' entry states agree on), the checks
of the lengths (on public values), verification's checks
(`ChkCtMid`, `ChkCtBack`, `ChkSaltBackCT`) and the epilogue, in two runs
whose entry states agree on the public data (`chk_ct`). With `chk_correct`,
`checkEncoding` meets `Proof.RsaPss.checkEncodingContract` (`chk_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-- The entry of the frame. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def KP : List Nat := [17, 21, 25, 26, 36, 37, 38]

variable (H) in
/-- After the prologue, and the copy. -/
def CJ1 (s t : State) : Prop :=
  VS H s t KP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ t.gpr .r9 = s.gpr .r9

variable (H) in
/-- After the salt length's arguments. -/
def CJ2 (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ t.gpr .rdx = vrdx s

variable (H) in
/-- After `fitH`: CF set if `emLen` is too short. -/
def CJ3 (s t : State) : Prop :=
  CJ2 H s t ∧ t.gpr .rax = BitVec.ofNat 64 (veml s) ∧ t.cf = some (decide (veml s < H.D + 2))

theorem pro_ct : RelCT isa (Two (VAt G J0)) (.block chkPrologue) (Two (VAt G (CJ1 H))) := by
  obtain ⟨_, hc⟩ := cFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 1 [.rdi, .rsi, .rdx, .rcx, .r8] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  refine WP.mono (chkPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ =>
    ⟨s, S, ⟨L1, k1.2.2, ⟨_, _, R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k1.2.1, frame_wrR f1,
      by rw [k1.gpr (by decide)]; rfl⟩
  have hel := hp.hel
  simp only [KP, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [proW', proW, upd, vw, cmask, vlo, hel]

theorem copyIn_ct : RelCT isa (Two (VAt G (CJ1 H))) copyIn (Two (VAt G (CJ1 H))) := by
  obtain ⟨_, hc⟩ := cFixed.copyIn
  refine two_post (vtwo (G := G) (H := H) [17, 21, 38] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, h9⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact WP.mono (WP.keepIn (by safe_by [copyIn]) (by exact Nat.zero_le 8)
    (copyIn_ok hp v.L R v.wr hrd (hw 17 (by decide)) (hw 38 (by decide)))) fun u ⟨⟨L', k', R'⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' hw trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
      (k'.gpr (by decide)).trans h9⟩

variable (H) in
/-- After `any_salt_len`'s test. -/
def CJZ (s t : State) : Prop :=
  VS H s t [] [] (fun _ _ => True) ∧ t.zf = some (decide ((s.gpr .r9).setWidth 32 = 0))

theorem anyReg_ct : RelCT isa (Two (VAt G (CJ1 H))) anyReg (Two (VAt G (CJ2 H))) := by
  refine two_post ?_ fun a t ⟨s, S, v, hrd, hM, h9⟩ => ?_
  · obtain ⟨_, h1⟩ := cFixed.any1
    obtain ⟨_, hT⟩ := cFixed.anyT
    obtain ⟨_, hE⟩ := cFixed.anyE
    unfold anyReg
    refine (two_post (Ψ := VAt G (CJZ H)) (vtwo (G := G) (H := H) [] [] (fun _ => [])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) h1) fun a t ⟨s, S, v, _, _, h9⟩ => ?_).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2, h₂.2, S₁.r9, S₂.r9])
        (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1⟩)
          (fun _ => rfl) (by decide) hT)
        (vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1⟩)
          (fun _ => rfl) (by decide) hE))
    refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧
        t'.zf = some (decide ((s.gpr .r9).setWidth 32 = 0))) (by
      xrun [h9]
      rw [BitVec.and_self, zext32_beq_zero]) rfl) fun t' ⟨⟨hm, hz⟩, k⟩ =>
      ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp)).sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ _ => trivial, hz⟩
  · obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    refine WP.mono (WP.keepIn (by safe_by [anyReg]) (by exact Nat.zero_le 8)
      (anyReg_ok v.L R (hw 36 (by decide)) h9)) fun u ⟨⟨L', k', R', hdx⟩, f⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' (fun k hk => ?_) trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
        by rw [hdx]; rfl⟩
    by_cases h35 : k = 35
    · subst h35; simp [upd, vw]
    simp only [upd]; rw [ifn h35]
    exact hw k (by simp only [K5, KP, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega)

theorem fit_ct (hc : HashChecks H.P H.D 1) (hH : HashOK H) :
    RelCT isa (Two (VAt G (CJ2 H))) (.block (fitH H)) (Two (VAt G (CJ3 H))) := by
  obtain ⟨_, hc⟩ := hc.fit
  refine two_post (vtwo (G := G) (H := H) [17] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hdx⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN; have hN := hH.N_le
  refine WP.mono (fitH_ok (H := H) (by omega) v.L R (k := veml s)
    (by rw [hw 17 (by decide)]; show s.gpr .rdx = _; rw [veml, vlo, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by unfold veml; omega)) fun t' ⟨k', hm, hax, hcf⟩ =>
    ⟨s, S, ⟨v.keep k' hm (by decide) (fun _ hp => by cases hp), k'.2.1.trans hrd, hm ▸ hM,
      (k'.gpr (by decide)).trans hdx⟩, hax, hcf⟩

/-- A refusal: 0. -/
theorem ret0_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib G a s ∧ VS H s t [] [] X) :
    RelCT isa (Two Φ) ret0 (Two (VAt G (JR H))) := by
  obtain ⟨_, hc⟩ := cFixed.ret0
  refine two_post (vtwo (G := G) (H := H) [] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) (by xrun [ret0]) rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, (v.keep k hm (by decide) (fun _ hp => by cases hp)).sub (by decide) [] (fun _ hp => by cases hp)
      fun _ _ _ => trivial⟩

theorem salt_ct (hc : VerifyChecks H.P H.D) (hH : HashOK H) :
    RelCT isa (Two fun a t => VAt G (CJ3 H) a t ∧ isa.eval .b t = some false)
      (.block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)), .alu .sub .rax (.reg .r8)] : List Instr) ++
        saltFits H)) (Two (VAt G (J7 H))) := by
  obtain ⟨_, hc⟩ := hc.salt
  refine two_post (vtwo (G := G) (H := H) [17, 26] [.rdx] (fun a => [(.rdx, vrdx a)])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.vrdx]; exact h.1.2.2.2) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, hb⟩ => ?_
  obtain ⟨⟨v, hrd, hM, hdx⟩, hax, hcf⟩ := h
  have hok : H.D + 2 ≤ veml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have L := v.L
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (veml s) ∧ u.mem = t.mem) ?_ rfl)
    fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), L.ld (d := sLo) (by decide), R.rd (d := sK) 17 rfl (by decide),
      R.rd (d := sLo) 26 rfl (by decide), hw 17 (by decide), hw 26 (by decide)]
    show s.gpr .rdx - BitVec.ofNat 64 (vlo s) = BitVec.ofNat 64 ((s.gpr .rdx).toNat - vlo s)
    rw [vlo, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.sub_zero _
  refine WP.mono (saltFits_ok (H := H) (by omega) t6 (a := veml s) (b := vrdx s) hok (by unfold veml; omega) hax6
    (by rw [k6.gpr (by decide)]; exact hdx)) fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hm : t7.mem = t.mem := by rw [hm7, hm6]
  exact ⟨s, S, v.keep (k6.trans k7) hm (by decide) (fun _ hp => by cases hp), k7.2.1.trans (k6.2.1.trans hrd),
    hm ▸ hM, hax7, hc7, hok⟩

theorem dbSlots_ct : RelCT isa (Two fun a t => VAt G (J7 H) a t ∧ isa.eval .b t = some false) (.block dbSlots)
    (Two (VAt G (JT H))) := by
  obtain ⟨_, hc⟩ := cFixed.dbSlots
  refine two_post (vtwo (G := G) (H := H) [26] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (veml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.veml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, hax, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have w : ∀ k ∈ K5, W k = vw H s k := hw
  refine WP.mono (dbSlots_ok v.L R (w 26 (by decide)) hax) fun u1 ⟨L1, k1, R1⟩ =>
    ⟨s, S, ⟨v.next L1 k1.2.2 R1 (fun k hk => ?_) trivial, k1.2.1.trans hrd, hok⟩⟩
  by_cases h23 : k = 23
  · subst h23; simp [upd, vw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, vw, vdb]
    congr 1; omega
  simp only [upd]; rw [ifn h24, ifn h23]; exact w k (km_k5 hk h23 h24)

theorem restore_ct : RelCT isa (Two (VAt G (JR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := cFixed.restore
  exact vtwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH) (hc : PssChecks H.P H.D)

include K hc in
theorem main_ct :
    RelCT isa (Two fun a t => VAt lk.G (J7 H) a t ∧ isa.eval .b t = some false) (chkMain H) (Two (VAt lk.G (JR H))) := by
  unfold chkMain
  simp only [seqs]
  exact dbSlots_ct.seq (acc0_ct.seq ((mgf_ct hH K lk hc.hash1).seq (clearTop_ct.seq ((scanCheck_ct hH hc.verify).seq
    (saltBack_ct hH K lk hc)))))

include K hc in
theorem body_ct : RelCT isa (Two (VAt lk.G J0)) (chkBody H) fun _ _ => True := by
  unfold chkBody
  simp only [seqs]
  exact pro_ct.seq (copyIn_ct.seq (anyReg_ct.seq ((fit_ct hc.hash1 hH).seq ((two_ite
      (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
        rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2, h₂.2.2,
          S₁.veml, S₂.veml])
      (ret0_ct (Φ := fun a t => VAt lk.G (CJ3 H) a t ∧ isa.eval .b t = some true)
        fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      ((salt_ct hc.verify hH).seq (two_ite
        (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
            h₂.2.2.2.2.1, S₁.veml, S₂.veml, S₁.vrdx, S₂.vrdx])
        (ret0_ct (Φ := fun a t => VAt lk.G (J7 H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        (main_ct hH K lk hc)))).seq restore_ct))))

include K hc in
/-- `checkEncoding` is constant time. -/
theorem chk_ct : ConstantTime isa (chkK lk.G).pre (chkK lk.G).pub (checkEncoding H) :=
  RelCT.constantTime (valloc ((body_ct hH K lk hc).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨Pre.of lk.G h₁, vpub_refl lk.G s₁, Pre.of lk.G h₁⟩, e₁⟩,
      ⟨s₂, ⟨Pre.of lk.G h₁, hpub, Pre.of lk.G h₂⟩, e₂⟩⟩) fun _ _ h => h))

include K hc in
/-- `checkEncoding` meets `Proof.RsaPss.checkEncodingContract`. -/
theorem chk_verified :
    Verified X86_64.target (checkEncoding H) (Proof.RsaPss.checkEncodingContract lk.G lk.G abi chkStack) :=
  Verified.of_correct (k := chkK lk.G) (chk_correct hH K lk) (chk_ct hH K lk hc) (chk_implies lk.G (chk_sat lk.G lk.mem))

end VG.Proof.RsaPss.X86_64.Chk
