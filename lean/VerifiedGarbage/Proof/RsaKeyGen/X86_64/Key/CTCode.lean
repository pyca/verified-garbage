import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.CTOut

/-!
# An RSA key from its primes on x86-64: constant time

Runs that agree on the arguments, `e` and the status leak the same
(`keyCode_constantTime`): the entry from `rsp`, the stack arguments and the
working space's base; the pieces from there (`front_ct`); and the branch on
`d` too small, whose condition correctness ties to the status (`front_zf`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)
open VG.Spec.Rsa (bytesAt)

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KP) (s : State) : Prop := keyPre s ∧ (keyIn s).pub = p.q ∧ (keyIn s).st = p.st

/-- After `entry`'s first instruction. -/
def KC1 (p : KP) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .r11 = p.q.B ∧ t.gpr .rsp = p.q.sp ∧
    WP isa (.block (entry.drop 1 ++ head)) t (KS (keyIn s) s.mem)

theorem keyEntry_split : entry ++ head = ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
    (entry.drop 1 ++ head) := rfl

/-- `entry` and `head`. -/
theorem start_ct : RelCT isa (Two KRel) (.block (entry ++ head)) (Two (KG NF)) := by
  rw [keyEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (congrArg KQ.sp h₁.2.1).trans (congrArg KQ.sp h₂.2.1).symm) (by taint_decide) ?_)
    (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, ⟨hpre, he, hst⟩, _, _, hw⟩ => WP.mono hw fun u hu =>
        ⟨keyIn s, s.mem, he, hst, hu, (keyCtx_of hpre).L, (keyCtx_of hpre).O, trivial⟩))
  intro p s ⟨hpre, he, hst⟩
  have c := keyCtx_of hpre
  have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 88 })] ++ (entry.drop 1 ++ head))) s
      (KS (keyIn s) s.mem) := by
    rw [← keyEntry_split]; exact keyStart_k c
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
    (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
      ⟨s, ⟨hpre, he, hst⟩, h11.trans (congrArg KQ.B he), (k.gpr (by decide)).trans (congrArg KQ.sp he), hw⟩

/-- From the loads to `smallMask`. -/
theorem front_ct : RelCT isa (Two (KG NF))
    (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ [.block [.store (hdr kEv) .rbx]]))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask)))))))
    (Two (KG NF)) := by
  refine rs_app (R := Two (KG EvOK)) (by simp [loadA]) (by simp [order, ltA]) ?_ ?_
  · refine rs_app (by simp [loadA]) (by simp [loadA]) loadAP_ct ?_
    exact rs_app (by simp [loadA]) (by simp [loadE]) loadAQ_ct loadE_ct
  refine rs_app (by simp [order, ltA]) (by simp [decTo]) order_ct ?_
  refine rs_app (by simp [decTo]) (by simp [decTo]) decP_ct ?_
  refine rs_app (by simp [decTo]) (by simp [lcmPart, phi]) decQ_ct ?_
  refine rs_app (by simp [lcmPart, phi]) (by simp) lcmPart_ct ?_
  exact rs_app (by simp) (by simp [smallMask, constA]) dPart_ct smallMask_ct

/-- `WP` for every `a` of a family, from one: runs are deterministic. -/
theorem wp_all {c : Prog isa} {s : State} {α : Type} {P : α → Prop} {Q : α → State → Prop} (a₀ : α) (h₀ : P a₀)
    (h : ∀ a, P a → WP isa c s (Q a)) : WP isa c s fun t => ∀ a, P a → Q a t := by
  obtain ⟨tr, t, e, -⟩ := h a₀ h₀
  refine ⟨tr, t, e, fun a ha => ?_⟩
  obtain ⟨_, _, e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- After `smallMask`: a mask in `kOk`, and ZF clear exactly for the status 2. -/
abbrev Zf : KIn → State → Prop := fun I t => KokM I t ∧ t.zf = some (!decide (I.st = 2))

/-- `smallMask`'s ZF, from correctness: clear exactly when `d ≤ 2^(8 pl)`,
the status 2. -/
theorem front_zf {I : KIn} {m₀ : Mem} {t : State} (F : Front I m₀ t) :
    KS I m₀ t ∧ Zf I t := by
  refine ⟨F.ks, ?_⟩
  obtain ⟨ok, hok, hiff, hzf⟩ := F.zf
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  refine ⟨⟨ok, hok⟩, ?_⟩
  rw [hzf]
  refine congrArg (fun b => some (!b)) ?_
  have hW : 8 * I.pl = 16 * I.pl / 2 := by omega
  have hst : I.st = 2 ↔ ∃ d, Spec.Rsa.inverse I.E I.L = some d ∧ d ≤ 2 ^ (8 * I.pl) := by
    simp only [KIn.st]
    constructor
    · intro h2
      unfold Spec.RsaKeyGen.keyOp at h2
      generalize hk : Spec.RsaKeyGen.keyFromPrimes (16 * I.pl) (Spec.Rsa.os2ip I.eb) (Spec.Rsa.os2ip I.pb)
        (Spec.Rsa.os2ip I.qb) = r at h2
      unfold Spec.RsaKeyGen.keyFromPrimes at hk
      have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
        by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
      rw [hswap] at hk
      dsimp only at hk
      rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, ← hW] at hk
      rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
      · rw [hi] at hk; subst hk; simp [Spec.RsaKeyGen.keyStatus] at h2
      · rw [hi] at hk
        dsimp only at hk
        by_cases hd : d ≤ 2 ^ (8 * I.pl)
        · exact ⟨d, rfl, hd⟩
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hd)] at hk
          obtain ⟨x, rfl⟩ : ∃ x, r = .inl x := by
            rw [← hk]
            split
            · exact ⟨_, rfl⟩
            · split <;> exact ⟨_, rfl⟩
          cases x <;> simp [Spec.RsaKeyGen.keyStatus] at h2
    · rintro ⟨d, hd, hsm⟩
      rw [keyOp_inr (by
        unfold Spec.RsaKeyGen.keyFromPrimes
        have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
          by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
        rw [hswap]
        dsimp only
        rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, ← hW]
        dsimp only
        rw [ite_eq_left hsm])]
      rfl
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  rw [show (8 * I.pl) = 8 * I.pl from rfl]
  cases hc : ok'
  · rw [hc] at hiff
    rw [Bool.and_false]
    refine (decide_eq_false fun h => ?_).symm
    obtain ⟨d, hd, _⟩ := hst.mp h
    exact absurd (hiff.mp ⟨d, hd⟩) (by simp)
  · rw [hc] at hiff
    obtain ⟨d, hd⟩ := hiff.mpr rfl
    rw [Bool.and_true, hdd d hd]
    exact decide_eq_decide.mpr ⟨fun h => hst.mpr ⟨d, hd, h⟩, fun h => by
      obtain ⟨d', hd', h'⟩ := hst.mp h
      rw [hd] at hd'; cases hd'; exact h'⟩

/-- The whole code. -/
theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by
  rw [code_eq]
  refine rs_app (R := Two (KG NF)) (by simp) (by simp [loadA]) start_ct ?_
  refine rs_app (R := Two (KG Zf)) (by simp [loadA]) (by simp) ?_ ?_
  · -- The front, and ZF from correctness.
    refine (RelCT.wpDep front_ct (F := fun σ t => ∀ a : KIn × Mem, (KS a.1 a.2 σ ∧ KLens a.1) →
        KS a.1 a.2 t ∧ Zf a.1 t) fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, ⟨p, h₁, h₂⟩, f₁, f₂⟩ => ?_
    · obtain ⟨I, m₀, -, -, hk, L, -⟩ := h₁
      exact wp_all (I, m₀) ⟨hk, L⟩ fun a ⟨hk', L'⟩ => WP.mono (front_k hk' L') fun t ⟨F, _⟩ => front_zf F
    · obtain ⟨I, m₀, -, -, hk, L, -⟩ := h₂
      exact wp_all (I, m₀) ⟨hk, L⟩ fun a ⟨hk', L'⟩ => WP.mono (front_k hk' L') fun t ⟨F, _⟩ => front_zf F
    obtain ⟨I₁, m₁, he₁, hs₁, hk₁, L₁, O₁, -⟩ := h₁
    obtain ⟨I₂, m₂, he₂, hs₂, hk₂, L₂, O₂, -⟩ := h₂
    obtain ⟨k₁, z₁⟩ := f₁ (I₁, m₁) ⟨hk₁, L₁⟩
    obtain ⟨k₂, z₂⟩ := f₂ (I₂, m₂) ⟨hk₂, L₂⟩
    exact ⟨p, ⟨I₁, m₁, he₁, hs₁, k₁, L₁, O₁, z₁⟩, ⟨I₂, m₂, he₂, hs₂, k₂, L₂, O₂, z₂⟩⟩
  -- The branch on the status 2.
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨I₁, _, _, hs₁, _, _, _, -, z₁⟩ := h₁
    obtain ⟨I₂, _, _, hs₂, _, _, _, -, z₂⟩ := h₂
    simp only [eval, z₁, z₂, hs₁, hs₂]
  · exact zeros_ct.mono (fun _ _ ⟨p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩ =>
      ⟨p, EG.of_kg (h₁.imp fun _ _ => trivial), EG.of_kg (h₂.imp fun _ _ => trivial)⟩) fun _ _ h => h
  · exact keyPart_ct.mono (fun _ _ ⟨p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩ =>
      ⟨p, h₁.imp fun _ h => ⟨trivial, h.1⟩, h₂.imp fun _ h => ⟨trivial, h.1⟩⟩) fun _ _ h => h

/-- Byte lists with the same values. -/
theorem bytes_eq_of_toNat : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, bytes_eq_of_toNat h.2]

/-- The public data of a state. -/
def kpubOf (s : State) : KP := ⟨(keyIn s).pub, (keyIn s).st⟩

/-- `vg_rsa_keygen_key` is constant time but for `e` and the status. -/
theorem keyCode_constantTime : ConstantTime isa keyCtr.pre keyCtr.pub code := by
  refine RelCT.constantTime (keyCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨kpubOf s₁, ⟨h₁, rfl, rfl⟩, h₂, ?_, ?_⟩)
    fun _ _ h => h)
  · obtain ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, ha, hl⟩ := hp
    simp only [keyLeak] at hl
    have hlen : ((bytesAt s₁.mem (arg s₁ 8) (arg s₁ 9).toNat).map (·.toNat)).length =
        ((bytesAt s₂.mem (arg s₂ 8) (arg s₂ 9).toNat).map (·.toNat)).length := by
      simp only [List.length_map, bytesAt_length, ha 9 (by decide)]
    obtain ⟨he, -⟩ := List.append_inj hl hlen
    have hwr : s₂.wr = s₁.wr := by
      have w₁ := h₁.2.2.1
      have w₂ := h₂.2.2.1
      rw [w₁, w₂]
      simp only [hdi, hsi, hdx, hcx, h8, h9, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
        ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 10 (by decide), ha 11 (by decide)]
    simp only [kpubOf, keyIn, KIn.pub, KQ.mk.injEq]
    exact ⟨(ha 10 (by decide)).symm, by rw [ha 11 (by decide)], by rw [h9], hdi.symm, hdx.symm, h8.symm,
      (ha 0 (by decide)).symm, (ha 2 (by decide)).symm, (ha 4 (by decide)).symm, (ha 6 (by decide)).symm,
      (ha 8 (by decide)).symm, by rw [ha 9 (by decide)], (bytes_eq_of_toNat he).symm, hwr, hsp.symm⟩
  · obtain ⟨-, -, -, -, -, -, -, ha, hl⟩ := hp
    simp only [keyLeak] at hl
    have hlen : ((bytesAt s₁.mem (arg s₁ 8) (arg s₁ 9).toNat).map (·.toNat)).length =
        ((bytesAt s₂.mem (arg s₂ 8) (arg s₂ 9).toNat).map (·.toNat)).length := by
      simp only [List.length_map, bytesAt_length, ha 9 (by decide)]
    obtain ⟨-, hs⟩ := List.append_inj hl hlen
    simp only [List.cons.injEq, and_true] at hs
    exact hs.symm

end VG.Proof.RsaKeyGen.X86_64.Key
