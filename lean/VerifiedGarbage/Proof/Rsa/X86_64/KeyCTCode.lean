import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode

/-!
# `vg_rsa_check_key` on x86-64: constant time

Runs that agree on the public data (the pointers, the lengths, `n` and
`e`) leak the same: `entry` from `rsp` and then the working space's base,
`expCheck` from `e`'s pointer and length, the branch on `e`'s validity,
the modulus' check from `n`'s pointer and length, the branch on its
validity, and `main` (`keyCode_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit invalid)

/-- The public data of `vg_rsa_check_key`. -/
structure KCPub where
  m : MPub
  rsp : Addr
  ep : Addr
  ecx : BitVec 64
  nb : List Byte
  eb : List Byte

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KCPub) (s : State) : Prop :=
  keyContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 10 = p.m.kp.B ∧ (stackArg s 11).toNat * 8 = p.m.kp.Z ∧
    (s.gpr .rsi).toNat = p.m.k ∧ s.gpr .rdi = p.m.np ∧ s.gpr .rdx = p.ep ∧ s.gpr .rcx = p.ecx ∧
    s.gpr .r8 = p.m.kp.pd ∧ (s.gpr .r9).toNat = p.m.kp.dl ∧ stackArg s 0 = p.m.kp.pp ∧
    (stackArg s 1).toNat = p.m.kp.pl ∧ stackArg s 2 = p.m.kp.pq ∧ (stackArg s 3).toNat = p.m.kp.ql ∧
    stackArg s 4 = p.m.kp.pdp ∧ stackArg s 6 = p.m.kp.pdq ∧ stackArg s 8 = p.m.kp.pqi ∧ keyN s = p.nb ∧
    keyE s = p.eb ∧ p.m.kp.w = (p.m.k + 7) / 8

theorem KRel.B {p : KCPub} {s : State} (h : KRel p s) : stackArg s 10 = p.m.kp.B := h.2.2.1

theorem keyEntry_split : entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++ entry.drop 1 :=
  rfl

/-- After `entry`'s first instruction. -/
def KC1 (p : KCPub) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .r11 = p.m.kp.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block (entry.drop 1)) t (EntryPost s (stackArg s 10))

/-- After `entry`. -/
def KC2 (p : KCPub) (t : State) : Prop := ∃ s, KRel p s ∧ EntryPost s (stackArg s 10) t

/-- After `expCheck`. -/
def KC3 (p : KCPub) (t : State) : Prop :=
  ∃ s t₁, KRel p s ∧ t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)) ∧ AfterExp s t₁ t

/-- After the stores, for a valid `e`. -/
def KC3s (p : KCPub) (t : State) : Prop :=
  ∃ s t₁ t₂, KRel p s ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true ∧ AfterExp s t₁ t₂ ∧
    t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧
    t.mem = t₂.mem.writeW (off (stackArg s 10) (8 * sEv)) (t₂.gpr .r11) ∧ Keep [.rdx, .rcx] t₂ t

/-- After the modulus' check, for a valid `e`. -/
def KC4 (p : KCPub) (t : State) : Prop :=
  ∃ s t₁ t₂ t₃, KRel p s ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.m.k) ∧ AfterInv s t₁ t₂ t₃ t

theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two KC2) ?_ (RelCT.seq (R := Two KC3) ?_ ?_)
  · rw [keyEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := keyArgs_of hs.1
    have hZ := c.hZ
    have := c.k1
    have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 10) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 88 })] ++ entry.drop 1)) s
        (EntryPost s (stackArg s 10)) := by
      rw [← keyEntry_split]; exact keyEntry_ok rfl hw c.ha c.hsep
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.B, (k.gpr (by decide)).trans hs.2.1, hw⟩
  · refine two_piece [.r8, .r9] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.r8, h₂.r8, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.r9, h₂.r9, c₁.2.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h₁⟩
    have c := keyArgs_of hs.1
    refine WP.mono (expK_ok c h₁) fun t' ⟨hz, hm, h11, k⟩ => ⟨s, t, hs, ?_, h₁, hm, h11, k⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, heb, -⟩ := hs
    rw [hz, heb]
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, z₁, _⟩ ⟨_, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    exact two_taint [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, c₁, _, e₁⟩, _⟩ ⟨⟨σ₂, _, c₂, _, e₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁.rdi, e₂.rdi, c₁.B, c₂.B]) (by taint_decide)
  simp only [seqs]
  refine RelCT.seq (R := Two KC4) (RelCT.block_append (RelCT.seq (R := Two KC3s) ?_ ?_)) ?_
  · refine two_piece [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, c₁, _, e₁⟩, _⟩ ⟨⟨σ₂, _, c₂, _, e₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁.rdi, e₂.rdi, c₁.B, c₂.B]) (by taint_decide) ?_
    rintro p t ⟨⟨s, t₁, hs, hz, e⟩, he⟩
    have c := keyArgs_of hs.1
    have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true := by
      simp only [eval, hz] at he; simpa using he
    exact WP.mono (storesK_ok c e) fun t' ⟨hdx, hcx, hm, k⟩ => ⟨s, t₁, t, hs, hv, e, hdx, hcx, hm, k⟩
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, _, _, c₁, _, _, d₁, x₁, _⟩ ⟨σ₂, _, _, c₂, _, _, d₂, x₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [d₁, d₂, c₁.2.2.2.2.2.1, c₂.2.2.2.2.2.1]
      · rw [x₁, x₂, ← ofNat_toNat64 (σ₁.gpr .rsi), ← ofNat_toNat64 (σ₂.gpr .rsi), c₁.2.2.2.2.1, c₂.2.2.2.2.1])
      (by taint_decide) ?_
    rintro p t ⟨s, t₁, t₂, hs, hv, e, hdx, hcx, hm, k⟩
    have c := keyArgs_of hs.1
    refine WP.mono (invalidK_ok c e hdx hcx hm k) fun t' ⟨hz, h⟩ => ⟨s, t₁, t₂, t, hs, hv, ?_, h⟩
    obtain ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, -, hnb, -, -⟩ := hs
    rw [hz, hnb, hk]
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · exact two_taint [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, _, _, c₁, _, _, h₁⟩, _⟩ ⟨⟨σ₂, _, _, _, c₂, _, _, h₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi, c₁.B, c₂.B]) (by taint_decide)
  · have toM : ∀ p t, KC4 p t ∧ isa.eval .ne t = some false → M0 p.m t := by
      rintro p t ⟨⟨s, t₁, t₂, t₃, hs, hv, hz, h⟩, he⟩
      have c := keyArgs_of hs.1
      obtain ⟨-, -, hB, hZ, hk, hnp, -, -, hpd, hdl, hpp, hpl, hpq, hql, hpdp, hpdq, hpqi, hnb, heb, hw⟩ := hs
      have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat = true := by
        simp only [eval, hz] at he; rw [hnb, hk]; simpa using he
      rw [← heb] at hv
      have := h.mainPre c hv hm
      rw [hB, hZ, hk, hnp, hpd, hpp, hpq, hpdp, hpdq, hpqi] at this
      exact ⟨_, _, _, _, _, _, _, _, this, hw, by rw [bytesAt_length, hdl], by rw [bytesAt_length, hpl],
        by rw [bytesAt_length, hql]⟩
    exact main_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h)
      fun _ _ h => h

/-- The public data of a state. -/
def kcpubOf (s : State) : KCPub :=
  ⟨⟨⟨stackArg s 10, (stackArg s 11).toNat * 8, ((s.gpr .rsi).toNat + 7) / 8, s.gpr .r8, stackArg s 0, stackArg s 2,
    stackArg s 4, stackArg s 6, stackArg s 8, (s.gpr .r9).toNat, (stackArg s 1).toNat, (stackArg s 3).toNat⟩,
    s.gpr .rdi, (s.gpr .rsi).toNat⟩, s.gpr .rsp, s.gpr .rdx, s.gpr .rcx, keyN s, keyE s⟩

/-- `vg_rsa_check_key` is constant time but for `n` and `e`. -/
theorem keyCode_constantTime : ConstantTime isa keyContract.pre keyContract.pub code := by
  refine RelCT.constantTime (keyCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨kcpubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, congrArg (·.toNat * 8) a11.symm, congrArg BitVec.toNat (r .rsi (by decide)),
      r .rdi (by decide), r .rdx (by decide), r .rcx (by decide), r .r8 (by decide),
      congrArg BitVec.toNat (r .r9 (by decide)), a0.symm, congrArg BitVec.toNat a1.symm, a2.symm,
      congrArg BitVec.toNat a3.symm, a4.symm, a6.symm, a8.symm, hn.symm, he.symm, rfl⟩

end VG.Proof.Rsa.X86_64
