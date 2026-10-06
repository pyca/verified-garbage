import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCTBase
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, to `D`

The setup (`setup_ct`), from two entry states whose public data agree, the
private-key operation (`priv_ct`), and `D` (`dBuild_ct`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpec (S + 1)).pre s₁ ∧ (decSpec (S + 1)).pre s₂ ∧ (decSpec (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

/-- After the setup. -/
abbrev CtxReady : Inv := fun L g vv m₀ t => Ctx L g vv m₀ t ∧ Ready L t

theorem setup_ct (S : Nat) : RelCT isa (Entered S) (.block setup) (Two S CtxReady) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay (S + 1) s₂ = lay (S + 1) s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, hsp]
  obtain ⟨hn, he⟩ := leak_split hl (by rw [bytesAt_length, bytesAt_length, h4])
  refine ⟨ht, ⟨lay (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, rfl, ⟨?_, ?_⟩, y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]

theorem priv_pub' {L : Lay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : CtxReady L g₁ v₁ m₁ a) (hb : CtxReady L g₂ v₂ m₂ b) :
    (privK S).pub (a.callEntry.withRegions (privRd L) (privWr L))
      (b.callEntry.withRegions (privRd L) (privWr L)) := by
  have aa := priv_args ha.1 (privRd L) (privWr L)
  have ab := priv_args hb.1 (privRd L) (privWr L)
  simp only [privK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.2.x0, ha.2.x1, ha.2.x2, ha.2.x3, ha.2.x4, ha.2.x5, ha.2.x6, ha.2.x7, hb.2.x0, hb.2.x1, hb.2.x2, hb.2.x3,
    hb.2.x4, hb.2.x5, hb.2.x6, hb.2.x7, ha.1.sp, hb.1.sp, true_and]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := ab
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := aa
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    exacts [c0.trans b0.symm, c1.trans b1.symm, c2.trans b2.symm, c3.trans b3.symm, c4.trans b4.symm,
      c5.trans b5.symm, c6.trans b6.symm, c7.trans b7.symm, c8.trans b8.symm, c9.trans b9.symm,
      c10.trans b10.symm, c11.trans b11.symm, absurd hi (by omega)]
  · rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L)]; exact hk.1
  · rw [ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L)]; exact hk.2

theorem priv_ct (v : PrivImpl) : RelCT isa (Two v.S CtxReady) (.call v.name v.code) (Two v.S Called) :=
  two_wp (fun e => RelCT.call (n := v.name) v.correct v.ct (privRd e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ =>
      ⟨priv_pre' hL hP f₁.1 f₁.2, priv_pre' hL hP f₂.1 f₂.2, priv_pub' hL hk f₁ f₂, (covers_priv f₁.1).1,
        (covers_priv f₁.1).2, (covers_priv f₂.1).1, (covers_priv f₂.1).2⟩)
    fun _ _ _ _ _ hL hP h => priv_call v hL hP h.1 h.2

/-! ## `D` -/

theorem regs_eq {a b : State} {rs : List (Reg × BitVec 64)} (ha : ∀ p ∈ rs, a.gpr p.1 = p.2)
    (hb : ∀ p ∈ rs, b.gpr p.1 = p.2) : ∀ r ∈ rs.map (·.1), a.gpr r = b.gpr r := fun r hr => by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact (ha p hp).trans (hb p hp).symm

theorem dBuild_ct (S : Nat) :
    RelCT isa (Two S Called) dBuild (Two S fun L g vv m₀ t => ∃ R EM, DB L g vv m₀ R EM t) := by
  refine (two (Ψ := fun L g vv m₀ t => ∃ R EM, ZInv L g vv m₀ R EM 0 t) [] (by taint_decide)
    (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ => ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL _ h => WP.mono (dPtrs₁_inv hL h) fun _ h' => ⟨_, _, h'⟩).seq
    ((two (Ψ := fun L g vv m₀ t => ∃ R EM, ZInv L g vv m₀ R EM L.k.toNat t) [.x11, .x12] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ => ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm]⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (zeroLoop_ok hL h) fun _ h' => ⟨_, _, h'⟩).seq
    ((two (Ψ := fun L g vv m₀ t => ∃ R EM, CInv L g vv m₀ R EM 0 t) [] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ =>
        ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (dPtrs₂_inv hL h) fun _ h' => ⟨_, _, h'⟩).seq
    (two [.x14, .x11, .x12] (by taint_decide)
      (fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, f₁⟩ ⟨_, _, f₂⟩ => ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        exacts [f₁.x14.trans f₂.x14.symm, f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm]⟩)
      fun _ _ _ _ _ hL _ ⟨_, _, h⟩ => WP.mono (copyLoop_ok hL h) fun _ h' => ⟨_, _, cinv_db hL h'⟩)))

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
