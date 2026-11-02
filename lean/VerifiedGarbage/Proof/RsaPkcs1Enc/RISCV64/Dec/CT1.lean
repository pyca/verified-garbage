module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CTBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Kdk
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.CTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Kdk
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time up to `KDK`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCT1.lean`, `DecCT2.lean`): the setup and `D`,
by the taint analysis from the registers correctness fixes (`setup_ct`,
`dBuild_ct`), the call of `vg_rsa_private_checked` by its constant time
(`priv_ct`), and `DH` and `KDK`: their blocks by the taint analysis and their
calls by `shaInit_rel`, … (`hashD_ct`, `kdkMac_ct`). From the call on, two
runs are related by `PostAt` and the registers each call's arguments are in.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

/-- `PostAt` is kept by code writing registers `Post` does not keep. -/
theorem PostAt.only {s t u : State} (h : DPre s) (hp : PostAt s t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : PostAt s u :=
  let ⟨_, _, P⟩ := hp
  ⟨_, _, P.keep h o.keep (ws := []) (by rw [o.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr) hrs h7⟩

section
variable {e : Env}

/-- After the frame's allocation. -/
def PEnt (s u : State) : Prop := u = allocd frameBytes s

theorem setup_ct : RelCT isa (Rel e PEnt) (.block setup) (Rel e AtCall) :=
  rel_step [] (by taint_decide)
    (fun a b ha hb => ⟨by rw [ha, hb]; show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp], fun _ h => nomatch h⟩)
    fun _ _ h hu => hu ▸ setup_ok h

omit e in
theorem bytes_call {s u : State} (A : AtCall s u) {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ (kR s))
    (hl : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem p n = Spec.Rsa.bytesAt s.mem p n :=
  bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl

theorem priv_pub {u₁ u₂ : State} (A₁ : AtCall e.s₁ u₁) (A₂ : AtCall e.s₂ u₂) :
    (Spec.Rsa.privateCheckedContract RISCV64.abi Impl.Rsa.RISCV64.Priv.frameBytes).pub (callE e.s₁ u₁)
      (callE e.s₂ u₂) := by
  have m : ∀ {s u : State}, (callE s u).mem = u.mem := fun {_ _} => rfl
  refine Rsa.RISCV64.Priv.pub_of (by rw [show (callE e.s₁ u₁).sp = fb e.s₁ from A₁.sp,
    show (callE e.s₂ u₂).sp = fb e.s₂ from A₂.sp, e.fb_eq]) (fun r hr => ?_)
    (fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, e.arg (by omega)]) ?_ ?_
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, e.r]
    · rw [A₁.a1, A₂.a1, e.r]
    · rw [A₁.a2, A₂.a2, e.r]
    · rw [A₁.a3, A₂.a3, e.r]
    · rw [A₁.a4, A₂.a4, e.r]
    · rw [A₁.a5, A₂.a5, e.r]
    · rw [A₁.a6, A₂.a6, e.arg]
    · rw [A₁.a7, A₂.a7, e.r]
  · rw [m, m, callE_gpr _ _ (r := .a2), callE_gpr _ _ (r := .a3), callE_gpr _ _ (r := .a2),
      callE_gpr _ _ (r := .a3), A₁.a2, A₁.a3, A₂.a2, A₂.a3,
      bytes_call A₁ e.h₁.kn.symm (by have := e.h₁.wn; omega), bytes_call A₂ e.h₂.kn.symm (by have := e.h₂.wn; omega),
      e.S.n]
  · rw [m, m, callE_gpr _ _ (r := .a4), callE_gpr _ _ (r := .a5), callE_gpr _ _ (r := .a4),
      callE_gpr _ _ (r := .a5), A₁.a4, A₁.a5, A₂.a4, A₂.a5,
      bytes_call A₁ e.h₁.ke.symm (by have := e.h₁.we; omega), bytes_call A₂ e.h₂.ke.symm (by have := e.h₂.we; omega),
      e.S.e]

theorem priv_ct : RelCT isa (Rel e AtCall) privCall (Rel e AtRet) := by
  refine rel_post ?_ fun s u h A => call_ok h A fun v hv => hv
  unfold privCall
  exact RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct Rsa.RISCV64.Priv.code_ct
    fun u₁ u₂ ⟨A₁, A₂⟩ => ⟨callRd e.s₁, callWr e.s₁, callRd e.s₂, callWr e.s₂,
      Rsa.RISCV64.Priv.pre_of_preP (preP_entry e.h₁ A₁), Rsa.RISCV64.Priv.pre_of_preP (preP_entry e.h₂ A₂),
      priv_pub A₁ A₂, (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2, (call_covers e.h₂ A₂).1,
      (call_covers e.h₂ A₂).2⟩

/-! ## `D` -/

theorem dBuild_ct : RelCT isa (Rel e AtRet) dBuild (Rel e PostAt) :=
  rel_step [.s0, .s1, .s4, .s5] (by taint_decide)
    (fun a b A B => ⟨(post_agree (⟨A.toMid, rfl, rfl⟩ : Post e.s₁ _ _ a) ⟨B.toMid, rfl, rfl⟩).1, fun r hr => by
      have g := post_agree (⟨A.toMid, rfl, rfl⟩ : Post e.s₁ _ _ a) ⟨B.toMid, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [g.2.1, g.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1]⟩)
    fun s u h A => WP.mono (dBuild_ok h A) fun v hv => ⟨_, _, hv.toPost⟩

/-! ## `DH` -/

def H1 (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt
def H2 (s u : State) : Prop := UpdAt s u sSt (scA s sD) (s.gpr .a4).toNat ∧ u.gpr .a1 = BitVec.ofNat 64 0
def H3 (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧ u.gpr .a2 = scA s sDH ∧ u.gpr .a1 = s.gpr .a4

theorem pin_post {P : State → State → Prop} (hp : ∀ s u, P s u → PostAt s u) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6] := by decide) :
    ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b := fun a b ha hb => by
  obtain ⟨_, _, A⟩ := hp _ _ ha
  obtain ⟨_, _, B⟩ := hp _ _ hb
  have g := post_agree A B
  refine ⟨g.1, fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2]

theorem hashD_ct : RelCT isa (Rel e PostAt) hashD (Rel e PostAt) := by
  unfold hashD
  refine RelCT.seq (rel_step [.s0] (P' := H1) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · unfold shaInitArgs
    exact wp_addi (imm := sSt) fun v o f => wp_nil ⟨hp.only h o, by
      obtain ⟨_, _, P⟩ := hp; rw [f, P.s0]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaInit_rel (a := sSt) (by decide) fun _ _ h => h)
    fun s u h ⟨⟨_, _, P⟩, g⟩ => shaInit_ok h P (by decide) g fun w P' _ _ => ⟨_, _, P'⟩) ?_
  refine RelCT.seq (rel_step [.s0, .s1] (P' := H2) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · have hk := h.k2
    have lk : sD + (s.gpr .a4).toNat ≤ scrBytes := by unfold sD scrBytes; omega
    unfold shaUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 0) (by decide) fun v₂ p₂ f₂ =>
      wp_addi (imm := sD) (fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide))
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    obtain ⟨_, _, P⟩ := hp
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    exact ⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P.s0],
      by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P.s1],
      Covers.right (scCov h P₄.wr lk), scDisj (.inr (by decide)) lk (by decide), lowSc h (by decide) lk⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => scA s sD)
    (len := fun s => (s.gpr .a4).toNat) (e.scA_eq _) (by rw [e.r]) (fun _ _ h => h.1)
    fun _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
    fun s u h ⟨U, _⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun w P' _ _ => ⟨_, _, P'⟩
  refine RelCT.seq (rel_step [.s0, .s1] (P' := H3) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · unfold shaFinArgs
    refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_mov fun w₂ q₂ g₂ =>
      wp_addi (imm := sDH) (fun w₃ q₃ g₃ => wp_nil ?_) (by decide))
    have O : Only [.a0, .a1, .a2] u w₃ := (q₁.trans (q₂.trans q₃)).mono
    obtain ⟨_, _, P⟩ := hp
    exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [q₃.get .a0, q₂.get .a0, g₁, P.s0], by rw [g₃, q₂.get .s0, q₁.get .s0, P.s0],
      by rw [q₃.get .a1, g₂, q₁.get .s1, P.s1]⟩
  exact rel_post (shaFin_rel (a := sSt) (o := sDH) (by decide) (by decide) (.inl (by decide)) fun _ _ h => h)
    fun s u h ⟨⟨_, _, P⟩, g0, g2, _⟩ => shaFin_ok h P (by decide) (by decide) (.inl (by decide)) g0 g2
      fun w P' _ _ => ⟨_, _, P'⟩

/-! ## `KDK` -/

def MI (k : Nat) (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧ u.gpr .a1 = scA s sOuter ∧
  u.gpr .a2 = scA s k ∧ u.gpr .a3 = BitVec.ofNat 64 32
def K2 (s u : State) : Prop := UpdAt s u sSt (stackArg s 1) (s.gpr .a4).toNat ∧ u.gpr .a1 = BitVec.ofNat 64 64
def MF (o : Nat) (cnt : State → BitVec 64) (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧
  u.gpr .a1 = scA s sOuter ∧ u.gpr .a2 = cnt s ∧ u.gpr .a3 = scA s o

theorem macInitArgs_ct {P : State → State → Prop} (hp : ∀ s u, P s u → PostAt s u) {k : Nat} (hk : k < 2048)
    (hct : RelCT isa (Rel e P) (.block (macInitArgs k)) fun _ _ => True) :
    RelCT isa (Rel e P) (.block (macInitArgs k)) (Rel e (MI k)) :=
  rel_post hct fun s u h hu => by
    obtain ⟨_, _, P⟩ := hp _ _ hu
    exact macInitArgs_ok h P hk fun v P' a0 a1 a2 a3 _ _ => ⟨⟨_, _, P'⟩, a0, a1, a2, a3⟩

theorem macInit_ct {k : Nat} (hk : k + 32 ≤ scrBytes) (hk1 : sOuter + 96 ≤ k) :
    RelCT isa (Rel e (MI k)) macInitCall (Rel e PostAt) :=
  rel_post (macInit_rel hk hk1 fun _ _ h => h) fun s u h ⟨⟨_, _, P⟩, a0, a1, a2, a3⟩ =>
    macInit_ok h P (i := sSt) (u := sOuter) (k := k) (by decide) (by decide) hk (.inl (by decide))
      (.inr (by unfold sSt sOuter at *; omega)) (.inr hk1) a0 a1 a2 a3 fun w P' _ _ _ => ⟨_, _, P'⟩

theorem macFin_ct {o : Nat} (ho : o + 32 ≤ scrBytes) (ho1 : sOuter + 96 ≤ o) {cnt : State → BitVec 64}
    (hcnt : cnt e.s₁ = cnt e.s₂) : RelCT isa (Rel e (MF o cnt)) macFinCall (Rel e PostAt) :=
  rel_post (macFin_rel ho ho1 hcnt fun _ _ h => h) fun s u h ⟨⟨_, _, P⟩, a0, a1, _, a3⟩ =>
    macFin_ok h P (i := sSt) (u := sOuter) (o := o) (by decide) (by decide) ho (.inl (by decide))
      (.inl (by unfold sSt sOuter at *; omega)) (.inl ho1) a0 a1 a3 fun w P' _ _ => ⟨_, _, P'⟩

theorem kdkMac_ct : RelCT isa (Rel e PostAt) kdkMac (Rel e PostAt) := by
  unfold kdkMac
  refine RelCT.seq (macInitArgs_ct (fun _ _ h => h) (k := sDH) (by decide)
    (rel_of (rs := [.s0]) (by taint_decide) fun a b h => pin_post (fun _ _ h => h) [.s0] (by decide) a b h.1 h.2)) ?_
  refine RelCT.seq (macInit_ct (by decide) (by decide)) ?_
  refine RelCT.seq (rel_step [.s0, .s1, .s6] (P' := K2) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · have hk := h.k2
    unfold kdkUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
      wp_mov fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    obtain ⟨_, _, P⟩ := hp
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    exact ⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s6, p₁.get .s6, P.s6],
      by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P.s1], c_cov h P₄, c_sc h (by decide), c_low h (by decide)⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => stackArg s 1)
    (len := fun s => (s.gpr .a4).toNat) e.arg (by rw [e.r]) (fun _ _ h => h.1)
    fun _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
    fun s u h ⟨U, _⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun w P' _ _ => ⟨_, _, P'⟩
  refine RelCT.seq (rel_step [.s0, .s1] (P' := MF sKDK fun s => s.gpr .a4 + BitVec.ofNat 64 64) (by taint_decide)
    (pin_post (fun _ _ h => h) _) fun s u h hp => ?_) (macFin_ct (by decide) (by decide) (by rw [e.r]))
  unfold kdkFinArgs
  refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
    wp_addi (imm := 64) (fun w₃ q₃ g₃ => wp_addi (imm := sKDK) (fun w₄ q₄ g₄ => wp_nil ?_) (by decide))
    (by decide)) (by decide)) (by decide)
  have O : Only [.a0, .a1, .a2, .a3] u w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
  obtain ⟨_, _, P⟩ := hp
  exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
    by rw [q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P.s0], by rw [q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P.s0],
    by rw [q₄.get .a2, g₃, q₂.get .s1, q₁.get .s1, P.s1], by rw [g₄, q₃.get .s0, q₂.get .s0, q₁.get .s0, P.s0]⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
