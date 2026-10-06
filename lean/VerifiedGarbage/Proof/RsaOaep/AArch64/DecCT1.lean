import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCTBase

/-!
# RSAES-OAEP decryption on AArch64: constant time, to the decoding

The prologue and the private-key operation's arguments (`head_ct`), from two
entry states whose public data agree; the private-key operation
(`priv_ct`); its result to its slot and the check of `k` (`resK_ct`); and
the failure for a short `k` (`decFail_tr`).
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl privK)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The prologue and the arguments -/

/-- Ready for the private-key operation. -/
abbrev PrivReady : Inv := fun L g vv m₀ t =>
  Ctx L g vv m₀ t ∧ Ready L t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Slots L W ∧ CallArgs L W

theorem head_ok {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (decSpec Hs Gs P).pre s) (hP : 16 ≤ P) :
    WP isa (.block (decPrologue ++ privArgs)) (entered s) (PrivReady (lay P s) s.gpr s.v s.mem) := by
  have hL := lay_ok h
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok h) fun t ⟨hc, h9, hpw⟩ => ?_
  rw [privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem (lay P s).Q (lay P s).scr (fun o => t.mem (off (lay P s).scr o))
      (fun j => word t.mem (lay P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots (lay P s) (privW (lay P s) fun j => word t.mem (lay P s).Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (privR_ok hL hP hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  refine ⟨hc2, hr2, _, _, hm2 ▸ R1, hS1, ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩⟩

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (Hs Gs : Spec.Mgf1.Hash) (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpec Hs Gs (S + 1)).pre s₁ ∧ (decSpec Hs Gs (S + 1)).pre s₂ ∧ (decSpec Hs Gs (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

theorem head_ct (Hs Gs : Spec.Mgf1.Hash) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Entered Hs Gs S) (.block (decPrologue ++ privArgs)) (Two S PrivReady) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := head_ok h₁ (by omega)
  obtain ⟨_, u₂, x₂, y₂⟩ := head_ok h₂ (by omega)
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

/-! ## The private-key operation -/

theorem priv_args_eq {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {a : State}
    (ha : PrivReady L g vv m₀ a) (rd wr : List Region) :
    ∀ i < 12, stackArg (a.callEntry.withRegions rd wr) i =
      [L.p, L.pl, L.q, L.ql, L.dp, L.dpl, L.dq, L.dql, L.qi, L.qil, L.scr + BitVec.ofNat 64 8192,
        L.sl - BitVec.ofNat 64 1024].getD i 0 := by
  obtain ⟨hc, -, V, W, R, -, hA⟩ := ha
  intro i hi
  rw [stackArg_ce, hc.sp, show a.mem.readW (L.Q + BitVec.ofNat 64 (8 * i)) 64 = W i from
    R.fr i (by unfold nW frameBytes; omega)]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  exacts [hA.p, hA.args 0 (by decide), hA.args 1 (by decide), hA.args 2 (by decide), hA.args 3 (by decide),
    hA.args 4 (by decide), hA.args 5 (by decide), hA.args 6 (by decide), hA.args 7 (by decide),
    hA.args 8 (by decide), hA.s10, hA.s11, absurd hi (by omega)]

theorem priv_pub' {L : DLay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : PrivReady L g₁ v₁ m₁ a) (hb : PrivReady L g₂ v₂ m₂ b) :
    (privK S).pub (a.callEntry.withRegions (privRd L) (privWr L))
      (b.callEntry.withRegions (privRd L) (privWr L)) := by
  have aa := priv_args_eq ha (privRd L) (privWr L)
  have ab := priv_args_eq hb (privRd L) (privWr L)
  simp only [privK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.2.1.x0, ha.2.1.x1, ha.2.1.x2, ha.2.1.x3, ha.2.1.x4, ha.2.1.x5, ha.2.1.x6, ha.2.1.x7, hb.2.1.x0, hb.2.1.x1,
    hb.2.1.x2, hb.2.1.x3, hb.2.1.x4, hb.2.1.x5, hb.2.1.x6, hb.2.1.x7, ha.1.sp, hb.1.sp, true_and]
  refine ⟨fun i hi => (aa i hi).trans (ab i hi).symm, ?_, ?_⟩
  · rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L)]; exact hk.1
  · rw [ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L)]; exact hk.2

/-- After the call. -/
abbrev CalledI : Inv := fun L g vv m₀ t => ∃ W, Called L g vv m₀ W t ∧ Slots L W

theorem priv_ct (v : PrivImpl) : RelCT isa (Two v.S PrivReady) (.call v.name v.code) (Two v.S CalledI) :=
  two_wp (fun e => RelCT.call (n := v.name) v.correct v.ct (privRd e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ => by
      obtain ⟨c₁, r₁, V₁, W₁, R₁, s₁, A₁⟩ := f₁
      obtain ⟨c₂, r₂, V₂, W₂, R₂, s₂, A₂⟩ := f₂
      exact ⟨priv_pre' hL hP c₁ r₁ R₁ A₁, priv_pre' hL hP c₂ r₂ R₂ A₂,
        priv_pub' hL hk ⟨c₁, r₁, V₁, W₁, R₁, s₁, A₁⟩ ⟨c₂, r₂, V₂, W₂, R₂, s₂, A₂⟩,
        (covers_priv hL c₁).1, (covers_priv hL c₁).2, (covers_priv hL c₂).1, (covers_priv hL c₂).2⟩)
    fun _ _ _ _ _ hL hP ⟨hc, hr, V, W, R, hS, hA⟩ => WP.mono (priv_call v hL hP hc hr R hA) fun _ h => ⟨W, h, hS⟩

/-! ## The result and the check of `k` -/

/-- After the check of `k`: `x11` all ones iff `k < 2 hLen + 2`. -/
abbrev KReady (D : Nat) : Inv := fun L g vv m₀ t =>
  In L g vv m₀ (fun _ t => t.gpr .x11 = if 2 * D + 2 ≤ L.k.toNat then 0 else BitVec.allOnes 64) t

theorem resK_ct {H : Hash} (hD : H.D ≤ 64) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S CalledI)
      (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK H))
      (Two S (KReady H.D)) :=
  two (Φ := CalledI) [] (check_of_zImm (τ := Taint.ofRegs []) (c := .block (([.logic .orr .w .x0 .x0 .x0,
    .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK H)) (c' := .block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0,
    .str .x .x0 .x9 sR] : List Instr) ++ chkK gH)) rfl (by taint_decide))
    (fun _ _ _ _ _ _ _ _ _ _ ⟨_, f₁, _⟩ ⟨_, f₂, _⟩ => ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun L g vv m₀ t hL hP ⟨W, hcl, hS⟩ => by
      have hP16 : 16 ≤ L.P := by omega
      have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact WP.mono (resK_ok (H := H) (hcl.ctx.lay hL hP16 hcl.rep hS.scr) hcl.rep hk3 hL.k1024 (by omega))
        fun u ⟨_, S4, R4, x11⟩ => In.of_step hL hP16 hcl.ctx S4 nil_ws R4
          (hS.of fun j _ _ h3 => by simp only [upd]; rw [ifn (by omega)]) x11

/-! ## A short `k` -/

theorem zeroHead_ok {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block [.ldrSp .x11 sOut, .ldrSp .x12 sK, .movz .x .x13 0 0]) t fun u => u.sp = t.sp ∧
      u.gpr .x11 = L.out ∧ u.gpr .x12 = L.k ∧ u.gpr .x13 = 0 := by
  have Ly := hc.lay hL hP R hS.scr
  have h152 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 152) 8 := Ly.ld (d := 152) (by decide)
  have h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) hS.out
  have rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  oaep_run [sOut, sK, h152, h168, Ly.sp, ro, rk]
  and_intros <;> first | trivial | rfl

theorem decFail_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ _ => True) decFail fun _ _ => True := by
  refine RelCT.seq (R := PW S e fun _ _ => True) (pw_seq (X' := fun _ _ => True) [.x11, .x12, .x13]
    (fun r => if r = .x11 then e.L.out else if r = .x12 then e.L.k else 0)
    (by taint_decide) (by taint_decide)
    (fun _ _ _ t _ _ hL hP hc R hS _ => WP.mono (zeroHead_ok hL (by omega) hc R hS) fun u ⟨hs, x11, x12, x13⟩ =>
      ⟨hs, by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [*]⟩)
    fun g vv m₀ t V W hL hP hc R hS _ => ?_) ?_
  · have hP16 : 16 ≤ e.L.P := by omega
    have Ly := hc.lay hL hP16 R hS.scr
    have O := hc.outAt hL hP16 hS
    have hk : W 21 = BitVec.ofNat 64 e.L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact WP.mono (zeroOut_ok Ly R O.ho hk (by have := hL.k64; omega) hL.k1024 O.hw O.hnw O.ha)
      fun u ⟨_, Su, Ru, _⟩ => In.of_step hL hP16 hc Su (fun r h => by simp at h; exact .inl h) Ru hS trivial
  · show RelCT isa _ (.block ([.ldrSp .x11 sMl] ++ (.str .x .x13 .x11 0 :: faultBit))) _
    refine RelCT.block_append (pw_seq_tr [.x11] (fun _ => e.L.ml) (by taint_decide) (by taint_decide)
      fun g vv m₀ t V W hL hP hc R hS _ => ?_)
    have Ly := hc.lay hL (by omega) R hS.scr
    have h216 : InRegions (t.rd ++ t.wr) (e.L.Q + BitVec.ofNat 64 216) 8 := Ly.ld (d := 216) (by decide)
    have rml := R.rd8 (d := 216) (k := 27) rfl (by decide) hS.ml
    oaep_run [sMl, h216, Ly.sp, rml]
    and_intros <;> first | trivial | rfl | (intro r hr; rw [List.mem_singleton.mp hr]; rfl)

end VG.Proof.RsaOaep.AArch64.Dec
