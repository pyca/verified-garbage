import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecArgs
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCT1

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, `DH` and `KDK`

Inside the pieces that call SHA-256's and HMAC's functions, two runs in a
layout are related by `PW`: each keeps `Post` (for some result and `EM`) and
satisfies `X`, which fixes the registers the next piece's addresses and
arguments depend on as functions of the layout. Each block is checked by the
taint analysis (`pw_blk`) and each call is the same call in both runs
(`Calls.init_rel` …): `hashD_ct`, `kdkMac_ct`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress}

/-- Two runs in the layout of `e`, each with `Post` and `X`. -/
def PW (S : Nat) (e : Env) (X : State → Prop) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = S + 1 ∧ (∃ R EM, Post e.L e.g₁ e.v₁ e.m₁ R EM a) ∧ (∃ R EM, Post e.L e.g₂ e.v₂ e.m₂ R EM b) ∧
    X a ∧ X b

/-- What a piece keeps of `Post`, and establishes. -/
abbrev PWStep (S : Nat) (e : Env) (c : Prog isa) (X X' : State → Prop) : Prop :=
  ∀ g vv m₀ R EM (t : State), e.L.Ok → e.L.P = S + 1 → Post e.L g vv m₀ R EM t → X t →
    WP isa c t fun u => (∃ R EM, Post e.L g vv m₀ R EM u) ∧ X' u

theorem pw_wp {S : Nat} {e : Env} {c : Prog isa} {X X' : State → Prop}
    (hct : RelCT isa (PW S e X) c fun _ _ => True) (hw : PWStep S e c X X') : RelCT isa (PW S e X) c (PW S e X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, ⟨R₁, E₁, f₁⟩, ⟨R₂, E₂, f₂⟩, x₁, x₂⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw _ _ _ _ _ s₁ hL hP f₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw _ _ _ _ _ s₂ hL hP f₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, hL, hP, z₁.1, z₂.1, z₁.2, z₂.2⟩

/-- A block checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_blk {S : Nat} {e : Env} {c : Prog isa} {X X' : State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, X a → X b → ∀ r ∈ rs, a.gpr r = b.gpr r) (hw : PWStep S e c X X') :
    RelCT isa (PW S e X) c (PW S e X') :=
  pw_wp (RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨_, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩, x₁, x₂⟩ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun r hr => hag _ _ x₁ x₂ r (Taint.mem_ofRegs.mp hr)⟩) h) hw

theorem pw_sp {S : Nat} {e : Env} {X : State → Prop} {a b : State} (h : PW S e X a b) : a.sp = b.sp := by
  obtain ⟨_, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩, _, _⟩ := h
  exact f₁.ctx.sp.trans f₂.ctx.sp.symm

/-! ## `DH = SHA256(D)` -/

/-- The registers `shaUpdArgs` sets. -/
def XU (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = 0 ∧ t.gpr .x2 = scA L sD ∧ t.gpr .x3 = L.k ∧ t.gpr .x4 = scA L sWork

/-- The registers `shaFinArgs` sets. -/
def XF (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = L.k ∧ t.gpr .x2 = scA L sDH ∧ t.gpr .x3 = scA L sWork

theorem hashD_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (hashD (HH v)) fun _ _ => True := by
  refine (pw_blk (X' := fun t => t.gpr .x0 = scA e.L sSt) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t hL _ hc _ =>
      WP.mono (shaInitArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, by show u.gpr .x0 = _; simp only [x0, hc.ctx.kept.scr]⟩).seq ?_
  refine (pw_wp (X' := fun _ => True)
    (Proof.Pbkdf2.Md.AArch64.Calls.init_rel (OK v).stream (st := scA e.L sSt)
      fun a b h => by
        obtain ⟨hL, _, ⟨_, _, ha⟩, ⟨_, _, hb⟩, xa, xb⟩ := h
        exact ⟨xa, xb, initA hL ha, initA hL hb, ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc hx => WP.mono (initW (v := v) hL (by omega) hc hx) fun u hu => ⟨hu.1, trivial⟩).seq ?_
  refine (pw_blk (X' := XU e.L) [] (by taint_decide) (fun _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun g vv m₀ R EM t hL _ hc _ => WP.mono (shaUpdArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, by simp only [x0, hc.ctx.kept.scr], x1, by simp only [x2, hc.ctx.kept.scr],
        by simp only [x3, hc.ctx.kept.k], by simp only [x4, hc.ctx.kept.scr]⟩).seq ?_
  have hk := fun (hL : e.L.Ok) => hL.k1024
  have upA : ∀ (hL : e.L.Ok) (hP : 16 ≤ e.L.P) {g vv m₀ R EM} {t : State}, Post e.L g vv m₀ R EM t → XU e.L t →
      Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs (OK v).stream t (scA e.L sSt) (scA e.L sD) (scA e.L sWork) e.L.k.toNat :=
    fun hL hP {_ _ _ _ _ _} hc ⟨x0, _, x2, x3, x4⟩ => updA hL hP hc x0 x2 (by rw [x3]) x4
      (Covers.right (scCov hL hc.ctx (by have := hL.k1024; unfold sD scrBytes; omega)))
      (fun a l hal => scD hL (.inr (by unfold sD; omega)) (by have := hL.k1024; unfold sD scrBytes; omega)
        (by unfold scrBytes; omega))
      (stkD hL hP (by have := hL.k1024; unfold sD scrBytes; omega))
  refine (pw_wp (X' := fun _ => True)
    (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel (OK v).stream fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, xa, xb⟩ := h
      exact ⟨upA hL (by omega) ha xa, upA hL (by omega) hb xb, xa.2.1.trans xb.2.1.symm,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc hx => WP.mono (updW (v := v) hL (by omega) hc (upA hL (by omega) hc hx))
      fun u hu => ⟨hu.1, trivial⟩).seq ?_
  refine (pw_blk (X' := XF e.L) [] (by taint_decide) (fun _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun g vv m₀ R EM t hL _ hc _ => WP.mono (shaFinArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, by simp only [x0, hc.ctx.kept.scr], by simp only [x1, hc.ctx.kept.k],
        by simp only [x2, hc.ctx.kept.scr], by simp only [x3, hc.ctx.kept.scr]⟩).seq ?_
  exact Proof.Pbkdf2.Md.AArch64.Calls.fin_rel (OK v).stream fun a b h => by
    obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := h
    exact ⟨finA (o := sDH) hL (by omega) ha (by decide) (by decide) a0 a2 a3,
      finA (o := sDH) hL (by omega) hb (by decide) (by decide) b0 b2 b3, a1.trans b1.symm,
      ha.ctx.sp.trans hb.ctx.sp.symm⟩

/-! ## HMAC's pieces

`G` is a fact about the frame's words from `oI` on (the counters), which no
piece changes. -/

/-- `G` holds of states with the same frame words from `oI` on. -/
def SlotsPred (L : Lay) (G : State → Prop) : Prop :=
  ∀ t u : State, G t → (∀ d, oI ≤ d → d + 8 ≤ frameBytes →
    u.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64) → G u

/-- The registers `macInitArgs key` sets. -/
def XI (key : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = scA L sOuter ∧ t.gpr .x2 = scA L key ∧ t.gpr .x3 = BitVec.ofNat 64 32 ∧
    t.gpr .x4 = scA L sWork

theorem macArgs_pw {S : Nat} {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) (key : Nat) (hk : key < 4096)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs []) (.block (macInitArgs key)) hc).isSome = true) :
    RelCT isa (PW S e G) (.block (macInitArgs key)) (PW S e fun t => G t ∧ XI key e.L t) :=
  pw_blk [] h (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc hx =>
    WP.mono (macInitArgs_ok hc.ctx.sp hc.slots key hk) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
      ⟨⟨R, EM, hc.same hs⟩, hG t u hx fun _ _ _ => by rw [hs.mem], by simp only [x0, hc.ctx.kept.scr],
        by simp only [x1, hc.ctx.kept.scr], by simp only [x2, hc.ctx.kept.scr], x3,
        by simp only [x4, hc.ctx.kept.scr]⟩

theorem hinit_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {key : Nat}
    (hk1 : 1024 ≤ key) (hk2 : key + 32 ≤ scrBytes) :
    RelCT isa (PW S e fun t => G t ∧ XI key e.L t) (.call (HH v).hmacInitN (HH v).hmacInit) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Pbk.hinit_rel (OK v) (hI v) fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨hinitA hL (by omega) ha hk1 hk2 a0 a1 a2 a3 a4, hinitA hL (by omega) hb hk1 hk2 b0 b1 b2 b3 b4,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, x1, x2, x3, x4⟩ =>
      WP.mono (hinitW (v := v) hL (by omega) hc (hinitA hL (by omega) hc hk1 hk2 x0 x1 x2 x3 x4)) fun u hu =>
        ⟨hu.1, hG t u hx hu.2⟩

/-- The registers before `update` of `n` bytes at `d`. -/
def XUp (d : Addr) (n : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = BitVec.ofNat 64 64 ∧ t.gpr .x2 = d ∧ (t.gpr .x3).toNat = n ∧
    t.gpr .x4 = scA L sWork

theorem upd_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {d : Addr} {n : Nat}
    (hcd : e.L.Ok → ∀ g vv m₀ R EM (t : State), Post e.L g vv m₀ R EM t → Covers [⟨d, n⟩] (t.rd ++ t.wr))
    (hds : e.L.Ok → ∀ a l, a + l ≤ 1024 → Region.Disjoint ⟨d, n⟩ ⟨scA e.L a, l⟩)
    (hdk : e.L.Ok → e.L.P = S + 1 → (below e.L.Q 16).Disjoint ⟨d, n⟩) :
    RelCT isa (PW S e fun t => G t ∧ XUp d n e.L t) (.call (HH v).updN (HH v).updC) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Calls.upd_rel (OK v).stream fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨updA hL (by omega) ha a0 a2 a3 a4 (hcd hL _ _ _ _ _ _ ha) (hds hL) (hdk hL hP),
        updA hL (by omega) hb b0 b2 b3 b4 (hcd hL _ _ _ _ _ _ hb) (hds hL) (hdk hL hP), a1.trans b1.symm,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, _, x2, x3, x4⟩ =>
      WP.mono (updW (v := v) hL (by omega) hc (updA hL (by omega) hc x0 x2 x3 x4 (hcd hL _ _ _ _ _ _ hc) (hds hL)
        (hdk hL hP))) fun u hu => ⟨hu.1, hG t u hx hu.2⟩

/-- The registers before HMAC's `finalize` to `scratch + o` with the count `cnt`. -/
def XHF (o : Nat) (cnt : BitVec 64) (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = scA L sSt ∧ t.gpr .x1 = scA L sOuter ∧ t.gpr .x2 = cnt ∧ t.gpr .x3 = scA L o ∧
    t.gpr .x4 = scA L sWork

theorem hfin_pw {S : Nat} (hS : 15 ≤ S) {e : Env} {G : State → Prop} (hG : SlotsPred e.L G) {o : Nat}
    {cnt : BitVec 64} (ho1 : 1024 ≤ o) (ho2 : o + 32 ≤ scrBytes) :
    RelCT isa (PW S e fun t => G t ∧ XHF o cnt e.L t) (.call (HH v).hmacFinN (HH v).hmacFin) (PW S e G) :=
  pw_wp (Proof.Pbkdf2.Md.AArch64.Pbk.hfin_rel (OK v) (hF v) (cnt := cnt) fun a b h => by
      obtain ⟨hL, hP, ⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨_, a0, a1, a2, a3, a4⟩, ⟨_, b0, b1, b2, b3, b4⟩⟩ := h
      exact ⟨a2 ▸ hfinA hL (by omega) ha ho1 ho2 a0 a1 a3 a4, b2 ▸ hfinA hL (by omega) hb ho1 ho2 b0 b1 b3 b4,
        ha.ctx.sp.trans hb.ctx.sp.symm⟩)
    fun g vv m₀ R EM t hL hP hc ⟨hx, x0, x1, _, x3, x4⟩ =>
      WP.mono (hfinW (v := v) hL (by omega) hc ho2 (hfinA hL (by omega) hc ho1 ho2 x0 x1 x3 x4)) fun u hu =>
        ⟨hu.1, hG t u hx hu.2⟩

/-! ## `KDK` -/

theorem kdkMac_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ => True) (kdkMac (HH v)) fun _ _ => True := by
  have hG : SlotsPred e.L fun _ => True := fun _ _ _ _ => trivial
  refine (macArgs_pw hG sDH (by decide) (by taint_decide)).seq (((hinit_pw (v := v) hS hG (key := sDH) (by decide)
    (by decide)).mono (fun _ _ h => by
      obtain ⟨hL, hP, a, b, ⟨_, xa⟩, ⟨_, xb⟩⟩ := h
      exact ⟨hL, hP, a, b, ⟨trivial, xa⟩, ⟨trivial, xb⟩⟩) fun _ _ h => h).seq ?_)
  refine ((pw_blk (X' := fun t => True ∧ XUp e.L.inp e.L.k.toNat e.L t) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc _ =>
      WP.mono (kdkUpdArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, trivial, by simp only [x0, hc.ctx.kept.scr], x1, by simp only [x2, hc.ctx.kept.inp],
          by simp only [x3, hc.ctx.kept.k], by simp only [x4, hc.ctx.kept.scr]⟩)).seq ?_
  refine ((upd_pw (v := v) hS hG
    (fun _ _ _ _ _ _ _ hc => Covers.left (Covers.of_mem fun r hr => by
      rw [List.mem_singleton.mp hr, hc.ctx.rd]; simp))
    (fun hL a l hal => (hL.sR _ (ro_INP e.L)).symm.sub_right (sub_trans (scSub (by unfold scrBytes; omega))
      hL.sc_sub))
    (fun hL hP => (hL.kR _ (ro_INP e.L)).sub_left (below_low hL (by omega)))).seq ?_)
  refine ((pw_blk (X' := fun t => True ∧ XHF sKDK (e.L.k + BitVec.ofNat 64 64) e.L t) [] (by taint_decide)
    (fun _ _ _ _ _ h => absurd h List.not_mem_nil) fun g vv m₀ R EM t _ _ hc _ =>
      WP.mono (kdkFinArgs_ok hc.ctx.sp hc.slots) fun u ⟨hs, x0, x1, x2, x3, x4⟩ =>
        ⟨⟨R, EM, hc.same hs⟩, trivial, by simp only [x0, hc.ctx.kept.scr], by simp only [x1, hc.ctx.kept.scr],
          by simp only [x2, hc.ctx.kept.k], by simp only [x3, hc.ctx.kept.scr],
          by simp only [x4, hc.ctx.kept.scr]⟩)).seq ?_
  exact (hfin_pw (v := v) hS hG (o := sKDK) (by decide) (by decide)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The pieces -/

theorem hashD_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, DB L g vv m₀ R EM t) (hashD (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM, HD L g vv m₀ R EM t) :=
  two_wp (fun e => (hashD_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (hashD_ok hL (by omega) h) fun _ h' => ⟨_, _, h'⟩

theorem kdkMac_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ R EM, HD L g vv m₀ R EM t) (kdkMac (HH v))
      (Two S fun L g vv m₀ t => ∃ R EM, KD L g vv m₀ R EM t) :=
  two_wp (fun e => (kdkMac_tr hS e).mono (fun _ _ ⟨hL, hP, _, ⟨_, _, f₁⟩, ⟨_, _, f₂⟩⟩ =>
      ⟨hL, hP, ⟨_, _, f₁.post⟩, ⟨_, _, f₂.post⟩, trivial, trivial⟩) fun _ _ h => h)
    fun _ _ _ _ _ hL hP ⟨_, _, h⟩ => WP.mono (kdkMac_ok hL (by omega) h) fun _ h' => ⟨_, _, h'⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
