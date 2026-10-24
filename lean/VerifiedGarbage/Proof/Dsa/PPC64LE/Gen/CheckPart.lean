module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.CheckCall
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PX
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pieces
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GPow
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: checking p‖q‖g

`checkPart_vp`: p (at `sPBE`), q (at `sQ`) and g (at `sG`) copied side by
side to `sPacked`, checked by a verified `vg_dsa_check_parameters`
(`CheckOk`): `fStatus` := 1 if `Spec.Dsa.checkParametersBytes` accepts them.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A claim copied to `dst`, the claims apart from it kept. -/
theorem copyCl_vp {dst src n : Nat} {bs : List Byte} (hs : (src, bs) ∈ c.cl) (hl : bs.length = n) (hn : 0 < n)
    (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15) (hs15 : src < 2 ^ 15) (hdE : hEnd ≤ dst) (hdK : dst + n ≤ pB)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst) (hcl : ∀ x ∈ c.cl, Apart dst n x) :
    VP (St G c X) (copyS dst src n) (St G { c with cl := (dst, bs) :: c.cl } X) := by
  refine copyS_vp (c := fun _ => c) (fun σ s h => h.1) hn hn15 hd15 hs15 (fun σ s h => ?_) (fun σ s h => ?_) hsep
    fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
  · have ⟨pb, pk⟩ := h.1.gi.pBig
    exact ⟨hdE, .inl (by simp only [List.length_replicate]; omega), by simp only [List.length_replicate]; omega⟩
  · have := (h.1.clOk _ hs).2.2; rw [hl] at this; exact this
  · have hf : c.cl.filter (fun x => decide (Apart dst n x)) = c.cl :=
      List.filter_eq_self.mpr fun x hx => decide_eq_true (hcl x hx)
    rw [hf] at h'
    have ⟨pb, pk⟩ := h.gi.pBig
    have b := h.sb _ hs
    simp only at b
    have e' : Spec.Rsa.bytesAt t.mem (G.sa dst) bs.length = bs := by rw [hl, e, ← hl]; exact b
    exact h'.addCl e' ⟨hdE, .inl (show dst + bs.length ≤ kB G.pLen by omega),
      show dst + bs.length ≤ G.scrLen * 8 by omega⟩

/-- The check's arguments. -/
theorem cargs_vp :
    VP (St G c X) (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
        scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)])
      (fun σ s => St G c X σ s ∧ CArgs G s) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
        scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)]), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  obtain ⟨_, w15, _, _, _, _, n15⟩ := ck_sizes h.gi.lens
  have hp15 : G.pLen < 2 ^ 15 := by rcases h.gi.lens3 with e | e | e <;> rw [e] <;> decide
  have hq15 : G.qLen < 2 ^ 15 := by rcases h.gi.lens with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> decide
  have wb15 : wB G.pLen < 2 ^ 15 := by rcases h.gi.lens3 with e | e | e <;> rw [e] <;> decide
  have hb : WP isa (.block [scr .r3 sPacked, .li .r4 (2 * G.pLen + G.qLen), .li .r5 G.pLen, .li .r6 G.qLen,
      scr .r7 (wB G.pLen), .li .r8 (wWords G.pLen)]) s fun u =>
      (CArgs G u ∧ u.mem = s.mem) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r3, .r4, .r5, .r6, .r7, .r8] s u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by rfl)
    simp only [scr]
    prun [h.gi.r28, exec_addi (show Reg.r28 ≠ .r0 by decide) (show sPacked < 2 ^ 15 by decide),
      exec_addi (show Reg.r28 ≠ .r0 by decide) wb15, exec_li (show nPk G < 2 ^ 15 from n15), exec_li hp15,
      exec_li hq15, exec_li w15]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.write, GP.sa]
  exact WP.mono hb fun u ⟨⟨a, m⟩, k⟩ => ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ m k.sp, x⟩, a⟩

/-- The call of the check on the claim `pk` at `sPacked`. -/
theorem checkCall_vp {code : Prog isa} {name : String} (ok : CheckOk code) {pk : List Byte}
    (hpk : (sPacked, pk) ∈ c.cl) (hpkl : pk.length = nPk G) (hcl : ∀ x ∈ c.cl, Apart (wB G.pLen) (wWords G.pLen * 8) x) :
    VP (fun σ s => St G c X σ s ∧ CArgs G s) (.call name code)
      (fun σ t => St G c X σ t ∧
        ((t.gpr .r3).setWidth 32).toNat = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0)) := by
  have bytes : ∀ σ s, SS G 176 σ c s → Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk := fun σ s h => by
    have := h.sb _ hpk; rw [hpkl] at this; exact this
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (cRd G) (cWr G) fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ =>
      ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    have p₁ := pre_of_ckin (h₁.cEntry_ckin g₁)
    have p₂ := pre_of_ckin (h₂.cEntry_ckin g₂)
    obtain ⟨cr₁, cw₁⟩ := h₁.cCovers
    obtain ⟨cr₂, cw₂⟩ := h₂.cCovers
    obtain ⟨a3, a4, a5, a6, a7, a8⟩ := g₁
    obtain ⟨b3, b4, b5, b6, b7, b8⟩ := g₂
    refine ⟨p₁, p₂, cpub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, cr₁, cw₁, cr₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      have e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a3, b3]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a4, b4]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a5, b5]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a6, b6]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a7, b7]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a8, b8]
    · obtain ⟨_, _, _, _, _, _, n15⟩ := ck_sizes h₁.gi.lens
      have e4 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), a3, a4, b3, b4, e4,
        bytes _ _ h₁, bytes _ _ h₂]
  refine h.checkCall_ok (name := name) ok regs (bytes _ _ h) fun t g rd wr sp f st => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  obtain ⟨_, _, _, _, _, hEs, _⟩ := ck_sizes h.gi.lens
  exact h.of_scrs (keep_of_preserved g rd wr) sp (os := [(wB G.pLen, wWords G.pLen * 8)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨by simp only [hEnd, wB, kB, pB, fSave] at hE ⊢; omega, .inr (Nat.le_refl _),
        by simp only [List.length_replicate]; omega⟩)
    f (cl' := c.cl) (fun y hy => .inl ⟨hy, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩)

/-- p‖q‖g. -/
abbrev pkOf (pB qB gB : List Byte) : List Byte := pB ++ qB ++ gB

/-- The stage after the check. -/
abbrev ckCfg (c : Cfg) (pk : List Byte) (ok : Bool) : Cfg :=
  if ok then ({ c with cl := (sPacked, pk) :: c.cl }).setV fStatus 1 else { c with cl := (sPacked, pk) :: c.cl }

/-- The verdict, zero-extended, compared with 1. -/
theorem verdict_vp {c' : Cfg} {b : Bool} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .r3).setWidth 32).toNat = (if b then 1 else 0))
      (.block [.lsr .w .r3 .r3 0, .subi .r0 .r3 1])
      (fun σ t => St G c' X σ t ∧ isa.eval (.zero .d .r0) t = some b) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [.lsr .w .r3 .r3 0, .subi .r0 .r3 1]),
      rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, r3⟩ => ?_
  refine WP.wr (exec_lsr_w (by decide)) fun s₁ u₁ sp₁ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun t u sp _ => WP.block_nil ?_
  refine ⟨⟨(h.of_upd u₁ sp₁ (by decide)).of_upd u sp (by decide), x⟩, ?_⟩
  have hv : ((s.gpr .r3).setWidth 32 >>> 0).setWidth 64 = BitVec.ofNat 64 (if b then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ushiftRight_zero, BitVec.toNat_setWidth, r3, BitVec.toNat_ofNat]
  rw [eval_zero, u.gpr, u₁.gpr, hv]
  cases b <;> decide

theorem checkPart_vp {g : Geo} (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : CheckOk g.checkCode)
    {pB qB gB : List Byte} (hP : (sPBE, pB) ∈ c.cl) (hQ : (sQ, qB) ∈ c.cl) (hG : (sG, gB) ∈ c.cl)
    (hPl : pB.length = G.pLen) (hQl : qB.length = G.qLen) (hGl : gB.length = G.pLen)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) :
    VP (St G c X) g.checkPart
      (St G (ckCfg c (pkOf pB qB gB) (Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB))) X) := by
  by_cases l : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  swap
  · exact VP.of_false fun σ s h => l h.1.gi.lens
  unfold Geo.checkPart
  rw [hp, hq]
  have hb : 0 < G.pLen ∧ 0 < G.qLen ∧ G.pLen ≤ 384 ∧ G.qLen ≤ 32 := by
    rcases l with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> decide
  have e1 : sPacked = 2208 := rfl
  have e2 : sPBE = 1056 := rfl
  have e3 : sQ = 608 := rfl
  have e4 : sG = 1824 := rfl
  have hE : hEnd = 296 := rfl
  have hpb : VG.Impl.Dsa.PPC64LE.Generation.pB = 3072 := rfl
  -- The copies.
  refine VP.seq (copyCl_vp (dst := sPacked) hP hPl hb.1 (by omega) (by decide) (by decide) (by omega) (by omega)
    (by omega) fun x hx => .inl (hcl x hx)) ?_
  refine VP.seq (copyCl_vp (dst := sPacked + G.pLen) (List.mem_cons_of_mem _ hQ) hQl hb.2.1 (by omega) (by omega)
    (by decide) (by omega) (by omega) (by omega) fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega)
    · exact .inl (by have := hcl x hx; omega)
  refine VP.seq (copyCl_vp (dst := sPacked + G.pLen + G.qLen) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hG))
    hGl hb.1 (by omega) (by omega) (by decide) (by omega) (by omega) (by omega) fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hQl]; omega)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega)
    · exact .inl (by have := hcl x hx; omega)
  -- p‖q‖g, as one claim.
  have hsz := (ck_sizes l).1
  have hpkl : (pkOf pB qB gB).length = nPk G := by simp only [pkOf, List.length_append, hPl, hQl, hGl, nPk]; omega
  have offe : ∀ o n, VG.Proof.Bignum.off (G.sa o) n = G.sa (o + n) := fun o n => by
    rw [VG.Proof.Bignum.off, GP.sa_add]
  have join : ∀ σ s, SS G 176 σ { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } s → SS G 176 σ { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } s := fun σ s h => by
    have bp := h.sb (sPacked, pB) (by simp)
    have bq := h.sb (sPacked + G.pLen, qB) (by simp)
    have bg := h.sb (sPacked + G.pLen + G.qLen, gB) (by simp)
    simp only at bp bq bg
    have hc : Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pkOf pB qB gB).length = pkOf pB qB gB := by
      show Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pB ++ qB ++ gB).length = pB ++ qB ++ gB
      rw [List.length_append, List.length_append, VG.Proof.Dsa.Generation.bytesAt_append,
        VG.Proof.Dsa.Generation.bytesAt_append, offe, offe, ← Nat.add_assoc, bp, hPl, bq, hQl, bg]
    have ⟨pb', pk'⟩ := h.gi.pBig
    exact (h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => by simp [hy]) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩) (c' := c)).addCl hc ⟨by show hEnd ≤ sPacked; decide,
        .inl (show sPacked + (pkOf pB qB gB).length ≤ kB G.pLen by rw [hpkl]; simp only [nPk]; omega),
        show sPacked + (pkOf pB qB gB).length ≤ G.scrLen * 8 by rw [hpkl]; simp only [nPk]; omega⟩
  refine VP.seq ((cargs_vp (c := { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl }) (X := X)).mono (G' := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) ::
        c.cl } X σ s ∧ CArgs G s) (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, a⟩ => ⟨⟨join σ s h, x⟩, a⟩) ?_
  -- The check.
  refine VP.seq (checkCall_vp (c := { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) hck (by simp) hpkl
    fun y hy => .inl (by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hpkl]; omega
      · have := hcl y hy; omega)) ?_
  generalize hbv : Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB) = b
  refine VP.seq verdict_vp ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases b
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact stImm_vp (c := fun _ => { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) (o := fStatus) (v := 1)
        (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.1.1.2⟩
  · cases b
    · exact VP.block_nil fun σ s h => h.1.1
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

end

end VG.Proof.Dsa.PPC64LE.Gen
