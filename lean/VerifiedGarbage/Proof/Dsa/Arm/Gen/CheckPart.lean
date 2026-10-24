module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.CheckCall
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: checking p‖q‖g

`checkPart_vp`: p (at `sPBE`), q (at `sQ`) and g (at `sG`) copied side by
side to `sPacked`, checked by `vg_dsa_check_parameters`: `fStatus` := 1 if
`Spec.Dsa.checkParametersBytes` accepts them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_movw wp_mov wp_cmp op2_imm eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The check's arguments. -/
theorem cargs_vp (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) :
    VP (St G c X) (.block (scr G.pLen .r0 sPacked ++ ([.movw .r1 (BitVec.ofNat 16 (2 * G.pLen + G.qLen)),
        .movw .r2 (BitVec.ofNat 16 G.pLen), .mov .r3 (.imm (BitVec.ofNat 32 G.qLen))] : List Instr) ++ scr G.pLen .r4 sA ++
        ([.movw .r5 (BitVec.ofNat 16 (wa G.pLen / 8))] : List Instr)))
      (fun σ s => St G c X σ s ∧ CArgs G s) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sPacked ++ [.movw .r1 (BitVec.ofNat 16 1), .movw .r2 (BitVec.ofNat 16 1),
        .mov .r3 (.imm (BitVec.ofNat 32 1))] ++ scr 128 .r4 sA ++ [.movw .r5 (BitVec.ofNat 16 1)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8])
    fun σ s ⟨h, x⟩ => ?_
  have big := h.gi.scrBig
  have hLv := h.lens
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hsK : sA ≤ sK G.pLen := by simp only [sK]; omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sPacked, sK, sA]; omega) fun s₁ v₁ R₁ M₁ => ?_
  refine wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ => wp_mov (op2_imm (encodable_lt (by omega))) fun s₄ u₄ => ?_
  have h4 : SS G σ c s₄ := ((((h.of_rest R₁ M₁).of_rest (u₂.rest (ws := [.r1]) (by simp)) u₂.mem).of_rest
    (u₃.rest (ws := [.r2]) (by simp)) u₃.mem).of_rest (u₄.rest (ws := [.r3]) (by simp)) u₄.mem)
  refine scr_ok (d := .r4) h4.r8 rfl hLv hsK fun s₅ v₅ R₅ M₅ => wp_movw fun t u => WP.block_nil ?_
  refine ⟨⟨(h4.of_rest R₅ M₅).of_rest (u.rest (ws := [.r5]) (by simp)) u.mem, x⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), v₁]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      setWidth_ofNat16 (by omega)]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.other _ (by decide), u₃.gpr, setWidth_ofNat16 (by omega)]
  · rw [u.other _ (by decide), R₅.gpr _ (by decide), u₄.gpr]
  · rw [u.other _ (by decide), v₅]
  · rw [u.gpr, setWidth_ofNat16 (by simp only [wa]; omega)]

/-- p‖q‖g. -/
abbrev pkOf (pB qB gB : List Byte) : List Byte := pB ++ qB ++ gB

/-- The stage after the check. -/
abbrev ckCfg (c : Cfg) (pk : List Byte) (ok : Bool) : Cfg :=
  if ok then ({ c with cl := (sPacked, pk) :: c.cl }).setV fStatus 1 else { c with cl := (sPacked, pk) :: c.cl }

theorem checkPart_vp {g : Geo} (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters)
    (hlq : Spec.Dsa.generationLengthsValid G.pLen G.qLen) {pB qB gB : List Byte}
    (hP : (sPBE, pB) ∈ c.cl) (hQ : (sQ, qB) ∈ c.cl) (hG : (sG, gB) ∈ c.cl)
    (hPl : pB.length = G.pLen) (hQl : qB.length = G.qLen) (hGl : gB.length = G.pLen)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) :
    VP (St G c X) g.checkPart
      (St G (ckCfg c (pkOf pB qB gB) (Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB))) X) := by
  unfold Geo.checkPart
  rw [hp, hq, hck]
  have hq32 : G.qLen ≤ 32 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hp384 : G.pLen ≤ 384 := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hp0 : 0 < G.pLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have hq0 : 0 < G.qLen := by unfold Spec.Dsa.generationLengthsValid at hlq; omega
  have e1 : sPacked = 2112 := rfl
  have e2 : sPBE = 576 := rfl
  have e3 : sQ = 128 := rfl
  have e4 : sG = 1728 := rfl
  have e5 : sA = 4096 := rfl
  have hK : ∀ n, n ≤ 4096 → n ≤ sK G.pLen := fun n hn => by simp only [sK, sA] at *; omega
  -- The copies.
  refine VP.seq (G := St G { c with cl := (sPacked, pB) :: c.cl } X) (copyS_vp (c := fun _ => c) (fun σ s h => h.1) rfl hp0 (by omega)
    (hK _ (by omega)) (hK _ (by omega)) (.inr (by omega)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ hP
    refine h.of_scr R (o := sPacked) (n := G.pLen) (hK _ (by omega)) (f.mono (by simp))
      (cl' := (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [hPl, e, ← hPl]; exact b, by rw [hPl]; exact hK _ (by omega)⟩
    · exact .inl ⟨hy, .inl (hcl y hy)⟩
  refine VP.seq (G := St G { c with cl := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl } X)
    (copyS_vp (c := fun _ => { c with cl := (sPacked, pB) :: c.cl }) (fun σ s h => h.1) rfl hq0 (by omega)
    (hK _ (by omega)) (hK _ (by omega)) (.inr (by omega)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ (show (sQ, qB) ∈ (sPacked, pB) :: c.cl from List.mem_cons_of_mem _ hQ)
    refine h.of_scr R (o := sPacked + G.pLen) (n := G.qLen) (hK _ (by omega)) (f.mono (by simp))
      (cl' := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    swap
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_self, .inl (by rw [hPl])⟩
    · exact .inl ⟨List.mem_cons_of_mem _ hy, .inl (by have := hcl y hy; omega)⟩
    · exact .inr ⟨by rw [hQl, e, ← hQl]; exact b, by rw [hQl]; exact hK _ (by omega)⟩
  refine VP.seq (G := St G { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } X)
    (copyS_vp (c := fun _ => { c with cl := (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl }) (fun σ s h => h.1) rfl hp0 (by omega)
    (hK _ (by omega)) (hK _ (by omega)) (.inr (by omega)) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩) ?_
  · have b := h.sb _ (show (sG, gB) ∈ (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl from
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hG))
    refine h.of_scr R (o := sPacked + G.pLen + G.qLen) (n := G.pLen) (hK _ (by omega)) (f.mono (by simp))
      (cl' := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) :: (sPacked, pB) :: c.cl) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [hGl, e, ← hGl]; exact b, by rw [hGl]; exact hK _ (by omega)⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_self, .inl (by rw [hQl])⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inl ⟨List.mem_cons_of_mem _ List.mem_cons_self, .inl (by rw [hPl]; omega)⟩
    · exact .inl ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy), .inl (by have := hcl y hy; omega)⟩
  -- p‖q‖g, as one claim.
  have join : ∀ σ s, SS G σ { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl } s → SS G σ { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } s := fun σ s h => by
    have hc : ∀ y ∈ (sPacked, pkOf pB qB gB) :: c.cl,
        Spec.Rsa.bytesAt s.mem (G.sa y.1) y.2.length = y.2 ∧ y.1 + y.2.length ≤ sK G.pLen := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · have bp := h.sb (sPacked, pB) (by simp)
        have bq := h.sb (sPacked + G.pLen, qB) (by simp)
        have bg := h.sb (sPacked + G.pLen + G.qLen, gB) (by simp)
        have offe : ∀ o n, VG.Proof.Bignum.off (G.sa o) n = G.sa (o + n) := fun o n => by
          simp only [VG.Proof.Bignum.off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        simp only at bp bq bg
        refine ⟨?_, by simp only [pkOf, List.length_append, hPl, hQl, hGl]; exact hK _ (by omega)⟩
        show Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pB ++ qB ++ gB).length = pB ++ qB ++ gB
        rw [List.length_append, List.length_append, VG.Proof.Dsa.Generation.bytesAt_append,
          VG.Proof.Dsa.Generation.bytesAt_append, offe, offe, ← Nat.add_assoc, bp, hPl, bq, hQl, bg]
      · exact ⟨h.sb _ (by simp [hy]), h.clOk _ (by simp [hy])⟩
    exact ⟨h.gi, h.r7, h.r8, h.r9, fun y hy => (hc y hy).1, fun y hy => (hc y hy).2, h.arrs, h.liveOk, h.ksl,
      h.kslOk⟩
  refine VP.seq ((cargs_vp (c := { c with cl := (sPacked + G.pLen + G.qLen, gB) :: (sPacked + G.pLen, qB) ::
      (sPacked, pB) :: c.cl }) (X := X) hlq).mono (G' := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) ::
        c.cl } X σ s ∧ CArgs G s) (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, a⟩ => ⟨⟨join σ s h, x⟩, a⟩) ?_
  -- The check.
  have hpkl : (pkOf pB qB gB).length = nPk G := by simp only [pkOf, List.length_append, hPl, hQl, hGl, nPk]; omega
  refine VP.seq (checkCall_vp (c := { c with cl := (sPacked, pkOf pB qB gB) :: c.cl })
    (cl' := (sPacked, pkOf pB qB gB) :: c.cl) hlq (by simp) hpkl h88 h92 fun y hy =>
    ⟨hy, .inl (by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hpkl]; simp only [nPk, sPacked, sA]; omega
      · have := hcl y hy; simp only [sPacked, sA] at *; omega)⟩) ?_
  generalize hb : Spec.Dsa.checkParametersBytes G.pLen G.qLen (pkOf pB qB gB) = b
  refine VP.seq (G := fun σ s => St G { c with cl := (sPacked, pkOf pB qB gB) :: c.cl } X σ s ∧ isa.eval .eq s = some b)
    (VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (.block [.cmp .r0 (.imm 1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r0⟩ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
        ⟨⟨h.of_rest (f.rest []) f.mem, x⟩, by rw [eval_eq, z, r0]; cases b <;> decide⟩) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases b
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact stImm_vp (c := fun _ => { c with cl := (sPacked, pkOf pB qB gB) :: c.cl }) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
  · cases b
    · exact VP.block_nil fun σ s h => h.1.1
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

end

end VG.Proof.Dsa.Arm.Gen
