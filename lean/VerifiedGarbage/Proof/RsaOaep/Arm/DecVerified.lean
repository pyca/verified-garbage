module

import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecChk
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.HashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-!
# RSAES-OAEP decryption on ARMv7: verified

The body (`body_vp`): the private-key operation into `EM`'s place, then
zeros and `(r = 2) ? 2 : 0` if `k < 2 hLen + 2`, or the decoding. The
frames around it (`wrap_ok`, `wrap_ct`), the result as the shared contract
states it, for MGF1's hash function the one whose table the argument 23 is
(`tabFacts_entered`): `vg_rsa_oaep_<H>_mgf1_decrypt`, calling
`vg_rsa_private_checked` over any implementation `v` of
`vg_rsa_private_crt`, with MGF1's hash function any of the tables of `vs`,
is verified (`dec_verified`). Every stage keeps the addresses of the statics
(`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.HashTable.Arm (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered)

section
variable {F G H : State → State → Prop} {a b c d e r : Prog isa}

theorem relCT_assoc' {Q R : State → State → Prop} (h : RelCT isa Q (.seq a (.seq b c)) R) :
    RelCT isa Q (.seq (.seq a b) c) R := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem VP.assoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := VP.assoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  VP.assoc (VP.cont2 (VP.assoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  VP.assoc (VP.cont3 (VP.assoc' h) h₂)

theorem VP.cont5 (h : VP F (.seq a (.seq b (.seq c (.seq d e)))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d (.seq e r))))) H :=
  VP.assoc (VP.cont4 (VP.assoc' h) h₂)

end

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The decoding, when `k ≥ 2 hLen + 2`, with MGF1's hash function `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => Sy (C2 h.H.D P) σ s ∧ isa.eval .ne s = some false) (decMain h.H f) (Sy (Fin h.G g.G P)) :=
  ((VP.syms (lab_vp h P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x).seq
    (VP.cont4 (unmask_vp h g P hT fne) (VP.syms (VP.cont5 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
      (VP.cont4 (buf_vp h g P) ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (outCopy_vp h g P)
        (VP.cont2 (outMask_vp h g P) (end_vp h g P))))))))))

theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S P)) (decBody h.H f (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h.G g.G P)) :=
  VP.cont4 (VP.syms ((start_vp P).seq ((pa_vp P).seq ((call_vp P v).seq (chk_vp h P))))) (VP.ite
    (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT fne))

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with MGF1's hash
function any of the tables of `vs`. -/
abbrev decCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  decrypt h.H (fnsOf vs) (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

/-- The contract, with MGF1's hash function one of the tables of `vs`. -/
abbrev dspec : Contract isa := spec h.G (tables vs)

variable {h vs}

/-- The public parameters for the table of `w`, with its functions where `s'` has them. -/
abbrev epw (s s' : State) (w : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (stackArg s 19) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))

theorem spec_sp {s : State} (hs : (dspec h vs).pre s) : stackBytes ≤ s.sp.toNat := by
  dec_pre at hs
  exact hs.1

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the table of `w` at the argument 23, with the
functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (dspec h vs).pre s) {w : TVar} (hw : w ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (tableOf w)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (epw (vs := vs) s s' w)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, hpw, hfit⟩ := spec_tab hs
  rw [List.append_nil] at hpw
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_sp hs)
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) hs trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.Arm.mem_names hw
  have tf := tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [ep]) hfit hc hpw hw hh
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN) hs tf
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) {s : State} (hs : (dspec h vs).pre s) :
    WP isa (decCode h vs v) s fun t => abiPreserved s t ∧ (dspec h vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, -, hfit⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have st := entered_state hc hs hw hh (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp h (epw (vs := vs) s s w) w.g (fun _ x => x) (fne_of hw) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (epw (vs := vs) s s w).lay.W)
    (Q := fun r m => Res h.G w.g.G (epw (vs := vs) s s w) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 80) (C := 3440) (argv := (epw (vs := vs) s s w).argv)
      (ro := (epw (vs := vs) s s w).lay.ro) (rw := (epw (vs := vs) s s w).lay.rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    intro G hG
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl, hashAt_tableOf hfit hidx,
      Option.some.injEq] at hG
    subst hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s s w).lay.ro) =>
      entered_ro (F := frameBytes) (A := 80) (C := 3440) (argv := (epw (vs := vs) s s w).argv)
        (rw := (epw (vs := vs) s s w).lay.rw) hin.ok hsp' hR
    have hP : pB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3))
        (stackArg s 4).toNat := ro (R := (epw (vs := vs) s s w).PP) (by simp)
    have hQ : qB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5))
        (stackArg s 6).toNat := ro (R := (epw (vs := vs) s s w).QQ) (by simp)
    have hDP : dpB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 7)) (stackArg s 4).toNat := ro (R := (epw (vs := vs) s s w).DP) (by simp)
    have hDQ : dqB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 9)) (stackArg s 6).toNat := ro (R := (epw (vs := vs) s s w).DQ) (by simp)
    have hQI : qiB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 11)) (stackArg s 4).toNat := ro (R := (epw (vs := vs) s s w).QI) (by simp)
    have hL : labB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 13)) (stackArg s 14).toNat := ro (R := (epw (vs := vs) s s w).LAB) (by simp)
    have hC : ctB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 15)) (stackArg s 0).toNat := ro (R := (epw (vs := vs) s s w).CT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (dspec h vs).pre (dspec h vs).pub (decCode h vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, -, hfit⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by rw [List.append_eq, List.append_nil]; exact hn)).symm
  have hep : epw (vs := vs) s₁ s₁ w = epw (vs := vs) s₂ s₁ w := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, a0])
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a9, a11, a13, a14, a15, a17, a18, a19]
    rw [h3, a0] at hn
    rw [a1, a2] at he
    rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
      show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h (epw (vs := vs) s₁ s₁ w) w.g (fun _ x => x) (fne_of hw) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, calling `vg_rsa_private_checked` over
`v`, with MGF1's hash function any of the tables of `vs`, meets the shared
contract (satisfiable, `DecSat.lean`). -/
theorem dec_verified (hc : Coh vs) (hsat : ∃ s, (dspec h vs).pre s) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (decCode h vs v) (dspec h vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc v, hsat⟩

end VG.Proof.RsaOaep.Arm.Dec
