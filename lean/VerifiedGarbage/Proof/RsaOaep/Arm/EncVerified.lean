module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncChk
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.HashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`) and the result as the
shared contract states it, for MGF1's hash function the one whose table the
argument 15 is (`tabFacts_entered`): `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`,
calling a precomputed public operation `c`, with MGF1's hash function any of
the tables of `vs`, is verified, given a state that meets the contract
(`EncSat.lean`): `encrypt_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)
open VG.Proof.HashTable.Arm (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered)

variable (h : OHash) (vs : List TVar)

/-- The code, calling `c`, with MGF1's hash function any of the tables of `vs`. -/
abbrev encryptCode (c : PdImpl) : Prog isa := encryptPrecomputed h.H (fnsOf vs) c.name c.code

/-- The contract, with MGF1's hash function one of the tables of `vs`. -/
abbrev espec : Contract isa := spec h.G (tables vs)

variable {h vs}

/-- The public parameters for the table of `w`, with its functions where `s'` has them. -/
abbrev epw (s s' : State) (w : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (stackArg s 11) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))

theorem spec_sp {s : State} (hs : (espec h vs).pre s) : stackBytes ≤ s.sp.toNat := by
  enc_pre at hs
  exact hs.1

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the table of `w` at the argument 15, with the
functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (espec h vs).pre s) {w : TVar} (hw : w ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 11)) (FnTable.words isa s (tableOf w)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S h (epw (vs := vs) s s' w)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, hpw, hfit⟩ := spec_tab hs
  rw [List.append_nil] at hpw
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := by have := spec_sp hs; simp only [stackBytes] at this; omega
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) hs trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.Arm.mem_names hw
  have tf := tabFacts_entered ok hsp' (p := stackArg s 11) (by simp [ep]) hfit hc hpw hw hh
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN) hs tf
  rw [h.glen] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (c : PdImpl) {s : State} (hs : (espec h vs).pre s) :
    WP isa (encryptCode h vs c) s fun t => abiPreserved s t ∧ (espec h vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, -, hfit⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have st := entered_state hc hs hw hh (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hsp; omega
  refine WP.mono (wrap_ok (by decide) (by omega) (W := ((epw (vs := vs) s s w).lay h.H.D).W)
    (Q := fun r m => Res h w.g (epw (vs := vs) s s w) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((body_vp h (epw (vs := vs) s s w) w.g (fun _ x => x) (fne_of hw) c).wp _ _ st)
      fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 48) (argv := (epw (vs := vs) s s w).argv)
      (ro := ((epw (vs := vs) s s w).lay h.H.D).ro) (rw := ((epw (vs := vs) s s w).lay h.H.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    intro G hG
    rw [show BitVec.setWidth 64 (stackArg s 11) = State.addr (stackArg s 11) from rfl, hashAt_tableOf hfit hidx,
      Option.some.injEq] at hG
    subst hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ ((epw (vs := vs) s s w).lay h.H.D).ro) =>
      entered_ro (F := frameBytes) (A := 48) (argv := (epw (vs := vs) s s w).argv)
        (rw := ((epw (vs := vs) s s w).lay h.H.D).rw) hin.ok hsp' hR
    have hL : labB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2))
        (stackArg s 3).toNat := ro (R := (epw (vs := vs) s s w).LAB) (by simp)
    have hM : msgB (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4))
        (stackArg s 5).toNat := ro (R := (epw (vs := vs) s s w).MSG) (by simp)
    have hS : seedB h (epw (vs := vs) s s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 6)) h.H.D := ro (R := (epw (vs := vs) s s w).SEED h.H.D) (by simp)
    unfold Res at res
    rw [hL, hM, hS] at res
    rw [h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (c : PdImpl) : ConstantTime isa (espec h vs).pre (espec h vs).pub (encryptCode h vs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, -, hfit⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hsp1 := spec_sp h₁
  sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by rw [List.append_eq, List.append_nil]; exact hn)).symm
  have hep : epw (vs := vs) s₁ s₁ w = epw (vs := vs) s₂ s₁ w := by
    obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h3])
    have hw' := map_toNat_inj hw
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [a9, a10] at hw'
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
      show State.addr (stackArg s₂ 9) = BitVec.setWidth 64 (stackArg s₂ 9) from rfl, hw']
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; simp only [stackBytes] at hsp1; omega) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h (epw (vs := vs) s₁ s₁ w) w.g (fun _ x => x) (fne_of hw) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, calling `c`, with MGF1's
hash function any of the tables of `vs`, meets the shared contract
(satisfiable, `EncSat.lean`). -/
theorem encrypt_verified (hc : Coh vs) (hsat : ∃ s, (espec h vs).pre s) (c : PdImpl) :
    Verified target (encryptCode h vs c) (espec h vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc c, hsat⟩

end VG.Proof.RsaOaep.Arm.Enc
