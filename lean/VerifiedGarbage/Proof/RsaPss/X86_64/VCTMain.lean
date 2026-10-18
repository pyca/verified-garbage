module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VPiecesB
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VPiecesB
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: `verifyMain` in constant time

The pieces between the calls are checked by the taint analysis from the
frame's public slots (`v_taintS`), with `VS`'s steps (`VPieces.lean`) for
what correctness says after them; the calls of the hash functions'
streaming functions are of the same addresses with the same public
arguments in both runs (`v_init`, `v_upd`, `v_fin`), and so is MGF1
(`v_mgf`); the public operation is constant time for its contract, whose
public data (the registers, its stack arguments, `pre` and `e`) the
entry's public data fix (`callV_ct`); the branch of `saltBack` is on
whether the salt's length is given, which is public, and the candidates'
loop runs `dbLen` times, which is public too.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD oEm oSt oDig oLh oBuf oW oRsa scr lay shift)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor initF updF finF ldFn)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub Lay Rep upd nW tw Like Calls Fns frT lenOf
  fns_of_tab two_initF two_updF two_finF ME MQ MArgs MFit mgf_ct nopin sizes stackArg_entry e_entry_regs)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Proof.HashFns (StreamingOK)

variable {kH kG : Nat}

theorem ks_sub {ks : List Nat} (h : ks.all (fun k => decide (k ∈ vKs ∨ k = 33 ∨ k = 44)) = true) :
    ∀ k ∈ ks, k ∈ vKs ∨ k = 33 ∨ k = 44 := fun k hk => of_decide_eq_true (List.all_eq_true.mp h k hk)

/-- The streaming functions of the table `i` (10 or 11), for the selector's
hash function. -/
theorem VSib.fns {a s : State} (S : VSib kH kG a s) {T : Spec.HashFns.Streaming} {i : Nat}
    (h : (i = 10 ∧ Spec.HashFns.streaming kH = some T) ∨ (i = 11 ∧ Spec.HashFns.streaming kG = some T)) :
    VFns s T i := by
  rcases h with ⟨rfl, sT'⟩ | ⟨rfl, sT'⟩
  · obtain ⟨T', _, sT, _, _, hF⟩ := fns_of_tab S.1.fH
    rw [S.2.2.1, sT', Option.some.injEq] at sT
    subst sT; exact hF
  · obtain ⟨T', _, sT, _, _, hF⟩ := fns_of_tab S.1.fG
    rw [S.2.2.2.1, sT', Option.some.injEq] at sT
    subst sT; exact hF

/-- The table's words in their slots: `j` is 45 for the table 10, 48 for 11. -/
theorem VS.fnw {P : State → (Nat → BitVec 64) → Prop} {s t : State} (h : VS P s t) {i j : Nat}
    (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) :
    t.mem.readW (off (fb s) (8 * j)) 64 = tw s.mem (stackArg s i) 0 ∧
      t.mem.readW (off (fb s) (8 * j + 8)) 64 = tw s.mem (stackArg s i) 1 ∧
      t.mem.readW (off (fb s) (8 * j + 16)) 64 = tw s.mem (stackArg s i) 2 := by
  obtain ⟨-, -, ⟨V, W, R, hA, -⟩, -⟩ := h
  rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(R.fr 45 (by decide)).trans hA.sel.2.2.1.1, (R.fr 46 (by decide)).trans hA.sel.2.2.1.2.1,
      (R.fr 47 (by decide)).trans hA.sel.2.2.1.2.2⟩
  · exact ⟨(R.fr 48 (by decide)).trans hA.sel.2.2.2.1, (R.fr 49 (by decide)).trans hA.sel.2.2.2.2.1,
      (R.fr 50 (by decide)).trans hA.sel.2.2.2.2.2⟩

theorem ji_i {i j : Nat} (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) : i = 10 ∨ i = 11 := by
  rcases hji with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem ji_j {i j : Nat} (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) : 8 * j + 24 ≤ frameBytes := by
  rcases hji with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-! ## The calls of the streaming functions -/

section
variable {T : Spec.HashFns.Streaming} {Hs : Spec.Mgf1.Hash} (hT : StreamingOK T Hs) {i j : Nat}
  (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) (hfn : ∀ a s, VSib kH kG a s → VFns s T i)

include hT hji hfn in
theorem v_init {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop}
    (hJ : ∀ s t, J s t → VS P s t ∧ t.gpr .rdi = off (stackArg s 4) oSt)
    (ht : ∃ hc, (taint.check (frT [] [] 1) (.block (ldFn (8 * j))) hc).isSome = true) :
    RelCT isa (Two (VAt kH kG J)) (initF (8 * j)) fun _ _ => True :=
  two_initF hT encStack fb (fun a => stackArg a 4) (fun a => [vscrR a]) id (fun a => tw a.mem (stackArg a i) 0)
    (fun a => tw a.mem (stackArg a i) 1) (fun a => tw a.mem (stackArg a i) 2) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, hdi⟩ := hJ s t hj
      have hf := h.fnw hji
      refine ⟨?_, ?_, ?_, ?_, S.calls h.1 (ji_i hji) (hfn a s S)⟩
      · rw [← S.fb, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 4) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (ji_i hji) (i := 0) (by decide)]; exact hf.1
      · rw [← S.arg (j := 4) (by decide)]; exact hdi) (by have := ji_j hji; omega) ht

include hT hji hfn in
theorem v_upd {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (O Ln C : State → Nat)
    (hJ : ∀ s t, VPre s → J s t → VS P s t ∧ RU (O s) (Ln s) (C s) s t ∧ O s + Ln s ≤ oRsa ∧
      (O s + Ln s ≤ oSt ∨ oSt + T.S.stateBytes ≤ O s) ∧ (O s + Ln s ≤ oW ∨ oW + 8 * T.scratch ≤ O s))
    (hs : ∀ a s, VSib kH kG a s → O s = O a ∧ Ln s = Ln a ∧ C s = C a)
    (ht : ∃ hc, (taint.check (frT [] [] 1) (.block (ldFn (8 * j + 8))) hc).isSome = true) :
    RelCT isa (Two (VAt kH kG J)) (updF (8 * j)) fun _ _ => True :=
  two_updF hT encStack fb (fun a => stackArg a 4) (fun a => [vscrR a]) id (fun a => tw a.mem (stackArg a i) 0)
    (fun a => tw a.mem (stackArg a i) 1) (fun a => tw a.mem (stackArg a i) 2) O Ln
    (fun a => BitVec.ofNat 64 (C a)) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, ⟨hdi, hsi, hdx, hcx, h8⟩, b1, b2, b3⟩ := hJ s t S.1 hj
      obtain ⟨e1, e2, e3⟩ := hs a s S
      have hf := h.fnw hji
      rw [e1, e2] at b1 b2 b3
      refine ⟨?_, ?_, ?_, S.calls h.1 (ji_i hji) (hfn a s S), b1, b2, b3, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← S.fb, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 4) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (ji_i hji) (i := 1) (by decide)]; exact hf.2.1
      · rw [← S.arg (j := 4) (by decide)]; exact hdi
      · rw [← e3]; exact hsi
      · rw [← S.arg (j := 4) (by decide), ← e1]; exact hdx
      · rw [← e2]; exact hcx
      · rw [← S.arg (j := 4) (by decide)]; exact h8) (by have := ji_j hji; omega) ht

include hT hji hfn in
theorem v_fin {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (O C : State → Nat)
    (hJ : ∀ s t, VPre s → J s t → VS P s t ∧ RF (O s) (C s) s t ∧ (O s + 64 ≤ oSt ∨ (oSt + 256 ≤ O s ∧ O s + 64 ≤ oW)))
    (hs : ∀ a s, VSib kH kG a s → O s = O a ∧ C s = C a)
    (ht : ∃ hc, (taint.check (frT [] [] 1) (.block (ldFn (8 * j + 16))) hc).isSome = true) :
    RelCT isa (Two (VAt kH kG J)) (finF (8 * j)) fun _ _ => True :=
  two_finF hT encStack fb (fun a => stackArg a 4) (fun a => [vscrR a]) id (fun a => tw a.mem (stackArg a i) 0)
    (fun a => tw a.mem (stackArg a i) 1) (fun a => tw a.mem (stackArg a i) 2) O
    (fun a => BitVec.ofNat 64 (C a)) (fun a t ⟨s, S, hj⟩ => by
      obtain ⟨h, ⟨hdi, hsi, hdx, hcx⟩, b1⟩ := hJ s t S.1 hj
      obtain ⟨e1, e3⟩ := hs a s S
      have hf := h.fnw hji
      rw [e1] at b1
      refine ⟨?_, ?_, ?_, S.calls h.1 (ji_i hji) (hfn a s S), b1, ?_, ?_, ?_, ?_⟩
      · rw [← S.fb, ← S.scr_eq]; exact h.1.frv S.1
      · rw [← S.fb, ← S.arg (j := 4) (by decide)]; exact h.2.1
      · rw [← S.fb, ← S.tw (ji_i hji) (i := 2) (by decide)]; exact hf.2.2
      · rw [← S.arg (j := 4) (by decide)]; exact hdi
      · rw [← e3]; exact hsi
      · rw [← S.arg (j := 4) (by decide), ← e1]; exact hdx
      · rw [← S.arg (j := 4) (by decide)]; exact hcx) (by have := ji_j hji; omega) ht

end

/-! ## The pieces of `verifyMain` -/

section
variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh) (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some Hh) (eG : Spec.HashId.mgf1 kG = some Gh)

include hTH eH in
theorem VSib.r9 {a s : State} (S : VSib kH kG a s) : (s.gpr .r9).toNat = vD s := by
  have e : Spec.HashId.mgf1 (vselH s) = some Hh := by rw [S.2.2.1]; exact eH
  rw [S.1.dl Hh e, hTH.len, VG.Proof.RsaOaep.X86_64.lenOf_eq hTH e]

/-- `VS P`, and a fact of the entry. -/
theorem VS.addP {P : State → (Nat → BitVec 64) → Prop} {Q : State → Prop} {s t : State} (h : VS P s t)
    (hq : Q s) : VS (fun s W => P s W ∧ Q s) s t :=
  let ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h; ⟨he, L, ⟨V, W, R, hA, h33, h44, hP, hq⟩, hf⟩

theorem VS.getP {P : State → (Nat → BitVec 64) → Prop} {Q : State → Prop} {s t : State}
    (h : VS (fun s W => P s W ∧ Q s) s t) : Q s :=
  let ⟨_, _, ⟨_, _, _, _, _, _, ⟨_, hq⟩⟩, _⟩ := h; hq

include hTH sH in
/-- `H`'s state set to represent the prefix. -/
theorem hashPrefix_ct {P : State → (Nat → BitVec 64) → Prop} :
    RelCT isa (Two (VAt kH kG (VS P))) hashPrefix (Two (VAt kH kG (VS P))) := by
  have hT := hTH
  have hfn : ∀ a s, VSib kH kG a s → VFns s TH 10 := fun a s S => S.fns (.inl ⟨rfl, sH⟩)
  unfold hashPrefix seqs seqs seqs
  refine RelCT.seq (v_post (J' := fun s t => VS P s t ∧ t.gpr .rdi = off (stackArg s 4) oSt)
    (v_taintS (fun _ _ h => h) [] [14] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => vscr_step h) ?_
  refine RelCT.seq (v_post (J' := VS P) (v_init hT (j := 45) (.inl ⟨rfl, rfl⟩) hfn (fun _ _ h => h)
    ⟨_, by taint_decide⟩) fun _ s _ S h => vinit_step hT (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1 h.2) ?_
  refine RelCT.seq (v_post (J' := fun s t => VS P s t ∧ RU oMp (vD s + 8) 0 s t)
    (v_taintS (fun _ _ h => h) [] [14, 39] (ks_sub (by decide)) nopin ⟨_, by taint_decide⟩)
    fun _ _ _ _ h => vpre_step h) ?_
  refine v_post (v_upd hT (j := 45) (.inl ⟨rfl, rfl⟩) hfn (fun _ => oMp) (fun s => vD s + 8) (fun _ => 0)
    (fun s t hp h => ⟨h.1, h.2, ?_⟩) (fun a s S => ⟨rfl, by rw [S.d_eq], rfl⟩) ⟨_, by taint_decide⟩)
    fun _ s _ S h => ?_
  · obtain ⟨-, -, -, hD64, -⟩ := h.1.2.2.2.sizes hp
    obtain ⟨hzS, -, hzW, -⟩ := sizes hT
    exact ⟨by unfold oMp oRsa; omega, .inr (by unfold oMp oSt; omega), .inl (by unfold oMp oW; omega)⟩
  · obtain ⟨-, -, -, hD64, -⟩ := h.1.2.2.2.sizes S.1
    obtain ⟨hzS, -, hzW, -⟩ := sizes hT
    obtain ⟨a, b, c, d, e⟩ := h.2
    exact vupd_step hT (.inl ⟨rfl, rfl⟩) (hfn _ s S) h.1 (by unfold oMp oRsa; omega)
      (.inr (by unfold oMp oSt; omega)) (.inl (by unfold oMp oW; omega)) a c d e

end

end VG.Proof.RsaPss.X86_64
