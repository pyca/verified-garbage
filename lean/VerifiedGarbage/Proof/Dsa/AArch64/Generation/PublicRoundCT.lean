module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrWin
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrWin
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
meta import VerifiedGarbage.Proof.MillerRabin.Representation
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# DSA parameter generation on AArch64: constant time of the round for public candidates

Runs of `publicRound` leak the same when they agree on the working space
and on the candidate: the exponent's windows are then the same, and with
them the table entry each window reads (`publicSel_ct`, its address pinned
by correctness). Everything else is the shared round's, piece by piece
(`Proof/RsaKeyGen/AArch64/CTMrWin.lean`, `CTMrExp.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The public data: the working space, and the candidate. -/
abbrev CPub := WsP × Nat

/-- Word `w − 1 − j` of the candidate's exponent. -/
def pubWord (c w j : Nat) : BitVec 64 := BitVec.ofNat 64 (mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64)

theorem pubWord_toNat (c w j : Nat) : (pubWord c w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
  rw [pubWord, BitVec.toNat_ofNat, Nat.mod_mod]

/-- After `i` windows of word `w − 1 − j` (`WinP`), for the candidate of the public data. -/
def WinPc (q : CPub × Nat) (i : Nat) (s : State) : Prop :=
  4 ≤ q.1.1.w ∧ q.1.1.w ≤ 128 ∧ slot q.1.1.w aE + 8 * (q.1.1.w + 2) ≤ q.1.1.Z ∧ q.2 < q.1.1.w ∧ ∃ bm b s₀,
    WinInv q.1.1.B q.1.1.Z q.1.1.w q.1.2 bm b (q.1.1.w - q.2) (pubWord q.1.2 q.1.1.w q.2) s₀ i s ∧
    ECtx s₀.mem q.1.1.B q.1.1.w q.1.2 ∧ q.1.2 % 2 = 1 ∧ 1 < q.1.2

theorem WinPc.winP {q : CPub × Nat} {i : Nat} {s : State} (h : WinPc q i s) : WinP (q.1.1, q.2) i s := by
  obtain ⟨h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  exact ⟨h4, h128, hEZ, hj, _, bm, b, s₀, _, hI, pubWord_toNat _ _ _, hE, hodd, hc1⟩

/-- The digit of window `i` of word `w − 1 − j`. -/
def pubDigit (r : (CPub × Nat) × Nat) : Nat :=
  ((pubWord r.1.1.2 r.1.1.1.w r.1.2 <<< (4 * r.2)) >>> 60).toNat

/-- After a window's squarings: `WW`, and the word in `kV`. -/
def WVc (r : (CPub × Nat) × Nat) (s : State) : Prop :=
  WW r.1.1.1 s ∧ word s.mem r.1.1.1.B (8 * kV) = pubWord r.1.1.2 r.1.1.1.w r.1.2 <<< (4 * r.2)

/-- After the digit: `WW`, and the public digit in `kG`. -/
def WDc (r : (CPub × Nat) × Nat) (s : State) : Prop :=
  WW r.1.1.1 s ∧ word s.mem r.1.1.1.B (8 * kG) = BitVec.ofNat 64 (pubDigit r)

theorem winSq_ok (M : Mont) {r : (CPub × Nat) × Nat} {s : State} (h : r.2 < 16 ∧ WinPc r.1 r.2 s) :
    WP isa (seqs (mrSq M.mm ++ (mrSq M.mm ++ (mrSq M.mm ++ mrSq M.mm)))) s (WVc r) := by
  obtain ⟨-, h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  have hn := hI.ctx.ws.scr.nowrap
  refine WP.mono (sq4_ok M h128 hI.ctx hodd hc1 (st := (_, _)) hI.y hI.flag) fun t ⟨hct, hYt, _, hf, k⟩ => ?_
  have hT : TabOK t.mem r.1.1.1.B r.1.1.1.w r.1.1.2 b :=
    hI.tab.of_low (hf.mono (sqRanges_win _)) (winRanges_low _) hEZ hn
  refine ⟨⟨h4, h128, hEZ, _, bm, hct, hodd, hc1, tab_lt hT (by omega_using [hc1]),
    by rw [hYt]; exact Nat.mod_lt _ (by omega_using [hc1])⟩, ?_⟩
  rw [hf.word_eq (by unfold sqRanges; w_disj) (by simp only [kV, kT0, sCnt, sFn]; omega_arith)]
  exact hI.v

theorem winDigitC_ok {r : (CPub × Nat) × Nat} {s : State} (h : WVc r s) :
    WP isa (.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]) s (WDc r) :=
  WP.mono (winDigit_ok h.1.ws h.2) fun t ⟨hm, k⟩ =>
    ⟨h.1.of_frm (rs := [(8 * kG, 8)]) (by rw [hm]; exact frm_hdr (show kG < 32 by decide) _ (by simp))
      (by simp [wkRanges]) k (by decide), by rw [hm, word_writeW_self]; rfl⟩

/-- The selection's registers, after its first block. -/
def selValC (r : (CPub × Nat) × Nat) : Reg → BitVec 64
  | .x0 => r.1.1.1.B
  | .x12 => BitVec.ofNat 64 r.1.1.1.w
  | .x16 => off r.1.1.1.B (slot r.1.1.1.w (aT0 + pubDigit r))
  | _ => off r.1.1.1.B (slot r.1.1.1.w aXm)

/-- The selection: its first block pins the entry's base, by the public digit. -/
theorem publicSel_ct : RelCT isa (Two WDc) (seqs publicSel) (Two WWX) := by
  have e : seqs publicSel = Code.seq _ _ := rfl
  rw [e]
  refine (pin_ct (Ψ := fun r s => WWX r.1.1.1 s) [.x0] [.x0, .x12, .x16, .x17] selValC
    (pins_ws' (fun r : (CPub × Nat) × Nat => r.1.1.1.B) (fun r => r.1.1.1.Z) (fun r => r.1.1.1.w)
      fun _ _ h => h.1.ws)
    (by taint_decide) (fun r s h => ?_) (by taint_decide) fun r s h => ?_).mono (fun _ _ h => h)
      (fun _ _ ⟨r, h₁, h₂, hsp⟩ => ⟨r.1.1.1, h₁, h₂, hsp⟩)
  · refine WP.mono (publicSelHead_ok h.1.ws h.2) fun t ⟨⟨h16, h17, h12, _⟩, k⟩ x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans h.1.ws.x0
    · exact h12
    · exact h16
    · exact h17
  · rw [← e]
    obtain ⟨⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩, hG⟩ := h
    have hd : pubDigit r < 16 := top_nibble _
    have hn := hc.ws.scr.nowrap
    refine WP.mono (publicSel_selOK hc.ws hEZ hd hG) fun t ⟨hv, ho, _, k⟩ => ?_
    have hf : Frm r.1.1.1.B [(slot r.1.1.1.w aXm, 8 * (r.1.1.1.w + 2))] s.mem t.mem :=
      Frm.of_outside (ho.mono (o' := slot r.1.1.1.w aXm) (n' := 8 * (r.1.1.1.w + 2)) (Nat.le_refl _)
        (by omega_arith)) (by simp)
    obtain ⟨-, -, -, c', bm', hc', hodd', hc1', hT', hY'⟩ :=
      WW.of_frm ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hT, hY⟩ hf (by simp [wkRanges]) k (by decide)
    have hN := hc.ws.sl (show aN < 16 by decide)
    have hn' : c' = c := by rw [← hc'.n, ← hc.n, hf.wv_eq (by w_disj) (by omega_arith)]
    subst hn'
    exact ⟨h4, h128, hEZ, c', bm', hc', hodd', hc1', hT', hY', by rw [hv]; exact hT _ hd⟩

/-- A window leaks the same in runs that agree on the working space and the
candidate. -/
theorem publicWin_ct (M : Mont) :
    RelCT isa (Two fun (r : (CPub × Nat) × Nat) s => r.2 < 16 ∧ WinPc r.1 r.2 s) (seqs (publicWin M.mm))
      fun _ _ => True := by
  rw [publicWin, mrWinS_eq]
  refine RelCT.seqs_append (by simp [mrSq]) (by simp) (RelCT.seq (two_post (Ψ := WVc)
    (two_map (fun r : (CPub × Nat) × Nat => r.1.1.1) (fun r _ h => winP_ww (p := (r.1.1.1, r.1.2)) h.2.winP)
      ((sq4_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun _ _ h => winSq_ok M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [publicSel_ne]) (RelCT.seq (two_post (Ψ := WDc)
    (two_map (fun r : (CPub × Nat) × Nat => r.1.1.1) (fun _ _ h => h.1)
      (digit_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)) fun _ _ h => winDigitC_ok h) ?_)
  exact RelCT.seqs_append publicSel_ne (by simp) (RelCT.seq publicSel_ct (winRest_ct M))

/-! ## The exponentiation -/

/-- Before the exponentiation (`E0`), for the candidate of the public data. -/
def E0c (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧ ∃ bm b, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧
    TabOK s.mem p.1.B p.1.w p.2 b ∧ ECtx s.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2 ∧
    wv s.mem p.1.B (slot p.1.w aY) p.1.w = 2 ^ (64 * p.1.w) % p.2

/-- After `j` words (`WI`), for the candidate of the public data. -/
def WIc (p : CPub) (j : Nat) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧ ∃ bm b s₀,
    WordInv p.1.B p.1.Z p.1.w p.2 bm b s₀ j s ∧ ECtx s₀.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2

theorem WIc.wi {p : CPub} {j : Nat} {s : State} (h : WIc p j s) : WI p.1 j s := by
  obtain ⟨h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩ := h
  exact ⟨h4, h128, hEZ, _, bm, b, s₀, hI, hE, hodd, hc1⟩

/-- The start of a word: its word is the public data's. -/
theorem pubWordHead_ct : RelCT isa (Two fun (q : CPub × Nat) s => q.2 < q.1.1.w ∧ WIc q.1 q.2 s)
    (.block (ws ++ base aE .x16 ++ wordHead)) (Two fun q s => 0 < 16 ∧ WinPc q 0 s) :=
  two_post (two_map (fun q : CPub × Nat => (q.1.1, q.2)) (fun _ _ h => ⟨h.1, h.2.wi⟩)
      (wordHead_ct.mono (fun _ _ h => h) fun _ _ _ => trivial))
    fun q s ⟨hj, h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩ => by
      have hW : (wordE s.mem q.1.1.B q.1.1.w q.2).toNat =
          mrE q.1.2 / 2 ^ (64 * (q.1.1.w - q.2 - 1)) % 2 ^ 64 := by
        have hE' : ECtx s.mem q.1.1.B q.1.1.w q.1.2 :=
          hE.of_low hI.frm (expRanges_low q.1.1.w) hEZ hI.ctx.ws.scr.nowrap
        rw [← hE'.e]; exact word_of_wv s.mem q.1.1.B (slot q.1.1.w aE) q.1.1.w (by omega_using [hj])
      have e : wordE s.mem q.1.1.B q.1.1.w q.2 = pubWord q.1.2 q.1.1.w q.2 :=
        BitVec.eq_of_toNat_eq (by rw [hW, pubWord_toNat])
      refine WP.mono (wordStart_ok hEZ hj hI) fun t hB => ?_
      rw [e] at hB
      exact ⟨by decide, h4, h128, hEZ, hj, bm, b, s₀, hB, hE, hodd, hc1⟩

/-- The windows of a word. -/
theorem pubWins_ct (M : Mont) : RelCT isa (Two fun (q : CPub × Nat) s => 0 < 16 ∧ WinPc q 0 s)
    (.loop (seqs (publicWin M.mm)) (.nonzero .x .x3)) (Two fun q s => WinPc q 16 s) := by
  refine two_loop (Φ := WinPc) (fun _ => 16) (publicWin_ct M) ?_
  rintro q i s hi ⟨h4, h128, hEZ, hj, bm, b, s₀, hI, hE, hodd, hc1⟩
  exact WP.mono (mrWinStepW_ok (publicWin_winOK M) h128 hEZ hodd hc1 (by omega_using [hj]) (by omega_using [])
    (pubWord_toNat _ _ _) hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h128, hEZ, hj, bm, b, s₀, hI', hE, hodd, hc1⟩,
      fun e => e ▸ ⟨h4, h128, hEZ, hj, bm, b, s₀, hI', hE, hodd, hc1⟩⟩

/-- One word. -/
theorem pubWordLoop_ct (M : Mont) : RelCT isa (Two fun (q : CPub × Nat) s => q.2 < q.1.1.w ∧ WIc q.1 q.2 s)
    (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (publicWin M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) fun _ _ => True :=
  RelCT.seq pubWordHead_ct (RelCT.seq (pubWins_ct M) (two_taint [.x0]
    (pins_ws' (fun q : CPub × Nat => q.1.1.B) (fun q => q.1.1.Z) (fun q => q.1.1.w)
      fun q _ h => (winP_ww (p := (q.1.1, q.2)) h.winP).ws) (by taint_decide)))

/-- The exponentiation leaks the same in runs that agree on the working
space and the candidate. -/
theorem publicExpLoop_ct (M : Mont) :
    RelCT isa (Two E0c) (seqs (mrExpLoopW (publicWin M.mm) M.mm)) fun _ _ => True := by
  rw [mrExpLoopW_eq]
  refine RelCT.seqs_append (by simp) (by simp [mrLast]) (RelCT.seq (?_ : RelCT isa (Two E0c) _ (Two WLast))
    (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (j := 1) (by decide))
      (ct_app' (by simp [mrLast]) (by simp [mrLast]) (mrLast_ct M (j := 2) (by decide))
        ((mrLast_ct M (j := 3) (by decide)).mono (fun _ _ h => h) fun _ _ _ => trivial))))
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.1.w ∧ WIc p 0 s) [.x0]
    (pins_ws' (fun p : CPub => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide)
    fun p s ⟨h4, h128, hEZ, bm, b, hc, hT, hE, hodd, hc1, hY⟩ => WP.mono (expStart_ok hEZ hc hT hY) fun t hI =>
      ⟨by omega_using [h4], h4, h128, hEZ, bm, b, s, hI, hE, hodd, hc1⟩) ?_
  refine (two_loop (Φ := WIc) (Ψ := fun p s => WLast p.1 s) (fun p => p.1.w) (pubWordLoop_ct M) ?_).mono
    (fun _ _ h => h) (fun _ _ ⟨p, h₁, h₂, hsp⟩ => ⟨p.1, h₁, h₂, hsp⟩)
  rintro p j s hj ⟨h4, h128, hEZ, bm, b, s₀, hI, hE, hodd, hc1⟩
  refine WP.mono (mrWordW_ok (publicWin_winOK M) h128 hEZ
    (hE.of_low hI.frm (expRanges_low p.1.w) hEZ hI.ctx.ws.scr.nowrap) hodd hc1 hj hI)
    fun t ⟨hI', hz⟩ => ⟨eval_cnt .x3 hj hz, fun _ => ⟨h4, h128, hEZ, bm, b, s₀, hI', hE, hodd, hc1⟩, fun _ => ?_⟩
  have hn := hI'.ctx.ws.scr.nowrap
  exact ⟨⟨h4, h128, hEZ, _, bm, hI'.ctx, hodd, hc1, tab_lt hI'.tab (by omega_using [hodd]),
    by rw [hI'.y]; exact Nat.mod_lt _ (by omega_using [hodd])⟩,
    by rw [hI'.ctx.n]; exact hE.of_low hI'.frm (expRanges_low p.1.w) hEZ hn, _, hI'.flag⟩

/-! ## The round -/

/-- A prepared input (`CorePre`), for the candidate of the public data. -/
def CorePreC (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧
    ∃ bm b, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧ ECtx s.mem p.1.B p.1.w p.2 ∧ p.2 % 2 = 1 ∧ 1 < p.2 ∧
      wv s.mem p.1.B (slot p.1.w aXm) p.1.w = Spec.Rsa.powMod b 1 p.2 * 2 ^ (64 * p.1.w) % p.2

theorem publicCore_ct (M : Mont) :
    RelCT isa (Two CorePreC) (seqs (preparedRoundW (publicWin M.mm) M.mm)) fun _ _ => True := by
  unfold preparedRoundW
  refine RelCT.seqs_append (by simp [tabBuild]) (by simp [mrExpLoopW]) (RelCT.seq (two_post (Ψ := E0c)
    (two_map (fun p : CPub => p.1) (fun p s h => ?_)
      ((tabBuild_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)) ?_) (publicExpLoop_ct M))
  · obtain ⟨h4, hw, hEZ, bm, b, hc, hE, hodd, hc1, hX⟩ := h
    exact ⟨h4, hw, hEZ, _, bm, b, hc, hodd, hc1, hX⟩
  · rintro p s ⟨h4, hw, hEZ, bm, b, hc, hE, hodd, hc1, hX⟩
    have hEn : p.1.B.toNat + slot p.1.w aE + 8 * (p.1.w + 1) ≤ 2 ^ 64 := by
      have := hc.ws.scr.nowrap
      omega_arith
    exact WP.mono (tabBuild_ok M hw hEZ hc hodd hc1 hX) fun t ⟨ht, htab, hy, hf, hk⟩ =>
      ⟨h4, hw, hEZ, bm, b, ht, htab,
        hE.of_frm hf (fun r hr => Or.inr (VG.Proof.MillerRabin.AArch64.tab_below_exp p.1.w r hr)) hEn, hodd, hc1, hy⟩

theorem publicCore_base (M : Mont) (p : CPub) (s : State) (h : CorePreC p s) :
    WP isa (seqs (preparedRoundW (publicWin M.mm) M.mm)) s fun t => t.gpr .x0 = p.1.B := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, hE, hodd, h1, hX⟩ := h
  have hfit : mrE p.2 < 16 ^ (16 * p.1.w) := by
    change mrE p.2 < (2 ^ 4) ^ (16 * p.1.w)
    rw [← Nat.pow_mul, show 4 * (16 * p.1.w) = 64 * p.1.w by omega_arith]
    have hn : p.2 < 2 ^ (64 * p.1.w) := hc.n ▸ wv_lt s.mem p.1.B (slot p.1.w aN) p.1.w
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)
  exact WP.mono (VG.Proof.MillerRabin.AArch64.coreW_ok (publicWin_winOK M) M h128 hEZ hc hE hodd
    (by omega_arith) hfit hX) fun t ⟨ht, _⟩ => ht.ws.x0

theorem publicRound_rel (M : Mont) : RelCT isa (Two CorePreC) (publicRound M.mm) fun _ _ => True := by
  change RelCT isa _ (.seq (seqs (preparedRoundW (publicWin M.mm) M.mm))
    (.block VG.Impl.MillerRabin.AArch64.returnFlag)) _
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = p.1.B) (publicCore_ct M) (publicCore_base M)) ?_
  exact two_taint [.x0] (fun p s t hs ht r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hs.trans ht.symm) (by unfold VG.Impl.MillerRabin.AArch64.returnFlag; taint_decide)

/-- The candidate of a prepared workspace. -/
def candidateOf (s : State) : Nat :=
  Proof.Rsa.Mont.numAt s.mem (s.gpr .x0) (Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)) 0

/-- What runs of the round for public candidates may agree on: the shared
round's (`roundPub`), and the candidate. -/
def publicRoundPub (s t : State) : Prop :=
  VG.Proof.MillerRabin.AArch64.roundPub s t ∧ candidateOf s = candidateOf t

/-- The shared round's contract, with the candidate public too. -/
def publicRoundContract : Contract isa where
  pre := VG.Proof.MillerRabin.AArch64.roundPre
  post := VG.Proof.MillerRabin.AArch64.roundPost
  pub := publicRoundPub

private def coreSpace (s : State) : VG.Proof.Bignum.AArch64.Ws :=
  ⟨s.gpr .x0, (s.gpr .x1).toNat * 8, Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)⟩

private theorem initial_core {s : State} (h : VG.Proof.MillerRabin.AArch64.roundPre s) :
    CorePreC (coreSpace s, candidateOf s) s := by
  unfold candidateOf
  obtain ⟨h4, h128, hEZ, bm, hc, hE, hodd, h3, hx⟩ := VG.Proof.MillerRabin.AArch64.initial_ctx h
  obtain ⟨b, -, hb⟩ := VG.Proof.MillerRabin.witness_exists (coprime_pow2 hodd _) hx
  refine ⟨h4, h128, hEZ, bm, b, hc, hE, hodd, by omega_arith, ?_⟩
  simpa only [coreSpace, VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb

/-- The round for public candidates leaks only the working space's place and
size, and the candidate. -/
theorem publicRound_ct (M : Mont) :
    ConstantTime isa VG.Proof.MillerRabin.AArch64.roundPre publicRoundPub (publicRound M.mm) := by
  apply RelCT.constantTime
  refine (publicRound_rel M).mono (fun s t ⟨hs, ht, hp⟩ => ?_) (fun _ _ h => h)
  obtain ⟨⟨hsp, h0, h1, hw⟩, hc⟩ := hp
  have hL : (coreSpace s, candidateOf s) = (coreSpace t, candidateOf t) := by
    unfold coreSpace
    rw [hw, h0, h1, hc]
  exact ⟨(coreSpace s, candidateOf s), initial_core hs, hL.symm ▸ initial_core ht, hsp⟩

end VG.Proof.Dsa.AArch64.Generation
