module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
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
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Rsa.Ranges

/-! ### `Dsa.AArch64.Generation.PublicRoundCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PublicRound`, which only this module used -/

section

/-!
# DSA parameter generation on AArch64: the round for public candidates

`publicSel` does what the masked selection does (`publicSel_selOK`), so the
round with it is the shared round's (`publicRound_correct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aXm)

/-- The base of entry `d`, from `T_0`'s and `d` strides. -/
theorem entry_base (B : Addr) (w d : Nat) :
    off B (slot w aT0) + BitVec.ofNat 64 d * BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (aT0 + d)) := by
  rw [← BitVec.ofNat_mul, off_add]
  congr 1
  unfold slot
  rw [Nat.add_mul]
  omega_using []

/-- The selection's head: the bases of `aXm` and of entry `d`. -/
theorem publicSelHead_ok {s : State} {B : Addr} {Z w d : Nat} (h : Ws s B Z w)
    (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 d) :
    WP isa (.block (ws ++ base aXm .x17 ++ base aT0 .x16 ++
      ([ldh .x9 kG, .mul .x .x9 .x9 .x11, .add .x .x16 .x16 .x9] : List Instr))) s fun t =>
      (t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.gpr .x17 = off B (slot w aXm) ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.x9, .x11, .x12, .x16, .x17] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aXm .x17 h0₁ h11) fun s₂ ⟨⟨h17, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aT0 .x16 ((k₂.gpr .x0 (by decide)).trans h0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (WP.keep [.x9, .x16] (Q := fun t => t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kG < 32 by decide),
      (hs.congr k13.wr).ld (d := 8 * kG) (by simp only [kG]; omega_using [h256]), (by rw [m₃, m₂, m₁]; exact hG :
        word s₃.mem B (8 * kG) = BitVec.ofNat 64 d), h16, (k₂.trans k₃ |>.gpr .x11 (by decide)).trans h11,
      entry_base])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16t, hm⟩, k⟩ => ?_
  exact ⟨⟨h16t, (k₃.trans k |>.gpr .x17 (by decide)).trans h17,
    (k₂.trans k₃ |>.trans k |>.gpr .x12 (by decide)).trans h12, by rw [hm, m₃, m₂, m₁]⟩,
    (k13.trans k).mono (by decide)⟩

/-- `publicSel`: `[aXm] := T_d` for the digit `d` in `kG`, as `mrSel_ok`. -/
theorem publicSel_selOK : SelOK publicSel := by
  intro s B Z w d h hEZ hd hG
  have hn := h.scr.nowrap
  have hT := tab_fits (w := w) hEZ hd
  have hX := tab_sep_xm w (j := d)
  have hXZ := h.sl (show aXm < 16 by decide)
  simp only [publicSel, seqs]
  refine WP.seq (WP.mono (publicSelHead_ok h hG) fun s₁ ⟨⟨h16, h17, h12, m₁⟩, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.wr
  refine WP.mono (copyWords_ok h16 h17 h12 (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [hn, hXZ])
    (fun i hi => hs₁.ld (by omega_using [hT, hi])) (fun i hi => hs₁.st (by omega_using [hXZ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hn, hT, hi, hb])]; omega_using [hX, hi, hb]))
    fun t ⟨hv, _, o, _, _, k₂⟩ => ?_
  rw [m₁] at hv o
  exact ⟨hv, o, h.scr.congr (k₁.trans k₂).wr, (k₁.trans k₂).mono (by decide)⟩

theorem publicSel_ne : publicSel ≠ [] := by unfold publicSel; exact List.cons_ne_nil _ _

theorem publicWin_winOK (M : Mont) : WinOK (publicWin M.mm) := mrWinS_winOK publicSel_ne publicSel_selOK M

/-- The round for public candidates meets the shared round's contract. -/
theorem publicRound_correct (M : Mont) (s : State) (h : roundContract.pre s) :
    ∃ tr t, Exec isa (publicRound M.mm) s tr t ∧ abiPreserved s t ∧ roundContract.post s t :=
  roundW_correct (publicWin_winOK M) M s h

end VG.Proof.Dsa.AArch64.Generation

end

end

/-!
# DSA parameter generation on AArch64: constant time of the round for public candidates

Runs of `publicRound` leak the same when they agree on the working space
and on the candidate: the exponent's windows are then the same, and with
them the table entry each window reads (`publicSel_ct`, its address pinned
by correctness). Everything else is the shared round's, piece by piece
(`Proof/RsaKeyGen/AArch64/CTMrTab.lean`, `CTMrExp.lean`).
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

end

end

/-!
# DSA parameter generation on AArch64: the kernel of its round

`PublicKernel` is `MillerRabin.AArch64.Kernel` for a public candidate: its
runs leak the same when they agree on the working space and the candidate
(`BeforeC`), not on the working space alone. `PublicKernel.called` calls
`publicRound` as `Kernel.called` calls the shared round.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Proof.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)

/-- Before the call (`Caller.Before`), for the candidate of the public data. -/
def BeforeC (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧
    ∃ bm b : Nat, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧ ECtx s.mem p.1.B p.1.w p.2 ∧
      p.2 % 2 = 1 ∧ 3 ≤ p.2 ∧ wv s.mem p.1.B (slot p.1.w aXm) p.1.w = b % p.2 * 2 ^ (64 * p.1.w) % p.2

theorem BeforeC.before {p : CPub} {s : State} (h : BeforeC p s) : Before p.1 s := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  exact ⟨h4, h128, hEZ, _, bm, b, hc, he, ho, h3, hx⟩

/-- After the registers are saved (`Caller.Ready`). -/
def ReadyC (p : CPub) (s : State) : Prop :=
  BeforeC p s ∧ s.gpr .x19 = p.1.B ∧ s.gpr .x1 = BitVec.ofNat 64 (callWords p.1.w)

theorem ReadyC.ready {p : CPub} {s : State} (h : ReadyC p s) : Ready p.1 s := ⟨h.1.before, h.2⟩

theorem save_readyC {p : CPub} {s : State} (h : BeforeC p s) : WP isa (.block save) s (ReadyC p) := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good.1 hc.good.2 h128) ?_
  rintro t ⟨hm, h19, h1, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hEZ hm hk
  refine ⟨⟨h4, h128, hEZ, bm, b, hct, het, ho, h3, ?_⟩, h19, h1⟩
  rw [hm, (saved_outside s p.1.B p.1.w (by
    have hz : slot p.1.w 16 ≤ p.1.Z := hc.ws.hZ
    have hn := hc.ws.scr.nowrap
    simp only [pad, slot, hdrBytes, aOne] at hz ⊢
    omega_arith)).wv (Or.inl (by simp only [pad, slot, hdrBytes, aOne, aXm]; omega_arith))
      (by
        have hsX := slot_le (w := p.1.w) (show aXm < 8 by decide)
        have hsZ := hc.good.2
        have hsN := hc.ws.scr.nowrap
        omega_arith)]
  exact hx

/-- The candidate the call's callee sees. -/
theorem ready_candidate {p : CPub} {s : State} (h : ReadyC p s) :
    candidateOf (narrowed s p.1.B p.1.w) = p.2 := by
  have h0 : (narrowed s p.1.B p.1.w).gpr .x0 = p.1.B := (s.callEntry_gpr (by decide)).trans (ready_base h.ready)
  obtain ⟨⟨_, _, _, bm, b, hc, _⟩, _⟩ := h
  have hw : Proof.Rsa.Mont.wOf s.mem p.1.B = p.1.w := ctx_width hc
  unfold candidateOf
  rw [h0]
  change Proof.Rsa.Mont.numAt s.mem p.1.B (Proof.Rsa.Mont.wOf s.mem p.1.B) 0 = p.2
  rw [hw, VG.Proof.Bignum.AArch64.MontFn.numAt_eq]
  exact hc.n

theorem publicPrepared_call_ct (M : Mont) (name : String) :
    RelCT isa (Two ReadyC) (.call name (publicRound M.mm)) fun _ _ => True := by
  apply RelCT.callEx (k := publicRoundContract) (publicRound_correct M) (publicRound_ct M)
  rintro s t ⟨p, hs, ht, hsp⟩
  have hcs := ready_covers hs.ready
  have hct := ready_covers ht.ready
  exact ⟨[], [⟨p.1.B, 8 * callWords p.1.w⟩], [], [⟨p.1.B, 8 * callWords p.1.w⟩],
    ready_pre hs.ready, ready_pre ht.ready,
    ⟨ready_pub hs.ready ht.ready hsp, (ready_candidate hs).trans (ready_candidate ht).symm⟩,
    Covers.right hcs, hcs, Covers.right hct, hct⟩

/-- A call of the round for public candidates leaks the same in runs that
agree on the working space and the candidate. -/
theorem publicCall_ct (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    RelCT isa (Two BeforeC) (call name (publicRound M.mm)) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.AArch64.Caller.call
  refine RelCT.seq (two_post (Ψ := ReadyC) ?_ (fun _ _ h => save_readyC h)) ?_
  · exact save_ct.mono (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p.1, before_good hs.before, before_good ht.before, hsp⟩)
      (fun _ _ h => h)
  · exact RelCT.seq (two_post (Ψ := fun p s => RestorePre p.1 s) (publicPrepared_call_ct M name)
      (fun _ _ h => call_restore_pre (publicRound_correct M) name hnf h.ready))
      (two_map (fun p : CPub => p.1) (fun _ _ h => h) restore_ct)

/-- The round for public candidates has no frames where the shared round has none:
they differ in the selection, which is blocks and a loop. -/
theorem publicRound_noFrames {mul : Nat → Nat → Nat → Prog isa}
    (h : (VG.Impl.MillerRabin.AArch64.round mul).noFrames = true) : (publicRound mul).noFrames = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self]
  exact h

/-- A prepared round for a public candidate: `Kernel`, but its runs agree on
the candidate too. -/
structure PublicKernel where
  run : List (Prog isa)
  nonempty : run ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat},
    MrCtx s B Z w c bm → ECtx s.mem B w c → 4 ≤ w → w ≤ 128 →
    slot w aE + 8 * (w + 2) ≤ Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa (seqs run) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two BeforeC) (seqs run) fun _ _ => True

/-- A call of the round for public candidates, keeping its workspace for the policy. -/
def PublicKernel.called (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    PublicKernel where
  run := [call name (publicRound M.mm)]
  nonempty := by simp
  ok := by exact Caller.call_result_ok (publicRound_correct M) name hnf
  ct := by exact publicCall_ct M name hnf

/-- The name of the round for public candidates that goes with a shared round. -/
def publicRoundName (v : RoundImpl) : String := "vg_dsa_miller_rabin_round" ++ v.suffix

/-- The kernel of DSA's parameter search for an implementation of the shared
round: the round for public candidates over the same multiplication. -/
def publicKernel (v : RoundImpl) : PublicKernel :=
  PublicKernel.called v.roundMont (publicRoundName v) (publicRound_noFrames v.noFrames)

end VG.Proof.Dsa.AArch64.Generation
