module

import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTDraw
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# An FFDH parameter candidate on AArch64: constant time of Miller–Rabin

`millerRabin_ct`: the loop runs `mrIters` times, which the public data
fixes, the `j`-th iteration from `u₀ + j ⌈mb / 8⌉` octets read.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The public data of the witnesses of a modulus: the candidate's, the
modulus's, and the octets read before them. -/
structure TQ where
  p : PP
  w : Nat
  N : Nat
  mb : Nat
  K : Nat
  u : Nat

/-- The result. -/
abbrev TQ.res (q : TQ) : Option (Bool × List Byte) := checkWitnesses q.N q.K (q.p.r.drop q.u)

/-- The octets read before iteration `j`. -/
abbrev TQ.uj (q : TQ) (j : Nat) : Nat := q.u + j * mLen q.mb

/-- The iterations. -/
abbrev TQ.n (q : TQ) : Nat := mrIters q.N q.K q.mb q.p.r (q.p.r.length + 1) 0 q.u

/-- At the head of iteration `j`. -/
def TL (q : TQ) (j : Nat) (s : State) : Prop :=
  MrDims q.p q.w q.N q.mb q.K ∧ ∃ s₀ i, MrSt q.p q.w q.N q.mb q.K s₀ q.res i (q.uj j) s ∧
    mrIters q.N q.K q.mb q.p.r (q.p.r.length + 1 - j) i (q.uj j) = q.n - j

/-- After the loop. -/
def TE (q : TQ) (s : State) : Prop := MrDims q.p q.w q.N q.mb q.K ∧ ∃ s₀, MrEnd q.p q.w q.N q.mb q.K s₀ q.res s

theorem MrSt.same {p : PP} {w N mb K : Nat} {s₀ : State} {res : Option (Bool × List Byte)} {i u : Nat}
    {s t : State} (h : MrSt p w N mb K s₀ res i u s) (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : ∀ r ∈ regs, r ∈ mmRegs) : MrSt p w N mb K s₀ res i u t :=
  ⟨h.fix.same hEZ hm k (fun h' => by have := hr _ h'; simp [mmRegs] at this), by rw [hm]; exact h.used,
    by rw [hm]; exact h.idx, h.ul, h.ik, h.rest, by rw [hm]; exact h.isc, (h.keep.trans k).mono fun r hr' => by
      rcases List.mem_append.mp hr' with h' | h'
      · exact h'
      · exact hr r h'⟩

theorem tl_ws {q : TQ} {j : Nat} {s : State} (h : TL q j s) : Ws s q.p.B q.p.Z q.w := by
  obtain ⟨-, s₀, i, hs, -⟩ := h
  exact hs.fix.st.ws

/-- Before the branch on `rand`'s length. -/
def TR (a : TQ × Nat) (s : State) : Prop :=
  TL a.1 a.2 s ∧ isa.eval (.zero .x .x5) s = some (decide (a.1.p.r.length < a.1.uj a.2 + mLen a.1.mb))

/-- The short end. -/
theorem shortEnd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [movi .x3 0, sth .x3 kStat]) s fun t => Ws t B Z w := by
  have hs := h.scr
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), hs.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have ft : Frm B [(8 * kStat, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  exact h.congr' ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) k (by decide)

/-- An iteration leaks the same in runs with the same public data. -/
theorem mrBody_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (a : TQ × Nat) s => a.2 < a.1.n ∧ TL a.1 a.2 s)
    (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) fun _ _ => True := by
  have pw : ∀ {Φ : TQ × Nat → State → Prop}, (∀ a s, Φ a s → Ws s a.1.p.B a.1.p.Z a.1.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun a : TQ × Nat => a.1.p.B) (fun a : TQ × Nat => a.1.p.Z) (fun a : TQ × Nat => a.1.w) h
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := TR) [.x0] (pw fun _ _ h => tl_ws h.2) (by taint_decide) ?_)
    (RelCT.seq (R := Two fun (a : TQ × Nat) t => Ws t a.1.p.B a.1.p.Z a.1.w)
      (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
        (two_piece [.x0] (pw fun _ _ h => tl_ws h.1.1) (by taint_decide) fun _ _ h => shortEnd_ok (tl_ws h.1.1))
        (two_post (two_map (Φ' := DA) (fun a : TQ × Nat =>
            (⟨a.1.p, a.1.w, a.1.N, a.1.mb, a.1.K, a.1.uj a.2⟩ : DD)) ?_ (draw_ct M R)) ?_))
      (two_taint [.x0] (pw fun _ _ h => h) (by taint_decide)))
  · rintro ⟨q, j⟩ s ⟨hj, hd, s₀, i, hs, hit⟩
    have hEZ := hd.eZ
    have hmb2 : q.mb ≤ 8192 := hd.mb2
    exact WP.mono (roomHead_ok (len := mLen q.mb) hs.fix.st.ws (by simp only [mLen]; omega_arith)
      hs.fix.st.dims.rl hs.ul hs.fix.len hs.fix.st.args.rlen hs.used)
      fun t ⟨hz, hm, k⟩ => ⟨⟨hd, s₀, i, hs.same hEZ hm k (by decide), hit⟩, hz⟩
  · rintro ⟨q, j⟩ s ⟨⟨⟨hd, s₀, i, hs, hit⟩, hz⟩, hb⟩
    have hb' : ¬ q.p.r.length < q.uj j + mLen q.mb := by
      intro h'; rw [hz] at hb; simp only [h', decide_true, Option.some.injEq] at hb; cases hb
    have hK : q.K < 2 ^ 62 := hd.k
    have hik : i < q.K := hs.ik
    exact ⟨hd, hs.fix, hs.used, ⟨i, hs.idx, (by omega_arith : i < 2 ^ 62)⟩,
      (by omega_arith : q.uj j + mLen q.mb ≤ q.p.r.length)⟩
  · rintro ⟨q, j⟩ s ⟨⟨⟨hd, s₀, i, hs, hit⟩, hz⟩, hb⟩
    have hb' : ¬ q.p.r.length < q.uj j + mLen q.mb := by
      intro h'; rw [hz] at hb; simp only [h', decide_true, Option.some.injEq] at hb; cases hb
    have hK : q.K < 2 ^ 62 := hd.k
    have hik : i < q.K := hs.ik
    exact WP.mono (draw_ok (i := i) (u := q.uj j) M R hd hs.fix hs.used hs.idx (by omega_arith : i < 2 ^ 62)
      (by omega_arith : q.uj j + mLen q.mb ≤ q.p.r.length))
      fun t ⟨hf, _⟩ => hf.st.ws

theorem mrIters_pos (N K mb : Nat) (r : List Byte) (f i u : Nat) : 1 ≤ mrIters N K mb r f i u := by
  cases f with
  | zero => simp only [mrIters]; omega_arith
  | succ f => simp only [mrIters]; split <;> (try split) <;> (try split) <;> omega_arith

/-- The loop leaks the same in runs with the same public data. -/
theorem mrLoop_ct (M : Mont) (R : Kernel) : RelCT isa (Two fun (q : TQ) s => 0 < q.n ∧ TL q 0 s)
    (.loop (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (draw M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)) (Two TE) := by
  refine two_loop (Φ := TL) TQ.n (mrBody_ct M R) ?_
  rintro q j s hj ⟨hd, s₀, i, hs, hit⟩
  have hul : q.u + j * mLen q.mb ≤ q.p.r.length := hs.ul
  have hl1 : 1 ≤ mLen q.mb := by have : 511 ≤ q.mb := hd.mb1; simp only [mLen]; omega_arith
  have hjl : j ≤ q.p.r.length := by
    have : j * 1 ≤ j * mLen q.mb := Nat.mul_le_mul_left _ hl1
    omega_arith
  obtain ⟨f, hf⟩ : ∃ f, q.p.r.length + 1 - j = f + 1 := ⟨q.p.r.length - j, by omega_arith⟩
  rw [hf] at hit
  refine WP.mono (mrIter_ok M R hd hs) fun t ht => ?_
  rcases ht with ⟨he, hend, h1⟩ | ⟨he, i', hs', hstep⟩
  · rw [h1 f] at hit
    have hn1 : ¬ j + 1 < q.n := by omega_arith
    refine ⟨by rw [he]; exact congrArg some (decide_eq_false hn1).symm, fun h => absurd h hn1,
      fun _ => ⟨hd, s₀, hend⟩⟩
  · rw [hstep f] at hit
    have hpos := mrIters_pos q.N q.K q.mb q.p.r f i' (q.uj j + mLen q.mb)
    have hn1 : j + 1 < q.n := by omega_arith
    refine ⟨by rw [he]; exact congrArg some (decide_eq_true hn1).symm, fun _ => ?_,
      fun h => absurd h (by omega_arith)⟩
    have hu : q.uj j + mLen q.mb = q.uj (j + 1) := by simp only [TQ.uj, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [hu] at hs'
    refine ⟨hd, s₀, i', hs', ?_⟩
    rw [show q.p.r.length + 1 - (j + 1) = f by omega_arith, ← hu]
    omega_arith

/-- Before `millerRabin`. -/
def TP (q : TQ) (s : State) : Prop :=
  MrDims q.p q.w q.N q.mb q.K ∧ MrFix q.p q.w q.N q.mb q.K s ∧
    word s.mem q.p.B (8 * kUsed) = BitVec.ofNat 64 q.u ∧ q.u ≤ q.p.r.length ∧ 1 ≤ q.K

/-- `millerRabin` leaks the same in runs with the same public data. -/
theorem millerRabin_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two TP) (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run)) (Two TE) := by
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin
  simp only [seqs]
  refine RelCT.seq (two_piece [.x0] (pins_ws' (fun q : TQ => q.p.B) (fun q : TQ => q.p.Z) (fun q : TQ => q.w)
    fun _ _ h => h.2.1.st.ws) (by taint_decide) ?_) (mrLoop_ct M R)
  rintro q s ⟨hd, h, hU, hul, hK1⟩
  have hEZ := hd.eZ
  have hs := h.st.ws.scr
  have h256 := h.st.ws.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off q.p.B (8 * fIdx)) (BitVec.ofNat 64 0))
    (by
      brun [h.st.ws.x0, hdr_enc (show fIdx < 32 by decide), hs.st (d := 8 * fIdx) (by simp only [fIdx]; omega_arith)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have ft : Frm q.p.B [(8 * fIdx, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have ht : MrFix q.p q.w q.N q.mb q.K t := h.of_frm hEZ ft (by kmut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega_arith)
    k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
  have hst : MrSt q.p q.w q.N q.mb q.K s q.res 0 (q.uj 0) t :=
    ⟨ht, by
      rw [ft.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]
      simpa only [TQ.uj, Nat.zero_mul, Nat.add_zero] using hU,
      by rw [hm, word_writeW_self], by simpa only [TQ.uj, Nat.zero_mul, Nat.add_zero] using hul, by omega_arith,
      by simp only [TQ.res, TQ.uj, Nat.sub_zero, Nat.zero_mul, Nat.add_zero],
      InScr.of_frm ft fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fIdx]; omega_arith, k.mono (by decide)⟩
  have hn : 0 < q.n := by
    simp only [TQ.n]
    cases q.p.r.length + 1 with
    | zero => simp only [mrIters]; omega_arith
    | succ f => simp only [mrIters]; split <;> (try split) <;> (try split) <;> omega_arith
  exact ⟨hn, hd, s, 0, hst, by simp only [TQ.uj, Nat.sub_zero, Nat.zero_mul, Nat.add_zero]⟩

end VG.Proof.Ffdh.AArch64.ParameterCandidate
