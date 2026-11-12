module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Framework.Omega

/-! # The halvings of Appendix C.2 by stages on i686

`RecoverDetRt.twos`: `u = n - 1`, then the stages of `u ∨ x₂` (word stages of `32 c` bits where
`c < w`, then bit stages `16 … 1`), each shifting `u` and `x₂` down and `x₃` up where the low bits of
both are zero, then the same stages on `u` alone. With `N = n - 1` and `T = tz (gcd N x)`, the joint
stages take `T` and those of `u` alone the rest of `tz N` (`ShiftStages.stage_pair`, `stage_tz`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr)

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {d x y : Nat}

/-- A header word already in memory, added to the stage's words. -/
theorem KS.addSlot (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d)
    (e : slot s.mem g.B d = x) : KS g s0 A live AW liveW (upd V d x) (d :: ls) s :=
  { h with
    sl := fun d' hd' => by
      by_cases eq : d' = d
      · subst eq; rw [upd_self]; exact e
      · rw [upd_ne _ _ eq]; exact h.sl d' ((List.mem_cons.mp hd').resolve_left eq)
    ls_ok := fun d' hd' => (List.mem_cons.mp hd').elim (fun e => e ▸ hd) (h.ls_ok d') }

/-- A header word rewritten: the old one dropped. -/
theorem KS.reslot (h : KS g s0 A live AW liveW (upd (upd V d x) d y) (d :: d :: ls) s) :
    KS g s0 A live AW liveW (upd V d y) (d :: ls) s :=
  h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) fun e he => ⟨List.mem_cons_of_mem _ he, by
    rw [upd_upd]⟩

/-- `body` run `b` times (`b` in `sB`), counted in `sBc`, as a step from `i` to `i + 1`. -/
theorem KS.timesH_ok {b : Nat} {body : Prog isa} (Ai AWi : Nat → Nat → Nat)
    (h : KS g s0 (Ai 0) live (AWi 0) liveW V ls s) (hB : sB ∈ ls) (hVB : V sB = b) (hb : 0 < b)
    (hb32 : b < 2 ^ 32)
    (hbody : ∀ i t, i < b → KS g s0 (Ai i) live (AWi i) liveW (upd V sBc (b - i)) (sBc :: ls) t →
      WP isa body t fun u => KS g s0 (Ai (i + 1)) live (AWi (i + 1)) liveW (upd V sBc (b - i)) (sBc :: ls) u) :
    WP isa (timesH body) s fun t => KS g s0 (Ai b) live (AWi b) liveW (upd V sBc 0) (sBc :: ls) t := by
  refine VG.Proof.Rsa.X86.Recover.timesH_ok
    (fun i t => KS g s0 (Ai i) live (AWi i) liveW (upd V sBc (b - i)) (sBc :: ls) t)
    (fun i t => KS g s0 (Ai (i + 1)) live (AWi (i + 1)) liveW (upd V sBc (b - i)) (sBc :: ls) t)
    hb hb32 h.ws (by rw [h.sl _ hB, hVB]) ?_ hbody ?_ ?_
  · intro t k e r
    rw [Nat.sub_zero]
    exact h.slot1 k (by decide) (r.mono (by decide)) e
  · intro i t _ P
    exact ⟨P.ws, by rw [P.sl _ (List.mem_cons_self ..), upd_self]⟩
  · intro i t u hi P k e r
    have P' := (P.slot1 k (by decide) r e).reslot
    exact ⟨fun _ => P', fun hb' => by subst hb'; rwa [Nat.sub_self] at P'⟩

/-- `downBitsH`: `[aTmp] := [j] / 2^b` (`b` in `sB`). -/
theorem KS.downBits_ok {j b : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ live) (hjT : j ≠ aTmp)
    (hlW : ∀ i ∈ liveW, aTmp / 2 ≠ i) (hB : sB ∈ ls) (hVB : V sB = b) (hb : 0 < b) (hb32 : b < 2 ^ 32) :
    WP isa (downBitsH j) s fun t =>
      KS g s0 (upd A aTmp (A j / 2 ^ b)) (aTmp :: live) AW liveW (upd V sBc 0) (sBc :: ls) t := by
  unfold downBitsH
  refine WP.seq (WP.mono (h.copy_w (o := aTmp) (a := j) (by decide) hj (Ne.symm hjT) hlW) fun u ⟨hu, _, _⟩ => ?_)
  refine KS.timesH_ok (fun i => upd A aTmp (A j / 2 ^ i)) (fun _ => AW)
    (by rw [Nat.pow_zero, Nat.div_one]; exact hu) hB hVB hb hb32 fun i t _ P => ?_
  refine WP.seq (wp_movS rfl fun t1 U _ => WP.block_nil ?_)
  have P1 := P.of_rest U.keeps (by decide) U.mem
  refine WP.mono (P1.half_w (j := aTmp) (by simp) (by rw [U.gpr]; rfl) hlW) fun v ⟨hv, _⟩ => ?_
  refine hv.mono (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  rw [upd_upd, upd_self, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- `[wT] := [wX3] 2^b mod 2^(32 W)` (`b` in `sB`). -/
theorem KS.upBits_ok {b : Nat} (h : KS g s0 A live AW liveW V ls s) (hX : wX3 ∈ liveW)
    (hl : ∀ j ∈ live, j / 2 ≠ wT) (hB : sB ∈ ls) (hVB : V sB = b) (hb : 0 < b) (hb32 : b < 2 ^ 32) :
    WP isa (.seq (VG.Impl.Rsa.X86.KeyRt.copy wid wT wX3)
        (timesH (VG.Impl.Rsa.X86.KeyRt.chain wid .adc wT wT wT false))) s fun t =>
      KS g s0 A live (upd AW wT (AW wX3 * 2 ^ b % 2 ^ (32 * g.W))) (wT :: liveW) (upd V sBc 0) (sBc :: ls) t := by
  have lt : AW wX3 < 2 ^ (32 * g.W) := by rw [← h.arrsW wX3 hX]; exact val32_lt _ _ _ _
  refine WP.seq (WP.mono (h.copy_W (o := wT) (a := wX3) (by decide) hX (by decide) hl) fun u ⟨hu, _⟩ => ?_)
  refine KS.timesH_ok (fun _ => A) (fun i => upd AW wT (AW wX3 * 2 ^ i % 2 ^ (32 * g.W)))
    (by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt lt]; exact hu) hB hVB hb hb32
    fun i t _ P => ?_
  refine WP.mono (P.add_W (o := wT) (a := wT) (b := wT) (by decide) (by simp) (by simp) hl) fun v ⟨hv, _⟩ => ?_
  refine hv.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
  rw [upd_upd, upd_self, ← Nat.two_mul, Nat.mul_comm, Nat.mod_mul_mod, Nat.pow_succ, Nat.mul_assoc]

theorem num_mod32 (m : Mem) (B : Addr) {w : Nat} (j : Nat) (hw : 0 < w) :
    num m B w j % 2 ^ 32 = w32 m B (arr w j) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [num, val32]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- The OR of two narrow numbers' low words, into `eax`. -/
theorem KS.lowOr_ok {a b : Nat} (h : KS g s0 A live AW liveW V ls s) (ha : a ∈ live) (hb : b ∈ live) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.arrPtr nar .esi a .edx ++ VG.Impl.Rsa.X86.KeyRt.arrPtr nar .ebp b .edx ++
      ([.mov .eax (.mem (at_ .esi 0)), .alu .or .eax (.mem (at_ .ebp 0))] : List Instr))) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ (t.gpr .eax).toNat = A a % 2 ^ 32 ||| A b % 2 ^ 32 := by
  have fa := h.ws.arr_fit (h.live_lt a ha)
  have fb := h.ws.arr_fit (h.live_lt b hb)
  have nw := h.rt.rt.nowrap
  have w18 : 18 ≤ g.w := by have := h.lower; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  simp only [S] at fa fb
  rw [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h.rt) h.rt.lenLe h.rt.edi
    (r := .esi) (t := .edx) (j := a) (by decide) (by decide) (by rw [kw_nar]; change arr g.w a < 2 ^ 32; omega) fun u₁ U₁ m₁ p₁ _ => ?_
  have h₁ := h.rt.keep U₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h₁) h₁.lenLe h₁.edi
    (r := .ebp) (t := .edx) (j := b) (by decide) (by decide) (by rw [kw_nar]; change arr g.w b < 2 ^ 32; omega) fun u₂ U₂ m₂ p₂ _ => ?_
  rw [kw_nar] at p₁ p₂
  have ws₂ := (h.rt.rt.of_wr U₁.2.2).of_wr U₂.2.2
  have p₁' : PtrAt u₂ g.B .esi (arr g.w a) := by rw [PtrAt, U₂.1 _ (by decide)]; exact p₁
  refine wp_movS (readSrc_ptr ws₂ p₁' (d := 0) (by omega)) fun u₃ U₃ _ => ?_
  have p₂' : PtrAt u₃ g.B .ebp (arr g.w b) := by rw [PtrAt, U₃.other _ (by decide)]; exact p₂
  refine wp_orS (readSrc_ptr (ws₂.of_wr U₃.wr) p₂' (d := 0) (by omega)) fun u₄ U₄ => WP.block_nil ?_
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, m₂, m₁]
  refine ⟨h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))) (fun x hx => hx) m₄, ?_⟩
  rw [U₄.gpr, U₃.gpr, BitVec.toNat_or, U₃.mem, m₂, m₁, Nat.add_zero, Nat.add_zero, ← h.arrs a ha, ← h.arrs b hb,
    num_mod32 _ _ _ (by omega), num_mod32 _ _ _ (by omega)]

theorem or_low {p q b : Nat} (hb : b ≤ 32) :
    (p % 2 ^ 32 ||| q % 2 ^ 32) % 2 ^ b = 0 ↔ p % 2 ^ b = 0 ∧ q % 2 ^ b = 0 := by
  rw [Nat.or_mod_two_pow, Nat.or_eq_zero_iff, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hb),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hb)]

end

/-! ## A stage -/

/-- The halvings' state: `[aU] = v.1`, `[aX2] = v.2.1`, `[wX3] = v.2.2`, `[aN] = n`, the header word
`d` (a loop's size) `vd` and `sOkDE` `ok`. -/
def TwS (g : Geo) (s0 : State) (ok n : Nat) (v : Nat × Nat × Nat) (d vd : Nat) (s : State) : Prop :=
  ∃ A AW V, KS g s0 A [aU, aX2, aN] AW [wX3] V [d, sOkDE] s ∧ V d = vd ∧ V sOkDE = ok ∧
    A aU = v.1 ∧ A aX2 = v.2.1 ∧ AW wX3 = v.2.2 ∧ A aN = n

/-- Whether a stage of `k` bits shifts: the low `k` bits of `u` and, in a joint stage, of `x₂` are zero. -/
def stP (joint : Bool) (v : Nat × Nat × Nat) (k : Nat) : Prop :=
  v.1 % 2 ^ k = 0 ∧ (if joint then v.2.1 else v.1) % 2 ^ k = 0

instance (joint : Bool) (v : Nat × Nat × Nat) (k : Nat) : Decidable (stP joint v k) := by
  unfold stP; infer_instance

/-- A stage of `k` bits: `u` (and, joint, `x₂`) shifted down and `x₃` up, where it shifts. -/
def stRes (M : Nat) (joint : Bool) (v : Nat × Nat × Nat) (k : Nat) : Nat × Nat × Nat :=
  if stP joint v k then
    (v.1 / 2 ^ k, if joint then v.2.1 / 2 ^ k else v.2.1, if joint then v.2.2 * 2 ^ k % M else v.2.2)
  else v

theorem flag_eq {c : BitVec 32} {P : Prop} [Decidable P] (e : c = 0 ↔ P) :
    (if c = 0 then 1 else 0) = (if P then 1 else 0) := by
  simp only [e]

theorem sel_eq {P : Prop} [Decidable P] (a b : Nat) :
    (if (if P then 1 else 0) = 0 then a else b) = if P then b else a := by
  by_cases hP : P <;> simp [hP]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {AW : Nat → Nat} {V : Nat → Nat}

/-- The common start of a word stage: the flag, and `u` shifted. -/
theorem stageW_pre (joint : Bool) {c : Nat}
    (h : KS g s0 A [aU, aX2, aN] AW [wX3] V [sC4, sOkDE] s) (hV : V sC4 = 4 * c) (hc0 : 0 < c) (hc : c < g.w) :
    WP isa (seqs [orLowH aU (if joint then aX2 else aU), .block flagZero, moveH nar aU aTmp true false,
        VG.Impl.Rsa.X86.KeyRt.sel nar aU aU aTmp sStg]) s fun t =>
      ∃ A' V', KS g s0 A' [aU, aTmp, aU, aX2, aN] AW [wX3] V' [sStg, sC4, sOkDE] t ∧
        V' sStg = (if stP joint (A aU, A aX2, AW wX3) (32 * c) then 1 else 0) ∧ V' sC4 = 4 * c ∧
        V' sOkDE = V sOkDE ∧
        A' aU = (if stP joint (A aU, A aX2, AW wX3) (32 * c) then A aU / 2 ^ (32 * c) else A aU) ∧
        A' aX2 = A aX2 ∧ A' aN = A aN := by
  simp only [seqs]
  refine WP.seq (WP.mono (h.orLowH (a := aU) (b := if joint then aX2 else aU) (c := c) (by simp)
    (by cases joint <;> simp) hc0 (Nat.le_of_lt hc) (by simp) hV) fun t₁ ⟨h₁, _, e₁⟩ => ?_)
  refine WP.seq (WP.mono h₁.flagZero fun t₂ ⟨h₂, _⟩ => ?_)
  have fl : (if t₁.gpr .ecx = 0 then 1 else 0) = (if stP joint (A aU, A aX2, AW wX3) (32 * c) then 1 else 0) :=
    flag_eq (by rw [e₁]; cases joint <;> simp [stP])
  rw [fl] at h₂
  refine WP.seq (WP.mono (h₂.moveDown_w (o := aTmp) (a := aU) (c := c) (by decide) (by simp) (by decide) hc
    (by simp) (by rw [upd_ne _ _ (by decide)]; exact hV) (by decide)) fun t₃ ⟨h₃, _, _⟩ => ?_)
  refine WP.mono (h₃.sel_w (o := aU) (a := aU) (b := aTmp) (sl := sStg) (by decide) (by simp) (by simp)
    (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_
  refine ⟨_, _, h₄, upd_self .., by rw [upd_ne _ _ (by decide)]; exact hV, by rw [upd_ne _ _ (by decide)], ?_,
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)], by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]⟩
  rw [upd_self, upd_self, sel_eq, upd_self, upd_ne _ _ (by decide)]

/-- A word stage of `32 c` bits, `c < w`. -/
theorem stageW_ok (joint : Bool) {ok n c : Nat} {v : Nat × Nat × Nat} (h : TwS g s0 ok n v sC4 (4 * c) s)
    (hc0 : 0 < c) (hc : c < g.w) :
    WP isa (stageWH joint) s (TwS g s0 ok n (stRes (2 ^ (32 * g.W)) joint v (32 * c)) sC4 (4 * c)) := by
  obtain ⟨A, AW, V, h, hd, hok, hU, hY, hZ, hN⟩ := h
  have ev : (A aU, A aX2, AW wX3) = v := by rw [hU, hY, hZ]
  unfold stageWH
  rw [seqs_append_iff]
  refine WP.mono (stageW_pre joint h hd hc0 hc) fun t ⟨A', V', h', f, e1, e2, eU, eY, eN⟩ => ?_
  rw [ev] at f eU
  cases joint
  · refine WP.block_nil ⟨A', AW, V', h'.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), e1, by rw [e2, hok], ?_⟩
    unfold stRes
    rw [eU, eY, eN, hY, hN, hZ]
    split <;> simp [hU]
  · simp only [ite_true, seqs]
    refine WP.seq (WP.mono (h'.moveDown_w (o := aTmp) (a := aX2) (c := c) (by decide) (by simp) (by decide) hc
      (by simp) e1 (by decide)) fun t₁ ⟨h₁, _, _⟩ => ?_)
    refine WP.seq (WP.mono (h₁.sel_w (o := aX2) (a := aX2) (b := aTmp) (sl := sStg) (by decide) (by simp)
      (by simp) (by simp) (by rw [f]; split <;> decide) (.inr (by decide)) (by decide)) fun t₂ ⟨h₂, _⟩ => ?_)
    refine WP.seq (WP.mono (h₂.moveUp_W (o := wT) (a := wX3) (c := c) (by decide) (by simp) (by decide)
      (by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hc; omega) (by simp) e1 (by decide)) fun t₃ ⟨h₃, _, _⟩ => ?_)
    refine WP.mono (h₃.sel_W (o := wX3) (a := wX3) (b := wT) (sl := sStg) (by decide) (by simp)
      (by simp) (by simp) (by rw [f]; split <;> decide) (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_
    refine ⟨_, _, V', h₄.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), e1,
      by rw [e2, hok], ?_⟩
    simp only [upd_self, upd_ne _ _ (show aU ≠ aX2 by decide), upd_ne _ _ (show aU ≠ aTmp by decide),
      upd_ne _ _ (show aX2 ≠ aTmp by decide), upd_ne _ _ (show aN ≠ aX2 by decide),
      upd_ne _ _ (show aN ≠ aTmp by decide), upd_ne _ _ (show wX3 ≠ wT by decide), f, sel_eq, eU, eY, eN]
    unfold stRes
    rw [← hY, ← hZ, ← hN, ← ev]
    split <;> simp


/-- The common start of a bit stage: the flag, and `u` shifted. -/
theorem stageB_pre (joint : Bool) {b : Nat}
    (h : KS g s0 A [aU, aX2, aN] AW [wX3] V [sB, sOkDE] s) (hV : V sB = b) (hb : 0 < b) (hb32 : b < 32) :
    WP isa (seqs [.block (VG.Impl.Rsa.X86.KeyRt.arrPtr nar .esi aU .edx ++
        VG.Impl.Rsa.X86.KeyRt.arrPtr nar .ebp (if joint then aX2 else aU) .edx ++
        ([.mov .eax (.mem (at_ .esi 0)), .alu .or .eax (.mem (at_ .ebp 0))] : List Instr)),
      lowTest, .block flagZero, downBitsH aU, VG.Impl.Rsa.X86.KeyRt.sel nar aU aU aTmp sStg]) s fun t =>
      ∃ A' V', KS g s0 A' [aU, aTmp, aU, aX2, aN] AW [wX3] V' [sBc, sStg, sB, sOkDE] t ∧
        V' sStg = (if stP joint (A aU, A aX2, AW wX3) b then 1 else 0) ∧ V' sB = b ∧
        V' sOkDE = V sOkDE ∧
        A' aU = (if stP joint (A aU, A aX2, AW wX3) b then A aU / 2 ^ b else A aU) ∧
        A' aX2 = A aX2 ∧ A' aN = A aN := by
  simp only [seqs]
  refine WP.seq (WP.mono (h.lowOr_ok (a := aU) (b := if joint then aX2 else aU) (by simp)
    (by cases joint <;> simp)) fun t₁ ⟨h₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (lowTest_ok h₁.ws (b := b) (by rw [h₁.sl _ (by simp), hV]) hb hb32)
    fun t₂ ⟨K₂, m₂, e₂⟩ => ?_)
  have h₂ := h₁.of_rest K₂ (by decide) m₂
  refine WP.seq (WP.mono h₂.flagZero fun t₃ ⟨h₃, _⟩ => ?_)
  have fl : (if t₂.gpr .ecx = 0 then 1 else 0) = (if stP joint (A aU, A aX2, AW wX3) b then 1 else 0) := by
    refine flag_eq ?_
    rw [← toNat_eq_zero_iff, e₂, e₁, or_low (by omega)]
    cases joint <;> simp [stP]
  rw [fl] at h₃
  refine WP.seq (WP.mono (h₃.downBits_ok (j := aU) (b := b) (by simp) (by decide) (by decide) (by simp)
    (by rw [upd_ne _ _ (by decide)]; exact hV) hb (by omega)) fun t₄ h₄ => ?_)
  refine WP.mono (h₄.sel_w (o := aU) (a := aU) (b := aTmp) (sl := sStg) (by decide) (by simp) (by simp)
    (by simp) (by rw [upd_ne _ _ (by decide), upd_self]; split <;> decide) (.inr (by decide)) (by decide))
    fun t₅ ⟨h₅, _⟩ => ?_
  refine ⟨_, _, h₅, by rw [upd_ne _ _ (by decide), upd_self],
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hV,
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)], ?_,
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)], by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]⟩
  rw [upd_self, upd_ne _ _ (show sStg ≠ sBc by decide), upd_self, sel_eq, upd_self, upd_ne _ _ (by decide)]

/-- A bit stage of `b` bits, `0 < b < 32`. -/
theorem stageB_ok (joint : Bool) {ok n b : Nat} {v : Nat × Nat × Nat} (h : TwS g s0 ok n v sB b s)
    (hb : 0 < b) (hb32 : b < 32) :
    WP isa (stageBH joint) s (TwS g s0 ok n (stRes (2 ^ (32 * g.W)) joint v b) sB b) := by
  obtain ⟨A, AW, V, h, hd, hok, hU, hY, hZ, hN⟩ := h
  have ev : (A aU, A aX2, AW wX3) = v := by rw [hU, hY, hZ]
  unfold stageBH
  rw [seqs_append_iff]
  refine WP.mono (stageB_pre joint h hd hb hb32) fun t ⟨A', V', h', f, e1, e2, eU, eY, eN⟩ => ?_
  rw [ev] at f eU
  cases joint
  · refine WP.block_nil ⟨A', AW, V', h'.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), e1, by rw [e2, hok], ?_⟩
    unfold stRes
    rw [eU, eY, eN, hY, hN, hZ]
    split <;> simp [hU]
  · simp only [ite_true, seqs]
    refine WP.seq (WP.mono (h'.downBits_ok (j := aX2) (b := b) (by simp) (by decide) (by decide) (by simp)
      e1 hb (by omega)) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (h₁.sel_w (o := aX2) (a := aX2) (b := aTmp) (sl := sStg) (by decide) (by simp)
      (by simp) (by simp) (by rw [upd_ne _ _ (by decide), f]; split <;> decide) (.inr (by decide)) (by decide))
      fun t₂ ⟨h₂, _⟩ => ?_)
    refine WP.seq (WP.mono (h₂.upBits_ok (b := b) (by simp) (by decide) (by simp)
      (by rw [upd_ne _ _ (by decide)]; exact e1) hb (by omega)) fun t₃ h₃ => ?_)
    refine WP.mono (h₃.sel_W (o := wX3) (a := wX3) (b := wT) (sl := sStg) (by decide) (by simp)
      (by simp) (by simp) (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), f]; split <;> decide)
      (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_
    refine ⟨_, _, _, h₄.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩),
      by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact e1,
      by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), e2, hok], ?_⟩
    simp only [upd_self, upd_ne _ _ (show aU ≠ aX2 by decide), upd_ne _ _ (show aU ≠ aTmp by decide),
      upd_ne _ _ (show aX2 ≠ aTmp by decide), upd_ne _ _ (show aN ≠ aX2 by decide),
      upd_ne _ _ (show aN ≠ aTmp by decide), upd_ne _ _ (show wX3 ≠ wT by decide),
      upd_ne _ _ (show sStg ≠ sBc by decide), f, sel_eq, eU, eY, eN]
    unfold stRes
    rw [← hY, ← hZ, ← hN, ← ev]
    split <;> simp

end

/-! ## The stages' loops -/

section
variable {g : Geo} {s0 t u : State} {ok n vd : Nat} {v : Nat × Nat × Nat} {d : Nat}

theorem TwS.of_rest (h : TwS g s0 ok n v d vd t) (r : Keeps opRegs t u) (m : u.mem = t.mem) :
    TwS g s0 ok n v d vd u := by
  obtain ⟨A, AW, V, h, rest⟩ := h
  exact ⟨A, AW, V, h.of_rest r (fun x hx => hx) m, rest⟩

theorem TwS.ws (h : TwS g s0 ok n v d vd t) : Ws t g.B g.Z g.w VG.Impl.Rsa.X86.Recover.nArr := by
  obtain ⟨A, AW, V, h, _⟩ := h
  exact h.ws

theorem TwS.slotEq (h : TwS g s0 ok n v d vd t) : slot t.mem g.B d = vd := by
  obtain ⟨A, AW, V, h, hd, _⟩ := h
  rw [h.sl _ (by simp), hd]

theorem TwS.rt (h : TwS g s0 ok n v d vd t) :
    VG.Proof.Rsa.X86.KeyRt.RtWs nar t g.B g.Z (8 * g.n + 8) VG.Impl.Rsa.X86.Recover.nArr := by
  obtain ⟨A, AW, V, h, _⟩ := h
  exact h.rt

/-- A header word written: it becomes the state's loop size. -/
theorem TwS.reslot {d' x w' : Nat} (h : TwS g s0 ok n v d vd t) (k : Keep g.B w' [] [d'] t.mem u.mem)
    (hd' : SlotOk d') (hne : d' ≠ sOkDE) (e : slot u.mem g.B d' = x) (r : Keeps opRegs t u) :
    TwS g s0 ok n v d' x u := by
  obtain ⟨A, AW, V, h, _, hok, rest⟩ := h
  refine ⟨A, AW, upd V d' x, (h.slot1 k hd' r e).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun e he => ⟨?_, rfl⟩), upd_self .., by rw [upd_ne _ _ (Ne.symm hne), hok], rest⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
  rcases he with rfl | rfl <;> simp

/-- The loop's size forgotten. -/
theorem TwS.forget (h : TwS g s0 ok n v d vd t) : TwS g s0 ok n v sOkDE ok t := by
  obtain ⟨A, AW, V, h, _, hok, rest⟩ := h
  exact ⟨A, AW, V, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun e he => ⟨by simp at he ⊢; omega, rfl⟩),
    hok, hok, rest⟩

theorem pow_pred {j : Nat} (hj : 0 < j) : 2 ^ j = 2 * 2 ^ (j - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

/-- One phase, `stages joint`: the stages of `2^12, …, 1` bits (word stages where `c < w`), each
taken where `a + k ≤ T`, from `a0` to `T`. -/
theorem phase_ok (joint : Bool) {T a0 : Nat} (vals : Nat → Nat × Nat × Nat)
    (hval : ∀ a k, a ≤ T → stRes (2 ^ (32 * g.W)) joint (vals a) k = vals (if a + k ≤ T then a + k else a))
    (ha0 : a0 ≤ T) (hT : T - a0 < 2 ^ 13) (hTw : T < 32 * g.w)
    (h : TwS g s0 ok n (vals a0) sOkDE ok t) :
    WP isa (seqs (stages joint)) t (TwS g s0 ok n (vals T) sOkDE ok) := by
  have e : seqs (stages joint) = .seq (wordStagesL (2 ^ 7) (VG.Impl.Rsa.X86.KeyRt.bytesB nar .eax) (stageWH joint))
    (bitStagesL (2 ^ 4) (2 ^ 0) (stageBH joint)) := rfl
  rw [e]
  refine WP.seq (WP.mono (wordStagesL_ok (k := 7) (lim := 4 * g.w)
    (Fin := fun t => ∃ a, a ≤ T ∧ T - a < 32 ∧ TwS g s0 ok n (vals a) sOkDE ok t)
    (fun j t => ∃ a, a ≤ T ∧ T - a < 64 * 2 ^ j ∧ TwS g s0 ok n (vals a) sC4 (4 * 2 ^ j) t)
    (fun j t => ∃ a, a ≤ T ∧ T - a < 32 * 2 ^ j ∧ TwS g s0 ok n (vals a) sC4 (4 * 2 ^ j) t)
    (by decide) h.ws ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t₁ F => ?_)
  · intro u k e r
    exact ⟨a0, ha0, by omega, h.reslot k (by decide) (by decide) e (r.mono (by decide))⟩
  · rintro j u _ ⟨a, _, _, P⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u _ ⟨a, _, _, P⟩ is Q k
    exact VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc P.rt) P.rt.lenLe
      fun u' K m e => k u' (K.mono (by decide)) m (by rw [e, kw_nar])
  · rintro j u u' _ ⟨a, h1, h2, P⟩ r m
    exact ⟨a, h1, h2, P.of_rest r m⟩
  · rintro j u _ ⟨a, h1, h2, P⟩ lt
    refine WP.mono (stageW_ok joint P (Nat.two_pow_pos j) (by omega)) fun u' P' => ?_
    rw [hval a _ h1] at P'
    exact ⟨_, by split <;> omega, by split <;> omega, P'⟩
  · rintro j u _ ⟨a, h1, h2, P⟩ le
    exact ⟨a, h1, by omega, P⟩
  · rintro j u _ ⟨a, _, _, P⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u u' _ ⟨a, h1, h2, P⟩ k e r
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have p := pow_pred hj
      exact ⟨a, h1, by omega, P.reslot k (by decide) (by decide) (by rw [e]; omega) r⟩
    · subst hj
      exact ⟨a, h1, by simpa using h2, (P.reslot k (by decide) (by decide) e r).forget⟩
  obtain ⟨a₁, ha₁, hlt₁, P₁⟩ := F
  refine bitStagesL_ok (k := 4) (m := 0) (Fin := TwS g s0 ok n (vals T) sOkDE ok)
    (fun j t => ∃ a, a ≤ T ∧ T - a < 2 * 2 ^ j ∧ TwS g s0 ok n (vals a) sB (2 ^ j) t)
    (fun j t => ∃ a, a ≤ T ∧ T - a < 2 ^ j ∧ TwS g s0 ok n (vals a) sB (2 ^ j) t)
    (by decide) (by decide) P₁.ws ?_ ?_ ?_ ?_
  · intro u k e r
    exact ⟨a₁, ha₁, by simpa using hlt₁, P₁.reslot k (by decide) (by decide) e (r.mono (by decide))⟩
  · rintro j u _ hj ⟨a, h1, h2, P⟩
    have p16 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hj
    refine WP.mono (stageB_ok joint P (Nat.two_pow_pos j) (by simp at p16; omega)) fun u' P' => ?_
    rw [hval a _ h1] at P'
    exact ⟨_, by split <;> omega, by split <;> omega, P'⟩
  · rintro j u _ _ ⟨a, _, _, P⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u u' _ _ ⟨a, h1, h2, P⟩ k e r
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have p := pow_pred hj
      exact ⟨a, h1, by omega, P.reslot k (by decide) (by decide) (by rw [e]; omega) r⟩
    · subst hj
      have : a = T := by simp at h2; omega
      subst this
      exact (P.reslot k (by decide) (by decide) e r).forget

end

/-! ## The halvings -/

section
variable {g : Geo} {s0 : State}
open VG.Proof.Bignum.ShiftStages

/-- `twosInit`: `u = n - 1`, and `x₃ = X`. -/
theorem twosInit_ok {u : State} {A AW V : Nat → Nat} {n x X : Nat}
    (h : KS g s0 A [aZ0, aX2, aN] AW [wX] V [sOkDE] u)
    (z : A aZ0 = 0) (hn : A aN = n) (hx : A aX2 = x) (hX : AW wX = X)
    (three : 3 ≤ n) :
    WP isa twosInit u (TwS g s0 (V sOkDE) n (n - 1, x, X) sOkDE (V sOkDE)) := by
  unfold twosInit
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aOneN) (a := aZ0) (by decide) (by simp) (by decide) (by decide))
    fun t₁ ⟨h₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h₁.setOne_w (j := aOneN) (by simp) (by decide)) fun t₂ ⟨h₂, _⟩ => ?_)
  refine WP.seq (WP.mono (h₂.sub3_w (o := aU) (a := aN) (b := aOneN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun t₃ ⟨Y, h₃, _, eY, b1⟩ => ?_)
  refine WP.mono (h₃.copy_W (o := wX3) (a := wX) (by decide) (by simp) (by decide) (by decide))
    fun t₄ ⟨h₄, _⟩ => ?_
  have lt : Y < 2 ^ (32 * g.w) := by
    have e := h₃.arrs aU (by simp)
    rw [upd_self] at e
    rw [← e]; exact val32_lt _ _ _ _
  simp only [upd_self, upd_ne _ _ (show aN ≠ aOneN by decide), hn, z, Nat.zero_div, Nat.mul_zero,
    Nat.add_zero] at eY
  have eY' : Y = n - 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e | e <;> rw [e] at eY <;> omega
  refine ⟨_, _, V, h₄.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), rfl, rfl, ?_⟩
  simp only [upd_self, upd_ne _ _ (show aX2 ≠ aU by decide), upd_ne _ _ (show aX2 ≠ aOneN by decide),
    upd_ne _ _ (show aN ≠ aU by decide), upd_ne _ _ (show aN ≠ aOneN by decide), eY', hx, hn, hX, and_self]

/-- The halvings: `u = (n - 1) / 2^tz(n - 1)`, and `x₂` and `x₃` shifted by `t = tz (gcd (n - 1) x)`. -/
theorem twos_ok {u : State} {A AW V : Nat → Nat} {n x X : Nat}
    (h : KS g s0 A [aZ0, aX2, aN] AW [wX] V [sOkDE] u)
    (z : A aZ0 = 0) (hn : A aN = n) (hx : A aX2 = x) (hX : AW wX = X)
    (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (t13 : VG.Proof.Bignum.ShiftStages.tz (n - 1) < 2 ^ 13) :
    WP isa twos u fun v => ∃ A' AW' V',
      KS g s0 A' [aU, aX2, aN] AW' [wX3] V' [sOkDE] v ∧
      A' aU = (n - 1) / 2 ^ VG.Proof.Bignum.ShiftStages.tz (n - 1) ∧
      A' aX2 = x / 2 ^ VG.Proof.Bignum.ShiftStages.tz (Nat.gcd (n - 1) x) ∧
      AW' wX3 = X * 2 ^ VG.Proof.Bignum.ShiftStages.tz (Nat.gcd (n - 1) x) % 2 ^ (32 * g.W) ∧
      A' aN = n ∧ V' sOkDE = V sOkDE := by
  have XM : X < 2 ^ (32 * g.W) := by rw [← hX, ← h.arrsW wX (by simp)]; exact val32_lt _ _ _ _
  have N0 : n - 1 ≠ 0 := by omega
  have g0 : Nat.gcd (n - 1) x ≠ 0 := Nat.gcd_ne_zero_left N0
  have tle : tz (Nat.gcd (n - 1) x) ≤ tz (n - 1) := (dvd_iff N0 _).mp
    (Nat.dvd_trans ((dvd_iff g0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left (n - 1) x))
  have tw : tz (n - 1) < 32 * g.w := tz_lt (by omega) (by omega)
  unfold twos
  rw [seqs_append_iff, seqs_append_iff]
  refine WP.mono (twosInit_ok h z hn hx hX three) fun t₁ P₁ => ?_
  have e₁ : ((n - 1, x, X) : Nat × Nat × Nat) =
      (fun a => ((n - 1) / 2 ^ a, x / 2 ^ a, X * 2 ^ a % 2 ^ (32 * g.W))) 0 := by
    simp [Nat.mod_eq_of_lt XM]
  rw [e₁] at P₁
  refine WP.mono (phase_ok true (T := tz (Nat.gcd (n - 1) x)) (a0 := 0) (fun a => ((n - 1) / 2 ^ a, x / 2 ^ a, X * 2 ^ a % 2 ^ (32 * g.W))) ?_ (Nat.zero_le _) (by omega) (by omega) P₁) fun t₂ P₂ => ?_
  · intro a k ha
    have hp := stage_pair (x := x) N0 ha k
    by_cases hk : a + k ≤ tz (Nat.gcd (n - 1) x)
    · have hs : stP true ((n - 1) / 2 ^ a, x / 2 ^ a, X * 2 ^ a % 2 ^ (32 * g.W)) k := by
        simpa [stP] using hp.mpr hk
      simp only [stRes, hs, hk, ↓reduceIte, div_pow_add, mul_pow_add_mod]
    · have hs : ¬ stP true ((n - 1) / 2 ^ a, x / 2 ^ a, X * 2 ^ a % 2 ^ (32 * g.W)) k := by
        simpa [stP] using mt hp.mp hk
      simp only [stRes, hs, hk, ↓reduceIte]
  refine WP.mono (phase_ok false (T := tz (n - 1)) (a0 := tz (Nat.gcd (n - 1) x)) (fun a => ((n - 1) / 2 ^ a, x / 2 ^ tz (Nat.gcd (n - 1) x),
    X * 2 ^ tz (Nat.gcd (n - 1) x) % 2 ^ (32 * g.W))) ?_ tle (by omega) tw P₂) fun v P => ?_
  · intro a k ha
    have hp := stage_tz N0 ha k
    by_cases hk : a + k ≤ tz (n - 1)
    · have hs : stP false ((n - 1) / 2 ^ a, x / 2 ^ tz (Nat.gcd (n - 1) x),
          X * 2 ^ tz (Nat.gcd (n - 1) x) % 2 ^ (32 * g.W)) k := by
        simpa [stP] using hp.mpr hk
      simp only [stRes, hs, hk, ↓reduceIte, div_pow_add, Bool.false_eq_true]
    · have hs : ¬ stP false ((n - 1) / 2 ^ a, x / 2 ^ tz (Nat.gcd (n - 1) x),
          X * 2 ^ tz (Nat.gcd (n - 1) x) % 2 ^ (32 * g.W)) k := by
        simpa [stP] using mt hp.mp hk
      simp only [stRes, hs, hk, ↓reduceIte]
  obtain ⟨A', AW', V', hK, _, hok, eU, eY, eZ, eN⟩ := P
  exact ⟨A', AW', V', hK.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), eU, eY, eZ, eN, hok⟩

end
end VG.Proof.Rsa.X86.Recover
