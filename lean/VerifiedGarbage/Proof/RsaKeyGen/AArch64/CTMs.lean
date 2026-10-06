import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTR2c
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase

/-!
# A candidate on AArch64: constant time of `montSetup`

`-c⁻¹` (its block split after the load of `c`'s base, which the taint
analysis cannot see is public), the number 1 (`setWord`), `R² mod c`
(`r2c_ct`), `R mod c`, `c − R mod c` and the number of uniform witnesses,
for runs that agree on the working space (`montSetup_ct`). Between the
pieces each run keeps `Ws`, `c` (with its top bit set), `-c⁻¹` and the
number 1 (`MSb`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aAcc aTmp aR2 aY aOne sCnt)

/-- The working space as public data. -/
abbrev WsP := VG.Proof.Bignum.AArch64.Ws

/-! ## Sequences and blocks -/

theorem ct_app' {α : Type} {Φ Ψ : α → State → Prop} {Q : State → State → Prop} {a b : List (Prog isa)}
    (ha : a ≠ []) (hb : b ≠ []) (hA : RelCT isa (Two Φ) (seqs a) (Two Ψ)) (hB : RelCT isa (Two Ψ) (seqs b) Q) :
    RelCT isa (Two Φ) (seqs (a ++ b)) Q :=
  RelCT.seqs_append ha hb (RelCT.seq hA hB)

/-- A block split after `l₁`, which leaves the registers `rs₂` with values of
the public data. -/
theorem blk_pin {α : Type} {Φ Ψ : α → State → Prop} (l₁ l₂ : List Instr) (rs₁ rs₂ : List Reg)
    (f : α → Reg → BitVec 64) (hpin : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    (hp : ∀ a s, Φ a s → WP isa (.block l₁) s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) (.block l₂) hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (l₁ ++ l₂)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (l₁ ++ l₂)) (Two Ψ) :=
  RelCT.block_append (pin_ct rs₁ rs₂ f hpin ht₁ hp ht₂ fun a s h => WP.seq_iff.mpr (WP.block_append_iff.mp (hw a s h)))

theorem pins_ws' {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) : Pins Φ [.x0] := pins_ws B Z w hws

/-- `setWord o` from `w` in `x12` and the word's index in `x13`. -/
theorem setWord_ct {α : Type} {Φ : α → State → Prop} {o : Nat} (ho : o < 8) (B : α → Addr) (Z w i : α → Nat)
    (hΦ : ∀ a s, Φ a s → (∃ mi, Good s (B a) (Z a) (w a) mi ∧ slot (w a) 8 ≤ Z a) ∧
      s.gpr .x12 = BitVec.ofNat 64 (w a) ∧ s.gpr .x13 = BitVec.ofNat 64 (i a))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr o), movi .x7 0]) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht' : (taint.check (Taint.ofRegs [.x8, .x12, .x13, .x7]) (.seq zeroAcc
      (.block [.lsl .x .x16 .x13 3, .add .x .x16 .x8 .x16, st .x9 .x16])) hc').isSome = true) :
    RelCT isa (Two Φ) (setWord o) fun _ _ => True := by
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun a s => s.gpr .x8 = off (B a) (slot (w a) o) ∧
      s.gpr .x12 = BitVec.ofNat 64 (w a) ∧ s.gpr .x13 = BitVec.ofNat 64 (i a) ∧ s.gpr .x7 = 0) [.x0]
    (pins_of _ (fun a _ => B a) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; obtain ⟨⟨_, hg, _⟩, _⟩ := hΦ a s h; exact hg.x0) ht ?_)
    (two_taint [.x8, .x12, .x13, .x7] (pins_of _ (fun a r => match r with
        | .x8 => off (B a) (slot (w a) o) | .x12 => BitVec.ofNat 64 (w a) | .x13 => BitVec.ofNat 64 (i a)
        | _ => 0) fun _ _ ⟨h8, h12, h13, h7⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h8
      · exact h12
      · exact h13
      · exact h7) ht')
  intro a s h
  obtain ⟨⟨mi, hg, hZ⟩, h12, h13⟩ := hΦ a s h
  have sa : sArr o < 32 := by unfold sArr; omega
  refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off (B a) (slot (w a) o) ∧ t.gpr .x7 = 0)
    (by brun [hg.x0, hdr_enc sa, hg.scr.ld (show 8 * sArr o + 8 ≤ Z a by have := hdr_lt_slot (w a) 8 sa; omega),
      hg.hdr.harr o ho]) rfl rfl rfl) fun t ⟨⟨h8, h7⟩, k⟩ =>
    ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13, h7⟩

/-! ## What `montSetup` keeps -/

/-- Before `montSetup`: the working space and the candidate. -/
def MS0 (L : WsP) (s : State) : Prop :=
  Ws s L.B L.Z L.w ∧ 4 ≤ L.w ∧ L.w ≤ 64 ∧
    ∃ N, wv s.mem L.B (slot L.w aN) L.w = N ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * L.w) N

/-- With `-c⁻¹`. -/
def MSc (L : WsP) (s : State) : Prop :=
  Ws s L.B L.Z L.w ∧ 4 ≤ L.w ∧ L.w ≤ 64 ∧
    ∃ N, wv s.mem L.B (slot L.w aN) L.w = N ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * L.w) N ∧
      ((word s.mem L.B (slot L.w aN)).toNat * (word s.mem L.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

/-- After `-c⁻¹`'s block. -/
def MSa (L : WsP) (s : State) : Prop :=
  MSc L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x9 = 1 ∧ s.gpr .x13 = BitVec.ofNat 64 0

/-- With the number 1. -/
def MSb (L : WsP) (s : State) : Prop := MSc L s ∧ wv s.mem L.B (slot L.w aOne) L.w = 1

/-- `MSc` survives changes away from `c` and `-c⁻¹`. -/
theorem MSc.frm {L : WsP} {s t : State} (h : MSc L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot L.w aN + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv) : MSc L t := by
  obtain ⟨hw, h4, h64, N, hn, hsh, hinv⟩ := h
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have eN := hw.sl (show aN < 16 by decide)
  refine ⟨hw.congr' hf hm k hr, h4, h64, N, by rw [hf.wv_eq dN (by omega)]; exact hn, hsh, ?_⟩
  rw [hf.word_eq (d := slot L.w aN) (fun r hr => by have := dN r hr; omega) (by omega),
    hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hw.h256; omega)]
  exact hinv

/-- `MSb` survives changes away from `c`, `-c⁻¹` and the number 1. -/
theorem MSb.frm {L : WsP} {s t : State} (h : MSb L s) {rs : List (Nat × Nat)} (hf : Frm L.B rs s.mem t.mem)
    (hm : ∀ r ∈ rs, KMut r) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dN : ∀ r ∈ rs, slot L.w aN + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aN)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dO : ∀ r ∈ rs, slot L.w aOne + 8 * L.w ≤ r.1 ∨ r.1 + r.2 ≤ slot L.w aOne) : MSb L t := by
  have hnw := h.1.1.scr.nowrap
  have hZ := h.1.1.hZ
  have eO := h.1.1.sl (show aOne < 16 by decide)
  exact ⟨h.1.frm hf hm k hr dN dI, by rw [hf.wv_eq dO (by omega)]; exact h.2⟩

/-- Disjointness from each of a list of literal ranges of the working space. -/
macro "msb_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, r2Ranges, slot,
    hdrBytes, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, sFn, sMinv]
  and_intros <;> omega))

/-- Ranges of literal arrays and header slots are `KMut`. -/
macro "msb_mut" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, r2Ranges]
  and_intros <;> first | exact KMut.ofSlot _ _ _ | exact KMut.hdr (by decide)))

/-! ## The pieces' correctness -/

theorem msH_ok {L : WsP} {s : State} (h : MS0 L s) :
    WP isa (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0])) s (MSa L) := by
  obtain ⟨hw, h4, h64, N, hn, hsh⟩ := h
  have hnw := hw.scr.nowrap
  have hodd := hsh.1
  have hw1 := hw.w1
  have hodd0 : (word s.mem L.B (slot L.w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem L.B (slot L.w aN) 1 (L.w - 1)
    rw [show 1 + (L.w - 1) = L.w by omega, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega
  refine WP.mono (msHead_ok hw hodd0) fun t ⟨⟨hinv, hm, h12, h9, h13⟩, k⟩ => ?_
  have o₁ : Outside L.B (8 * sMinv) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega)
  have f₁ : Frm L.B [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside o₁ (List.mem_singleton_self _)
  have hw₁ : word t.mem L.B (slot L.w aN) = word s.mem L.B (slot L.w aN) :=
    o₁.word (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)
  refine ⟨⟨hw.congr' f₁ (by msb_mut) k (by decide), h4, h64, N, ?_, hsh, by rw [hw₁]; exact hinv⟩, h12, h9,
    h13⟩
  rw [o₁.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)]; exact hn

theorem msOne_ok {L : WsP} {s : State} (h : MSa L s) : WP isa (setWord aOne) s (MSb L) := by
  obtain ⟨hc, h12, h9, h13⟩ := h
  have hw := hc.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  obtain ⟨g, hZ8⟩ := hw.good
  refine WP.mono (setWord_ok g.scr g.x0 g.hdr hZ8 h12 (by omega) (o := aOne) (by decide) (i := 0)
    (by omega) h13) fun t ⟨hv, o, k⟩ => ?_
  rw [h9] at hv
  have f : Frm L.B [(slot L.w aOne, 8 * (L.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  exact ⟨hc.frm f (by msb_mut) k (by decide) (by msb_disj) (by msb_disj), hv⟩

theorem msb_r2pre {L : WsP} {s : State} (h : MSb L s) : Up R2Pre L s := by
  obtain ⟨⟨hw, h4, h64, N, hn, hsh, hinv⟩, -⟩ := h
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  have htop : 2 ^ (64 * L.w - 1) ≤ N := by
    have : 2 ^ (64 * L.w - 1) = 2 ^ (64 * L.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    omega
  have hlo' : 2 ^ (64 * (L.w - 1)) ≤ N := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) htop
  exact ⟨word s.mem L.B (8 * sMinv), N, ⟨hw.good, show 2 ≤ L.w by omega, show L.w < 2 ^ 30 by omega, hn, hinv,
    hodd, hlo'⟩, htop⟩

theorem msR2_ok (M : Mont) {L : WsP} {s : State} (h : MSb L s) : WP isa (seqs (r2Steps M.mm)) s (MSb L) := by
  obtain ⟨mi, N, ⟨hg, hw2, hw', hn, hinv, hodd, hlo⟩, -⟩ := msb_r2pre h
  have hZ := h.1.1.hZ
  refine WP.mono (r2_ok M hg.1 hg.2 hw2 hw' hn hinv hodd hlo) fun t ⟨_, _, _, fr, k⟩ =>
    h.frm fr (by msb_mut) k (by decide) (by msb_disj) (by msb_disj) (by msb_disj)

theorem msY_ok (M : Mont) {L : WsP} {s : State} (h : MSb L s) : WP isa (M.mm aY aR2 aOne) s (MSb L) := by
  obtain ⟨⟨hw, h4, h64, N, hn, hsh, hinv⟩, hone⟩ := h
  obtain ⟨g, hZ8⟩ := hw.good
  have hN1 : 1 < N := by have := hsh.2.1; have := Nat.two_pow_pos (64 * L.w - 2); omega
  refine WP.mono (M.mm_ok g hZ8 hw.w1 (by have := hw.w2; omega) (o := aY) (a := aR2) (b := aOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv (by rw [hone, hn]; exact hN1))
    fun t ⟨_, _, _, ha, k⟩ => ?_
  exact MSb.frm (s := s) ⟨⟨hw, h4, h64, N, hn, hsh, hinv⟩, hone⟩ (Frm.of_arrays ha (rs := [(slot L.w aAcc,
    8 * (L.w + 2)), (slot L.w aTmp, 8 * (L.w + 2)), (slot L.w aY, 8 * (L.w + 2))]) (by simp)) (by msb_mut) k
    (by decide) (by msb_disj) (by msb_disj) (by msb_disj)

theorem msR1_ok {L : WsP} {s : State} (h : MSb L s) : WP isa (copyA aR1 aY) s (MSb L) := by
  have hw := h.1.1
  have hnw := hw.scr.nowrap
  have hZ := hw.hZ
  refine WP.mono (copyA_ok hw (o := aR1) (a := aY) (by decide) (by decide) (by decide)) fun t ⟨_, o, _, _, k⟩ =>
    h.frm (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide) (by msb_disj) (by msb_disj)
      (by msb_disj)

theorem msRm_ok {L : WsP} {s : State} (h : MSb L s) :
    WP isa (seqs (subA aRm1 aN aR1)) s fun t => Ws t L.B L.Z L.w := by
  have hw := h.1.1
  exact WP.mono (subA_ok hw (o := aRm1) (a := aN) (b := aR1) (by decide) (by decide) (by decide) (.inr (by decide))
    (by decide)) fun t ⟨_, o, _, _, _, k⟩ =>
    hw.congr' (Frm.of_outside o (List.mem_singleton_self _)) (by msb_mut) k (by decide)

/-! ## Constant time -/

theorem msH_ct : RelCT isa (Two MS0) (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) (Two MSa) := by
  have e : ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0] :
      List Instr) = [ldh .x8 (sArr aN)] ++ ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
        movi .x13 0]) := rfl
  rw [e]
  refine blk_pin _ _ [.x0] [.x0, .x8] (fun L r => match r with | .x0 => L.B | _ => off L.B (slot L.w aN))
    (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h.1) (by taint_decide) (fun L s h => ?_) (by taint_decide)
    fun L s h => by rw [← e]; exact msH_ok h
  have hw := h.1
  have hnw := hw.scr.nowrap
  have sN := hw.sl (show aN < 16 by decide)
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = off L.B (slot L.w aN)) (by
    brun [hw.x0, hdr_enc (show sArr aN < 32 by decide), hw.scr.ld (d := 8 * sArr aN) (by simp only [sArr, aN]; omega),
      hw.harr aN (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨h8, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h8

theorem msOne_ct : RelCT isa (Two MSa) (setWord aOne) (Two MSb) :=
  two_post (setWord_ct (by decide) (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ => 0) (fun _ _ h => ⟨⟨_, h.1.1.good⟩, h.2.1, h.2.2.2⟩)
    (by taint_decide) (by taint_decide)) fun _ _ h => msOne_ok h

theorem msR2_ct (M : Mont) : RelCT isa (Two MSb) (seqs (r2Steps M.mm)) (Two MSb) :=
  two_post (two_map id (fun _ _ h => msb_r2pre h) (r2c_ct M)) fun _ _ h => msR2_ok M h

theorem msY_ct (M : Mont) : RelCT isa (Two MSb) (M.mm aY aR2 aOne) (Two MSb) :=
  two_post (two_map id (fun _ _ h => ⟨_, h.1.1.good⟩) (M.ct (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
    fun _ _ h => msY_ok M h

theorem msR1_ct : RelCT isa (Two MSb) (copyA aR1 aY) (Two MSb) := by
  have e : copyA aR1 aY = .seq (.block (ws ++ (base aY .x16 ++ base aR1 .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) (fun _ _ h => h.1.1) (by taint_decide) fun _ _ h => by
    rw [← e]; exact msR1_ok h

theorem subA_eq' (o a b : Nat) : seqs (subA o a b) = .seq (.block (ws ++ ([movi .x7 0, .subImm .x .x15 .x7 1,
    mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17 ++ base o .x8))) (countLoop .x14 subMBody) :=
  rfl

theorem msTail_ct : RelCT isa (Two MSb) (seqs (subA aRm1 aN aR1 ++
    [.block ([ldh .x12 sW, movi .x5 27] ++ checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++
      checksIf 22 4 ++ checksIf 59 3 ++ [sth .x5 kChecks])])) fun _ _ => True := by
  exact RelCT.seqs_append (by simp [subA]) (by simp) (RelCT.seq (R := Two fun (L : WsP) t => Ws t L.B L.Z L.w)
    (show RelCT isa _ (seqs (subA aRm1 aN aR1)) _ by
      rw [subA_eq']
      exact ws_ct (Φ := MSb) (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w)
        (Ψ := fun L t => Ws t L.B L.Z L.w) (fun _ _ h => h.1.1) (by taint_decide)
        fun _ _ h => by rw [← subA_eq']; exact msRm_ok h)
    (two_taint [.x0] (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w) fun _ _ h => h) (by taint_decide)))

theorem montSetup_eq' (mul : Nat → Nat → Nat → Prog isa) : montSetup mul =
    [.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
      setWord aOne] ++ (r2Steps mul ++ ([mul aY aR2 aOne, copyA aR1 aY] ++ (subA aRm1 aN aR1 ++
      [.block ([ldh .x12 sW, movi .x5 27] ++ checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++
        checksIf 22 4 ++ checksIf 59 3 ++ [sth .x5 kChecks])]))) := by
  simp only [montSetup, List.append_assoc, List.cons_append, List.nil_append]

/-- `montSetup` leaks the same in runs that agree on the working space. -/
theorem montSetup_ct (M : Mont) : RelCT isa (Two MS0) (seqs (montSetup M.mm)) fun _ _ => True := by
  rw [montSetup_eq']
  exact ct_app' (by simp) (by simp [r2Steps]) (RelCT.seq msH_ct msOne_ct)
    (ct_app' (by simp [r2Steps]) (by simp) (msR2_ct M)
      (ct_app' (by simp) (by simp [subA]) (RelCT.seq (msY_ct M) msR1_ct) msTail_ct))

end VG.Proof.RsaKeyGen.AArch64
