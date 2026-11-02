module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Call
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # After an attempt (x86)

`classify` consumes the candidate's octets (`advance_ok`) and, by its
status, finishes the search with p, counts a rejection and asks the loop
for another candidate, or, on a shortage, requests more of the tape or
gives up once it holds the entropy cap (`classify_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch Aligned.cons)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The octets the candidate at `used` consumes. -/
abbrev PPub.cu (p : PPub) (used : Nat) : Nat := candUsed p.bits p.gen p.rand used

/-- Whether the loop goes on after an iteration from `used` with `n` attempts: a candidate was drawn
and rejected. -/
def PPub.cont (p : PPub) (used n : Nat) : Prop :=
  n ≠ 0 ∧ p.len ≤ p.randLen - used ∧ ∃ rest, candAt p.bits p.gen p.rand used = some (none, rest)

/-- A loop state after a rejection: the status word says so. -/
def Rej (p : PPub) (o : State) (used n : Nat) (s : State) : Prop :=
  Live p o used n s ∧ s.mem.readW (addr p.S statusOff) 32 = 4

/-- After an iteration from a loop state: the search from there finished, or a rejection counted and
the loop state after it. -/
def Next (p : PPub) (o : State) (used n : Nat) (s : State) : Prop :=
  (Done p o (p.tail used n) s ∧ ¬ p.cont used n) ∨ (p.cont used n ∧ Rej p o (used + p.cu used) (n - 1) s)

/-- A run's state with a loop state's words. -/
theorem St.live {o s : State} {used n : Nat}
    (h : St o liveDs (liveF (ofState o) (o.gpr .esi) used n) s) (hu : used ≤ (ofState o).randLen)
    (hn : n ≤ (ofState o).attempts) : Live (ofState o) o used n s :=
  ⟨⟨h.abi, rfl⟩, hu, hn, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words⟩

/-- A word of the state beside the others. -/
theorem St.withWord {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat}
    {v : BitVec 32} (hv : s.mem.readW (addr (arg o 9) d) 32 = v) : St o (d :: ds) (upd f d v) s := by
  refine ⟨h.abi, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, fun e he => ?_⟩
  rcases List.mem_cons.mp he with rfl | he
  · simp only [upd, ite_true]; exact hv
  · by_cases hde : e = d
    · subst hde; simp only [upd, ite_true]; exact hv
    · simp only [upd, hde, ite_false]; exact h.words e he

theorem advance_ok {o u : State} {e : BitVec 32} {used n c : Nat}
    (S : St o (candOff :: liveDs) (upd (liveF (ofState o) e used n) candOff (BitVec.ofNat 32 c)) u)
    (hr : used + c ≤ (ofState o).randLen) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o liveDs (liveF (ofState o) e (used + c) n) t → t.gpr .edx = u.gpr .eax →
      Frame [sR o] u.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (advance ++ rest)) u Q := by
  have hA : Aligned (candOff :: liveDs) := by decide
  unfold advance
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ U₁ => ?_
  have S₁ := S.reg U₁ (Or.inr (Or.inr rfl))
  refine S₁.ld (Or.inr (Or.inl rfl)) (d := candOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  refine S₂.ld (Or.inl rfl) (d := randOff) (by decide) (by decide) fun t₃ S₃ g₃ o₃ _ m₃ => ?_
  refine wp_add fun t₄ U₄ _ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA (d := randOff) (by decide) (by decide) fun t₅ S₅ G₅ _ _ F₅ => ?_
  have hA₅ := hA.cons (d := randOff) (by decide) (by decide)
  refine S₅.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_sub fun t₇ U₇ _ => ?_
  have S₇ := S₆.reg U₇ (Or.inl rfl)
  refine S₇.stw hA₅ (d := leftOff) (by decide) (by decide) fun t₈ S₈ G₈ _ _ F₈ => ?_
  have hA₈ := hA₅.cons (d := leftOff) (by decide) (by decide)
  refine S₈.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₉ S₉ g₉ o₉ _ m₉ => ?_
  refine wp_add fun t₁₀ U₁₀ _ => ?_
  have S₁₀ := S₉.reg U₁₀ (Or.inl rfl)
  refine S₁₀.stw hA₈ (d := usedOff) (by decide) (by decide) fun t₁₁ S₁₁ G₁₁ _ _ F₁₁ => k t₁₁ ?_ ?_ ?_
  · -- The values stored.
    have c₃ : t₃.gpr .ecx = BitVec.ofNat 32 c := by rw [o₃ .ecx (by decide), g₂]; rfl
    have c₆ : t₆.gpr .ecx = BitVec.ofNat 32 c := by
      rw [o₆ .ecx (by decide), G₅, U₄.other .ecx (by decide), c₃]
    have c₉ : t₉.gpr .ecx = BitVec.ofNat 32 c := by
      rw [o₉ .ecx (by decide), G₈, U₇.other .ecx (by decide), c₆]
    have v₄ : t₄.gpr .eax = (ofState o).rp + BitVec.ofNat 32 (used + c) := by
      rw [U₄.gpr, g₃, c₃, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have v₇ : t₇.gpr .eax = BitVec.ofNat 32 ((ofState o).randLen - (used + c)) := by
      rw [U₇.gpr, g₆, c₆, show upd (upd (liveF (ofState o) e used n) candOff (BitVec.ofNat 32 c)) randOff
        (t₄.gpr .eax) leftOff = BitVec.ofNat 32 ((ofState o).randLen - used) from rfl, sub_ofNat (by omega_arith),
        Nat.sub_add_eq]
    have v₁₀ : t₁₀.gpr .eax = BitVec.ofNat 32 (used + c) := by
      rw [U₁₀.gpr, g₉, c₉, show upd (upd (upd (liveF (ofState o) e used n) candOff (BitVec.ofNat 32 c)) randOff
        (t₄.gpr .eax)) leftOff (t₇.gpr .eax) usedOff = BitVec.ofNat 32 used from rfl, BitVec.ofNat_add_ofNat]
    rw [v₄, v₇, v₁₀] at S₁₁
    refine (S₁₁.sub fun d hd => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hd)))).congr ?_
    simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl) <;> simp [upd, liveF, randOff, leftOff, usedOff, candOff]
  · rw [G₁₁, U₁₀.other _ (by decide), o₉ _ (by decide), G₈, U₇.other _ (by decide), o₆ _ (by decide), G₅,
      U₄.other _ (by decide), o₃ _ (by decide), o₂ _ (by decide), U₁.gpr]
  · have e₄ : t₄.mem = u.mem := by rw [U₄.mem, m₃, m₂, U₁.mem]
    have e₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
    have e₁₀ : t₁₀.mem = t₈.mem := by rw [U₁₀.mem, m₉]
    rw [e₄] at F₅; rw [e₇] at F₈; rw [e₁₀] at F₁₁
    exact (F₅.trans F₈).trans F₁₁

/-- The high half of a 64-bit decrement. -/
theorem dec_hi {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 32) :
    BitVec.ofNat 32 (n / 2 ^ 32) - 0 - (BitVec.ofBool (decide ((BitVec.ofNat 32 n).toNat < (1 : BitVec 32).toNat))).setWidth 32 =
      BitVec.ofNat 32 ((n - 1) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [sub3_toNat]
  by_cases hn : n = 2 ^ 32
  · subst hn; decide
  · have hlt : n < 2 ^ 32 := by omega_arith
    rw [toNat_ofNat_lt hlt]
    simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl, show ¬ n < 1 by omega_arith,
      decide_false, Bool.toNat_false, Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (show n - 1 < 2 ^ 32 by omega_arith)]
    rfl

/-- A rejection: one fewer attempt (64 bits), the status 4. -/
theorem St.rejected {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hd0 : attemptsOff ∈ ds) (hd4 : attemptsOff + 4 ∈ ds) {n : Nat} (hlo : f attemptsOff = BitVec.ofNat 32 n)
    (hhi : f (attemptsOff + 4) = BitVec.ofNat 32 (n / 2 ^ 32)) (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 32) :
    WP isa (.block VG.Impl.Ffdh.X86.ParamSearch.rejected) s fun t =>
      St o (statusOff :: (attemptsOff + 4) :: attemptsOff :: ds)
        (upd (upd (upd f attemptsOff (BitVec.ofNat 32 (n - 1))) (attemptsOff + 4)
          (BitVec.ofNat 32 ((n - 1) / 2 ^ 32))) statusOff 4) t := by
  unfold VG.Impl.Ffdh.X86.ParamSearch.rejected
  refine h.ld (Or.inl rfl) hd0 (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_subi fun t₂ U₂ c₂ _ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine S₂.stw hA (d := attemptsOff) (by decide) (by decide) fun t₃ S₃ G₃ _ C₃ _ => ?_
  have hA₃ := hA.cons (d := attemptsOff) (by decide) (by decide)
  refine S₃.ld (Or.inl rfl) (List.mem_cons_of_mem _ hd4) (by decide) fun t₄ S₄ g₄ _ C₄ _ => ?_
  refine wp_sbbS (v := 0) rfl (C₄.trans (C₃.trans c₂)) fun t₅ U₅ _ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw hA₃ (d := attemptsOff + 4) (by decide) (by decide) fun t₆ S₆ _ _ _ _ => ?_
  have hA₆ := hA₃.cons (d := attemptsOff + 4) (by decide) (by decide)
  refine wp_movi fun t₇ U₇ => ?_
  have S₇ := S₆.reg U₇ (Or.inl rfl)
  refine S₇.stw hA₆ (d := statusOff) (by decide) (by decide) fun t₈ S₈ _ _ _ _ => WP.block_nil ?_
  have v₂ : t₂.gpr .eax = BitVec.ofNat 32 (n - 1) := by rw [U₂.gpr, g₁, hlo, ofNat_pred h1]
  have v₅ : t₅.gpr .eax = BitVec.ofNat 32 ((n - 1) / 2 ^ 32) := by
    rw [U₅.gpr, g₄, show upd f attemptsOff (t₂.gpr .eax) (attemptsOff + 4) = f (attemptsOff + 4) from rfl, hhi,
      g₁, hlo]
    exact dec_hi h1 h2
  rw [v₂, v₅, U₇.gpr] at S₈
  exact S₈

theorem cmp_status {s t : State} {k j : Nat} (hk : k ≤ 2) (hj : j ≤ 2) (he : s.gpr .edx = BitVec.ofNat 32 k)
    (z : t.zf = some (s.gpr .edx - BitVec.ofNat 32 j == 0)) : isa.eval .e t = some (decide (k = j)) := by
  show t.zf = _
  rw [z, he, sub_beq (by omega_arith) (by omega_arith)]

theorem classify_ok {p : PPub} {o s₀ u : State} {used n : Nat} (h : Live p o used n s₀)
    (S : St o liveDs (liveF p (o.gpr .esi) used n) u)
    (he : u.gpr .eax = BitVec.ofNat 32 (candidateStatus (candOf o used))) (ho : AttemptOut o used u.mem)
    (hcu : u.mem.readW (addr (arg o 9) candOff) 32 = BitVec.ofNat 32 (p.cu used)) (hn : n ≠ 0)
    (hr : p.len ≤ p.randLen - used) :
    WP isa classify u (Next p o used n) := by
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  have hnl := h.n_le
  have hat := attempts_le A
  have hlen : (ofState o).rand.length = (ofState o).randLen := rand_length
  have hcl : used + (ofState o).cu used ≤ (ofState o).randLen := by
    have h2 := candUsed_le (ofState o).bits (ofState o).gen (ofState o).rand used
    rw [hlen] at h2
    have := h.used_le
    show used + candUsed _ _ _ _ ≤ _
    omega_arith
  have hst := candidateStatus_le (candOf o used)
  unfold classify
  refine WP.seq (advance_ok (S.withWord hcu) hcl fun t S' hed Ft => wp_cmpi fun t' F _ z => WP.block_nil ?_)
  have S'' := S'.fupd F
  have Ft' : Frame [sR o] u.mem t'.mem := by rw [F.mem]; exact Ft
  have hedT : t.gpr .edx = BitVec.ofNat 32 (candidateStatus (candOf o used)) := hed.trans he
  have hed' : t'.gpr .edx = BitVec.ofNat 32 (candidateStatus (candOf o used)) := by rw [F.gpr, hedT]
  rcases hc : candOf o used with _ | ⟨_ | q, rest⟩
  · -- A shortage: nothing consumed.
    have h0 : (ofState o).cu used = 0 := by
      show candUsed _ _ _ _ = 0; unfold candUsed; rw [show candAt _ _ _ used = none from hc]
    rw [hc] at hedT hed'
    rw [h0, Nat.add_zero] at S''
    refine WP.ite false (by rw [cmp_status (candidateStatus_le _) (j := 1) (by decide) hedT z]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    refine WP.ite false (by rw [cmp_status (candidateStatus_le _) (j := 2) (by decide) hed' z₂]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    unfold shortage
    refine WP.seq (S₂.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₃ S₃ g₃ _ _ _ => ?_)
    refine S₃.ld (Or.inr (Or.inl rfl)) (d := capOff) (by decide) (by decide) fun t₄ S₄ g₄ o₄ _ _ => ?_
    refine wp_cmp fun t₅ F₅ c₅ _ => WP.block_nil ?_
    have L₅ := (S₄.fupd F₅).live h.used_le hnl
    have hcap := cap_lt A
    have hR := A.randLen
    have er : (ofState o).randLen = (arg o 6).toNat := rfl
    have ec : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl
    have hb : isa.eval .b t₅ = some (decide ((ofState o).randLen - used < (ofState o).cap)) := by
      show t₅.cf = _
      rw [c₅, o₄ .eax (by decide), g₃, g₄]
      simp only [liveF, leftOff, capOff, ↓reduceIte, Nat.reduceEqDiff]
      rw [toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]
    have tail := ptail_short (bits := (ofState o).bits) (gen := (ofState o).gen) (rand := (ofState o).rand)
      (used := used) hn hc
    rw [hlen] at tail
    have nc : ¬ (ofState o).cont used n := fun ⟨_, _, rest', h'⟩ => absurd (hc.symm.trans h') (by simp)
    by_cases hl : (ofState o).randLen - used < (ofState o).cap
    · refine WP.ite true (by rw [hb]; simp [hl]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine WP.mono (request_ok L₅) fun v hv => Or.inl ⟨?_, nc⟩
      show Done _ _ (ptail _ _ _ _ _) v
      rw [tail]
      split
      · rename_i hc'; exact absurd hc' (by unfold PPub.cap at hl; omega_arith)
      · exact hv
    · refine WP.ite false (by rw [hb]; simp [hl]) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine WP.mono (exhausted_ok L₅) fun v hv => Or.inl ⟨?_, nc⟩
      show Done _ _ (ptail _ _ _ _ _) v
      rw [tail]
      split
      · exact hv
      · rename_i hc'; exact absurd (by unfold PPub.cap at hl; omega_arith) hc'
  · -- A rejection.
    rw [hc] at hedT hed'
    refine WP.ite false (by rw [cmp_status (candidateStatus_le _) (j := 1) (by decide) hedT z]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    refine WP.ite true (by rw [cmp_status (candidateStatus_le _) (j := 2) (by decide) hed' z₂]; rfl) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine WP.mono (S₂.rejected hA (by decide) (by decide) (n := n) (by simp [liveF, attemptsOff])
      (by simp [liveF, attemptsOff]) (by omega_arith) (by omega_arith)) fun v Sv => Or.inr ⟨⟨hn, hr, rest, hc⟩, ?_, ?_⟩
    · refine ((Sv.sub fun d hd => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))).congr
        ?_).live (by omega_arith) (by omega_arith)
      simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl) <;> simp [upd, liveF, statusOff, attemptsOff]
    · show v.mem.readW (addr (arg o 9) statusOff) 32 = 4
      rw [Sv.words.get (List.mem_cons_self ..)]; simp [upd, statusOff]
  · -- Accepted.
    rw [hc] at hedT hed'
    refine WP.ite true (by rw [cmp_status (candidateStatus_le _) (j := 1) (by decide) hedT z]; rfl) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine WP.mono (S''.terminal hA 1) fun v ⟨Sv, Fv⟩ => Or.inl ⟨?_, fun ⟨_, _, rest', h'⟩ =>
      absurd (hc.symm.trans h') (by simp)⟩
    show Done _ _ (ptail _ _ _ _ _) v
    rw [ptail_accept hn hc]
    refine Sv.done (by decide) ?_ ?_ ⟨Nat.zero_le _, Nat.zero_le _, hcl⟩
    · simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        simp [upd, liveF, doneF, statusOff, requestOff, attemptsOff, ParameterSearchResult.remaining,
          ParameterSearchResult.requested, ParameterSearchResult.status, ParameterSearchResult.used]
    · have ho' := ho
      unfold AttemptOut at ho'
      rw [hc] at ho'
      exact (out_keep A (Ft'.trans Fv)).trans ho'

end VG.Proof.Ffdh.X86.PSearch
