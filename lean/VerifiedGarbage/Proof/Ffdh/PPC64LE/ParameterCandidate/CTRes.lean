module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTest
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.WriteP
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTTest
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.WriteP
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.TestsFn

/-!
# An FFDH parameter candidate on PPC64LE: the results in constant time

`finish` stores through `used`'s address, pinned once loaded from the
header; the results branch on a test's status, which its witnesses decide
(`statOf`); `writeP` copies p through `out`'s address and length, pinned
once loaded.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- Before `finish`: the working space, and `used`'s address in its header. -/
def FS (q : PP) (s : State) : Prop :=
  ∃ Z, Scr s q.B Z ∧ 40 ≤ Z ∧ s.gpr .r31 = q.B ∧ s.mem.readW (q.B + BitVec.ofNat 64 32) 64 = q.up

theorem pins_FS : Pins FS [.r31] := by
  rintro q s₁ s₂ ⟨_, _, _, h₁, -⟩ ⟨_, _, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- With `used`'s address loaded. -/
def F4 (q : PP) (s : State) : Prop := s.gpr .r31 = q.B ∧ s.gpr .r4 = q.up

theorem pins_F4 : Pins F4 [.r4, .r31] := by
  rintro q s₁ s₂ ⟨a31, a4⟩ ⟨b31, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a4, b4]
  · rw [a31, b31]

theorem St.fs {p : PP} {s : State} (h : St p s) : FS p s := by
  have := h.dims.n
  exact ⟨p.Z, h.scr, by simp only [PP.Z]; omega, h.r31, h.args.usedP'⟩

theorem finish_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) : RelCT isa (Two FS) (.block (finish r)) fun _ _ => True := by
  have hd : RelCT isa (Two FS) (.block [ldh .r4 hUsedP]) (Two F4) :=
    two_post (two_taint _ pins_FS (by taint_decide)) fun q s ⟨Z, hs, hZ, h31, hu⟩ =>
      WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = q.up) (by
          simp only [ldh, hUsedP]; prun [h31, hs.ld (d := 32) (n := 8) (by omega), hu]) (by decide))
        fun t ⟨t4, k⟩ => ⟨(k.gpr _ (by decide)).trans h31, t4⟩
  unfold finish
  rw [List.append_assoc]
  obtain rfl | rfl | rfl := hr
  all_goals exact RelCT.block_append (RelCT.seq hd (two_taint _ pins_F4 (by taint_decide)))

/-- A test's status: 0 without enough octets, 1 if it passed, 2 if not. -/
def statOf : Option (Bool × List Byte) → Nat
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem statOf_le (r : Option (Bool × List Byte)) : statOf r ≤ 2 := by
  rcases r with _ | ⟨_ | _, _⟩ <;> simp [statOf]

theorem MrEnd.stat {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {s : State}
    (h : MrEnd p mb N res s) : word s.mem p.B 160 = BitVec.ofNat 64 (statOf res) := by
  obtain ⟨_, hn, hs⟩ := h
  rcases res with _ | ⟨b, rest⟩
  · exact hn rfl
  · exact (hs b rest rfl).1

theorem MSt.fs {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N s) : FS p s := h.st.fs

theorem pins_ME : Pins ME [.r31] := by
  rintro a s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.st.r31, h₂.st.r31]; rfl

/-- With a test's status in `r3`. -/
def SL (a : MrD) (t : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N t) ∧ t.gpr .r3 = BitVec.ofNat 64 (statOf a.res)

theorem pins_SL : Pins SL [.r3, .r31] := by
  rintro a s₁ s₂ ⟨⟨_, _, M₁⟩, a3⟩ ⟨⟨_, _, M₂⟩, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [M₁.st.r31, M₂.st.r31]; rfl

theorem statLoad_ct : RelCT isa (Two ME) (.block [ldh .r3 hStat]) (Two SL) :=
  two_post (two_taint _ pins_ME (by taint_decide)) fun _ _ ⟨sv, toc, hE⟩ =>
    WP.mono (statLoad_ok hE.1) fun _ ⟨Mt, t3, _⟩ => ⟨⟨sv, toc, Mt⟩, t3.trans hE.stat⟩

theorem finSL_ct {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2) {Φ : MrD → State → Prop}
    (h : ∀ a s, Φ a s → ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N s) :
    RelCT isa (Two Φ) (.block (finish r)) fun _ _ => True :=
  two_map MrD.q (fun a s hs => let ⟨_, _, M⟩ := h a s hs; M.fs) (finish_ct hr)


/-- After a failed test of q. -/
theorem qResult_ct : RelCT isa (Two ME) qResult fun _ _ => True := by
  unfold qResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0)) (fun a s h => ?_)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  exact eval_zero_ofNat s .r3 (by have := statOf_le a.res; omega) h.2

/-- With a test's status less one in `r3`. -/
def SL1 (a : MrD) (t : State) : Prop :=
  (∃ sv toc, MSt (a.q.with sv toc) a.mb a.N t) ∧ t.gpr .r3 = BitVec.ofNat 64 (statOf a.res) - BitVec.ofNat 64 1

/-- In a modulus's working space. -/
def MS (a : MrD) (t : State) : Prop := ∃ sv toc, MSt (a.q.with sv toc) a.mb a.N t

theorem pins_MS {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) : Pins Φ [.r31] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨_, _, M₁⟩ := h a s₁ h₁
  obtain ⟨_, _, M₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [M₁.st.r31, M₂.st.r31]; rfl

theorem sub1_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → SL a s) :
    RelCT isa (Two Φ) (.block [.subi .r3 .r3 1]) (Two SL1) :=
  two_post (two_taint _ (pins_MS fun a s hs => (h a s hs).1) (by taint_decide)) fun a s hs => by
    obtain ⟨⟨sv, toc, M⟩, h3⟩ := h a s hs
    exact WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (statOf a.res) - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) (by prun [h3]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ =>
      ⟨⟨sv, toc, M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k (by decide) (k.gpr _ (by decide))
        (k.gpr _ (by decide)) (k.gpr _ (by decide))⟩, t3⟩

/-- With `out`, `out_len` and p's last octet's address loaded. -/
def W4 (a : MrD) (t : State) : Prop :=
  t.gpr .r4 = a.q.op ∧ t.gpr .r5 = BitVec.ofNat 64 a.q.L ∧ t.gpr .r6 = off a.q.B (256 + (a.q.L - 1))

theorem pins_W4 : Pins W4 [.r4, .r5, .r6] := by
  rintro a s₁ s₂ ⟨a4, a5, a6⟩ ⟨b4, b5, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a4, b4]
  · rw [a5, b5]
  · rw [a6, b6]

theorem writeP_ct {Φ : MrD → State → Prop} (h : ∀ a s, Φ a s → MS a s) :
    RelCT isa (Two Φ) writeP (Two fun (a : MrD) => FS a.q) := by
  refine two_post ?_ fun a s hs => ?_
  · unfold writeP
    refine RelCT.seq (two_post (two_taint _ (pins_MS h) (by taint_decide)) (Ψ := W4) fun a s hs => ?_)
      (two_taint _ pins_W4 (by taint_decide))
    obtain ⟨sv, toc, M⟩ := h a s hs
    have hdn := M.st.dims.n
    have hb1 := M.st.dims.b1
    have hLe : (a.q.with sv toc).L = ((a.q.with sv toc).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv toc).Z = 8 * (a.q.with sv toc).n := rfl
    exact WP.mono (writeHead_ok M.st.scr M.st.r31 (M.ph.r10.trans (by rw [slot_zero])) M.st.args.out'
      M.st.args.len' (by omega) (by omega)) fun t ⟨⟨t6, t4, t5, _⟩, _⟩ => ⟨t4, t5, t6⟩
  · obtain ⟨sv, toc, M⟩ := h a s hs
    have h := M.st
    have hdn := h.dims.n
    have hb1 := h.dims.b1
    have hnw := h.scr.nowrap
    have hLe : (a.q.with sv toc).L = ((a.q.with sv toc).bits + 7) / 8 := rfl
    have hZe : (a.q.with sv toc).Z = 8 * (a.q.with sv toc).n := rfl
    refine WP.mono (writeP_ok h.scr h.bufs.scrO h.r31 (M.ph.r10.trans (by rw [slot_zero])) h.args.out'
      h.args.len' (by omega) (by omega) h.bufs.sepO) fun t₁ ⟨⟨_, tout⟩, k₁⟩ => ?_
    have hws₁ : ∀ x, ofs (a.q.with sv toc).B x < (a.q.with sv toc).Z → t₁.mem x = s.mem x := fun x hx => tout x (Or.inr (by
      by_contra hc'
      have := h.bufs.sepO x (by omega)
      omega))
    have E₁ := h.toE.frame hws₁ k₁ (by decide)
    exact ⟨_, E₁.scr, by omega, E₁.r31, (word_of_ws hws₁ (d := 32) (by omega) hnw).trans h.args.usedP'⟩

/-- After p's test. -/
theorem pResult_ct : RelCT isa (Two ME) pResult fun _ _ => True := by
  unfold pResult
  refine RelCT.seq statLoad_ct (two_ite' (fun a => decide (statOf a.res = 0))
    (fun a s h => eval_zero_ofNat s .r3 (by have := statOf_le a.res; omega) h.2)
    (finSL_ct (.inl rfl) fun _ _ h => h.1.1) ?_)
  refine RelCT.seq (sub1_ct fun _ _ h => h.1) (two_ite' (fun a => decide (statOf a.res = 1)) (fun a s h => ?_)
    (RelCT.seq (writeP_ct fun _ _ h => h.1.1) (two_map MrD.q (fun _ _ h => h) (finish_ct (.inr (.inl rfl)))))
    (finSL_ct (.inr (.inr rfl)) fun _ _ h => h.1.1))
  rw [eval_zero, h.2]
  exact congrArg some (stat_one (by have := statOf_le a.res; omega))

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
