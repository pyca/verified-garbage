module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTMain
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTMain
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Correct

/-!
# An FFDH parameter candidate on PPC64LE: constant time

`code_ct`: two runs with the same public arguments and tape (`qOf`) leak
the same, whatever the registers they save. The entry loads `scratch_len`
from the stack, pinned once loaded; `zeroOut` and the length check load
`out`, `out_len` and the tape's length from the header, pinned once loaded;
the exit loads `scratch_len` from the header to find the save area.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- A run's public data: its arguments and tape, without the registers it
saves. -/
def qOf (s : State) : PP := (ppOf s).with (fun _ => 0) 0

/-- On entry. -/
def CI (q : PP) (s : State) : Prop := pcPre s ∧ qOf s = q

/-- `scratch_len` from the stack. -/
theorem entryL_ok {s : State} (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r12 .r11 0]) s fun t =>
      t.gpr .r12 = stackArg s 0 ∧ Keep [.r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, stackArg, Nat.reduceMul, Nat.reduceAdd] at hargs ⊢
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  prun [ea, hargs, BitVec.add_zero]

/-- The entry: the header's `out` and `out_len`. -/
theorem entry_ok (s : State) (h : pcPre s) :
    WP isa (.block entry) s fun t => Scr t (s.gpr .r10) (8 * (stackArg s 0).toNat) ∧ t.gpr .r31 = s.gpr .r10 ∧
      word t.mem (s.gpr .r10) 16 = s.gpr .r3 ∧ word t.mem (s.gpr .r10) 24 = s.gpr .r4 := by
  obtain ⟨hsp, hspT, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nwS, hb1, hb2, hL, hg, hsw⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  have hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  have h8n : 160 ≤ 8 * (stackArg s 0).toNat := by omega
  have hscr : Scr s (s.gpr .r10) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega)
  have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs h8n (hscr.st (by omega))) fun tA ⟨⟨a11, _, _⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a11 h8n (by omega) fun i hi => by
    rw [ka.wr]; exact hscr.st (by omega)) fun tS hS => ?_
  have hS10 : tS.gpr .r10 = s.gpr .r10 := by rw [hS.gpr, ka.gpr _ (by decide)]
  refine WP.mono (header_ok (s := tS) hS10 fun d hd => by
    rw [hS.wr, ka.wr]; exact hscr.st (d := d) (by omega)) fun t₁ ⟨⟨c31, _, cm⟩, kc⟩ => ?_
  have gS : ∀ r, r ∉ ([.r0, .r11, .r12] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr r hr
  obtain ⟨-, w16, w24, -⟩ := hdrW_words tS.mem (s.gpr .r10) (tS.gpr .r12)
    (tS.gpr .r3) (tS.gpr .r4) (tS.gpr .r5) (tS.gpr .r6) (((tS.gpr .r7).setWidth 32).setWidth 64) (tS.gpr .r8)
    (tS.gpr .r9)
  rw [← cm] at w16 w24
  have hwr₁ : t₁.wr = s.wr := by rw [kc.wr, hS.wr, ka.wr]
  exact ⟨hscr.congr hwr₁, c31, w16.trans (gS _ (by decide)), w24.trans (gS _ (by decide))⟩

/-- After `scratch_len`'s load. -/
def E1 (q : PP) (t : State) : Prop := t.gpr .r10 = q.B ∧ t.gpr .r12 = BitVec.ofNat 64 q.n

theorem pins_E1 : Pins E1 [.r10, .r12] := by
  rintro q s₁ s₂ ⟨a10, a12⟩ ⟨b10, b12⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a10, b10]
  · rw [a12, b12]

/-- After the entry. -/
def Z0 (q : PP) (t : State) : Prop :=
  ∃ Z, Scr t q.B Z ∧ 32 ≤ Z ∧ t.gpr .r31 = q.B ∧ t.mem.readW (q.B + BitVec.ofNat 64 16) 64 = q.op ∧
    t.mem.readW (q.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 q.L

theorem entry_ct : RelCT isa (Two CI) (.block entry) (Two Z0) := by
  refine two_post ?_ fun q s ⟨h, hq⟩ => ?_
  · rw [show entry = [.addSp .r11 96, .load .d .r12 .r11 0] ++ entry.drop 2 from rfl]
    refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide)) (Ψ := E1)
      fun q s ⟨h, hq⟩ => ?_) (two_taint _ pins_E1 (by taint_decide)))
    subst hq
    have hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
      ⟨⟨stackArgAddr s 0, 8⟩, by rw [h.2.2.1]; simp, by simp [Region.Contains]⟩
    exact WP.mono (entryL_ok hargs) fun t ⟨t12, k⟩ => ⟨k.gpr _ (by decide), t12.trans (ofNat_toNat _).symm⟩
  · subst hq
    have h' := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb1, -, hL, -, hsw⟩ := h'
    have hL' : (s.gpr .r4).toNat = (qOf s).L := hL
    simp only [Spec.Rsa.scratchWords] at hsw
    refine WP.mono (entry_ok s h) fun t ⟨hs, h31, w16, w24⟩ => ⟨_, hs, by omega, h31, w16, ?_⟩
    rw [← hL']; exact w24.trans (ofNat_toNat _).symm

/-- With `out` and `out_len` loaded. -/
def Z1 (q : PP) (t : State) : Prop := t.gpr .r4 = q.op ∧ t.gpr .r5 = BitVec.ofNat 64 q.L

theorem pins_Z1 : Pins Z1 [.r4, .r5] := by
  rintro q s₁ s₂ ⟨a4, a5⟩ ⟨b4, b5⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a4, b4]
  · rw [a5, b5]

theorem zeroOut_ct : RelCT isa (Two Z0) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint _ (pins_r31 PP.B fun _ _ ⟨_, _, _, h31, _⟩ => h31) (by taint_decide))
    (Ψ := Z1) fun q s ⟨Z, hs, hZ, h31, hO, hL⟩ => ?_) (two_taint _ pins_Z1 (by taint_decide))
  exact WP.mono (WP.keep [.r0, .r4, .r5] (Q := fun s₂ => s₂.gpr .r4 = q.op ∧ s₂.gpr .r5 = BitVec.ofNat 64 q.L)
    (by simp only [ldh, hOut, hLen]
        prun [h31, hO, hL, hs.ld (d := 16) (n := 8) (by omega), hs.ld (d := 24) (n := 8) (by omega)])
    (by decide)) fun _ ⟨h, _⟩ => h

/-- After the front. -/
def BI (q : PP) (t : State) : Prop := ∃ sv toc, St (q.with sv toc) t ∧ word t.mem q.B 152 = BitVec.ofNat 64 q.L

theorem front_ct : RelCT isa (Two CI) (.seq (.block entry) zeroOut) (Two BI) :=
  two_post (RelCT.seq entry_ct zeroOut_ct) fun _ s ⟨h, hq⟩ => by
    subst hq
    exact WP.mono (front_ok s h) fun _ ⟨st, hU, _⟩ => ⟨_, _, st, hU⟩

/-- With the tape's length and `out_len` loaded. -/
def L34 (q : PP) (t : State) : Prop :=
  t.gpr .r3 = BitVec.ofNat 64 q.r.length ∧ t.gpr .r4 = BitVec.ofNat 64 q.L

theorem pins_L34 : Pins L34 [.r3, .r4] := by
  rintro q s₁ s₂ ⟨a3, a4⟩ ⟨b3, b4⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a4, b4]

/-- After the length check. -/
def LC (q : PP) (t : State) : Prop :=
  isa.eval (.zero .d .r5) t = some (decide ((if q.L ≤ q.r.length then 1 else 0) = 0)) ∧
    ∃ sv toc, St (q.with sv toc) t ∧ word t.mem q.B 152 = BitVec.ofNat 64 q.L

theorem lenChk_ct :
    RelCT isa (Two BI) (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4)) (Two LC) :=
  two_post (RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_r31 PP.B fun _ _ ⟨_, _, h, _⟩ => h.r31)
      (by taint_decide)) (Ψ := L34) fun _ _ ⟨_, _, h, _⟩ => WP.mono (lenLoad_ok h) fun _ ⟨⟨a3, a4, _⟩, _⟩ =>
        ⟨a3, a4⟩) (two_taint _ pins_L34 (by taint_decide))))
    fun _ _ ⟨sv, toc, h, hU⟩ => WP.mono (lenChk_ok h hU) fun _ ⟨he, st, hU'⟩ => ⟨he, sv, toc, st, hU'⟩

/-- Before the exit. -/
def XE (q : PP) (t : State) : Prop := ∃ sv toc, ESt (q.with sv toc) t

theorem body_ct (R : RoundImpl) : RelCT isa (Two BI) (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++
    geFlag .r5 .r3 .r4)) (.ite (.zero .d .r5) (.block (finish 0)) (main R.name R.code))) (Two XE) := by
  refine two_post (RelCT.seq lenChk_ct (two_ite' (fun q => decide ((if q.L ≤ q.r.length then 1 else 0) = 0))
    (fun _ _ h => h.1) ?_ ?_)) fun _ _ ⟨sv, toc, h, hU⟩ => WP.mono (body_ok R h hU) fun _ ht => ⟨sv, toc, ht.1⟩
  · exact two_mono (fun _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => h.fs) (finish_ct (.inl rfl))
  · refine two_mono (fun q _ ⟨⟨_, sv, toc, h, hU⟩, hb⟩ => ⟨sv, toc, h, hU, ?_⟩) (main_ct R)
    by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega)])

/-- With the save area's word count loaded. -/
def X1 (q : PP) (t : State) : Prop := t.gpr .r11 = BitVec.ofNat 64 q.n ∧ t.gpr .r31 = q.B

theorem pins_X1 : Pins X1 [.r11, .r31] := by
  rintro q s₁ s₂ ⟨a11, a31⟩ ⟨b11, b31⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a31, b31]

theorem exit_ct : RelCT isa (Two XE) (.block exit) fun _ _ => True := by
  rw [show exit = [ldh .r11 hWsLen] ++ exit.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_r31 PP.B fun _ _ ⟨_, _, h⟩ => h.r31)
    (by taint_decide)) (Ψ := X1) fun q t ⟨sv, toc, h⟩ => ?_) (two_taint _ pins_X1 (by taint_decide)))
  have l0 : InRegions (t.rd ++ t.wr) ((q.with sv toc).B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by
    have := h.dims.n; simp only [PP.Z]; omega)
  exact WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = BitVec.ofNat 64 (q.with sv toc).n)
    (by simp only [ldh, hWsLen]; prun [h.r31, l0, show t.mem.readW ((q.with sv toc).B + BitVec.ofNat 64 0) 64 =
      BitVec.ofNat 64 (q.with sv toc).n from h.len]) (by decide)) fun _ ⟨u11, k⟩ =>
    ⟨u11, (k.gpr _ (by decide)).trans h.r31⟩

/-- `vg_ffdh_parameter_candidate` leaks the same from the same public
arguments and tape. -/
theorem code_rel (R : RoundImpl) : RelCT isa (Two CI) (code R.name R.code) fun _ _ => True := by
  unfold code
  exact RelCT.assoc (RelCT.seq front_ct (RelCT.assoc (RelCT.seq (body_ct R) exit_ct)))

theorem qOf_pub {s t : State} (h : pcPub s t) : qOf s = qOf t := by
  obtain ⟨hsp, hr, h3, -, h5, h6, h7, h8, -, h10, hst⟩ := h
  have hr' : pcRand s = pcRand t :=
    (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hr
  simp only [qOf, PP.with, ppOf, hsp, h3, h5, h6, h7, h8, h10, hst, hr']

/-- `vg_ffdh_parameter_candidate` in constant time, for any implementation of
the round. -/
theorem code_ct (R : RoundImpl) : ConstantTime isa pcContract.pre pcContract.pub (code R.name R.code) :=
  RelCT.constantTime ((code_rel R).mono (fun s _ ⟨hs, ht, hp⟩ => ⟨qOf s, ⟨hs, rfl⟩, ⟨ht, (qOf_pub hp).symm⟩, hp.1⟩)
    fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
