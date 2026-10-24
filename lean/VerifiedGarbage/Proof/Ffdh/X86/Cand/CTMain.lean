module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Main
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTSieve
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTTests
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTDraw
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTSmall
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTSieve
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Draw
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase

/-!
# The FFDH candidate on i686: the timing of p's checks

Runs with the same tape draw the same candidate p, so its congruences, the
divisions by small primes, its sieves and its tests run alike: each branch
is on a value the candidate fixes (`main_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

theorem congHead_check : ACheck (.block [.mov .eax (.mem (sc genOff)), .alu .cmp .eax (.imm 2)]) := by
  dsimp only [ACheck]; taint_decide
theorem gen2Head_check : ACheck (.block (lowWord (.slot .wide 9) ++ ([.alu .and .eax (.imm 7), .alu .cmp .eax (.imm 3)] : List Instr))) := by
  dsimp only [ACheck]; taint_decide
theorem minus2_check : ACheck (minus 2) := by dsimp only [ACheck]; taint_decide
theorem minus3_check : ACheck (minus 3) := by dsimp only [ACheck]; taint_decide
theorem bounds12_check : ACheck (.block (bounds (.slot .wide 12))) := by dsimp only [ACheck]; taint_decide
theorem divSetup3_check : RCheck [.esp, .eax] (.block (divSetup 3 inv3)) := by dsimp only [RCheck]; taint_decide
theorem divSetup5_check : RCheck [.esp, .eax] (.block (divSetup 5 inv5)) := by dsimp only [RCheck]; taint_decide
theorem load9_check : ACheck (load (.slot .wide 9) (one .wide) 2 3) := by dsimp only [ACheck]; taint_decide
theorem shapeB_check : ACheck (.block [.mov .eax (.mem (VG.Impl.Bignum.X86.PublicRt.argAt 0 3)), .store (sc curOff) .eax,
    .mov .eax (.mem (sc bitsOff)), .store (sc kOff) .eax]) := by dsimp only [ACheck]; taint_decide
theorem cutSetLow9_check : PCheck [.ecx, .edx] (.seq (.seq Impl.Ffdh.X86.Candidate.maskLoop <|
    .block (ptrTo (.slot .wide 9) .ebx .ecx ++ ([.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)),
      .alu .and .ecx (.reg .eax)] : List Instr) ++
      ([.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)] : List Instr) ++
      ([.store (at_ .ebx 0) .ecx] : List Instr))) (.block (setLow (.slot .wide 9)))) := by
  dsimp only [PCheck]; taint_decide
theorem setLow9_check : ACheck (.block (setLow (.slot .wide 9))) := by dsimp only [ACheck]; taint_decide
theorem testEax_check : ACheck testEax := by dsimp only [ACheck]; taint_decide
theorem half_check : ACheck half := by dsimp only [ACheck]; taint_decide
theorem oddQ_check : ACheck (.block (lowWord (.slot .wide 10) ++ ([.alu .and .eax (.imm 1)] : List Instr))) := by
  dsimp only [ACheck]; taint_decide
theorem sieveHead9_check : ACheck (.block (bounds (.slot .wide 9) ++ countBlock)) := by
  dsimp only [ACheck]; taint_decide
theorem sieveHead10_check : ACheck (.block (bounds (.slot .wide 10) ++ countBlock)) := by
  dsimp only [ACheck]; taint_decide
theorem mov0_check : ACheck (.block [.mov .eax (.imm 0)]) := by dsimp only [ACheck]; taint_decide
theorem storeOk_check : ACheck (.block [.store (sc okOff) .eax]) := by dsimp only [ACheck]; taint_decide
theorem orOk_check : ACheck (.block [.alu .or .eax (.mem (sc okOff))]) := by dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

theorem relCT_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc]
          exact ⟨ht, hq⟩

/-- A cut and what follows it, which the taint analysis checks with the cut's word and bits public. -/
theorem cutThen_trace {j : Nat} {top : Bool} {k : Prog isa} (hc : PCheck [.ecx, .edx] (.seq (cutRest j top) k))
    {n : Nat} (hn1 : 1 ≤ n) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base kOff = n) :
    RelCT isa (Both P) (.seq (cut (.slot .wide j) top) k) fun _ _ => True := by
  unfold cut
  refine relCT_assoc' (RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧
      v.gpr .ecx = BitVec.ofNat 32 ((n - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((n - 1) / 32)))
    (fun x h => (hP x h).1) cutHead_check fun x h => ?_)
    (pinned_end (rs := [.ecx, .edx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) hc))
  · obtain ⟨R, hk⟩ := hP x h
    have := cutHead_ok (is := []) (Q := fun v => Run Ex base bytes len args sp v ∧
        v.gpr .ecx = BitVec.ofNat 32 ((n - 1) % 32 + 1) ∧ v.gpr .edx = BitVec.ofNat 32 (4 * ((n - 1) / 32)))
      R.1 hk hn1 fun t m K ec ed =>
      WP.block_nil ⟨⟨R.1.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, ec, ed⟩
    rwa [List.append_nil] at this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.2.1, hy.2.1]
    · rw [hx.2.2, hy.2.2]

/-- A run, and p in wide slot 9. -/
abbrev PRun (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (p : Nat) (x : State) : Prop :=
  Run Ex base bytes len args sp x ∧ sv x.mem base len .wide 9 = p

theorem minus_run {p t : Nat} (ht : t ≤ p) (htl : t < 2 ^ 32) {x : State} (R : PRun Ex base bytes len args sp p x) :
    WP isa (minus t) x (PRun Ex base bytes len args sp p) :=
  WP.mono (minus_ok R.1.1 R.2 ht htl) fun _ ⟨S, _, k⟩ => ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩

theorem divides_run {prime inv p : Nat} (p3 : 3 ≤ prime) (p65 : prime ≤ 65537) (podd : prime % 2 = 1)
    (pinv : (prime * inv + 1) % 2 ^ 32 = 0) (invl : inv < 2 ^ 32) {x : State} (R : PRun Ex base bytes len args sp p x) :
    WP isa (divides (.slot .wide 12) prime inv) x (PRun Ex base bytes len args sp p) :=
  WP.mono (dividesS_ok R.1.1 (j := 12) (by decide) p3 p65 podd pinv invl) fun _ ⟨S, _, k⟩ =>
    ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩

/-- p's congruences, for runs with the same p and generator. -/
theorem congruences_trace {p g : Nat} (hp3 : 3 ≤ p) {P : State → Prop}
    (hP : ∀ x, P x → PRun Ex base bytes len args sp p x ∧ w32 x.mem base genOff = g) :
    RelCT isa (Both P) congruences fun _ _ => True := by
  unfold congruences
  refine RelCT.seq (aRel (F := fun u => PRun Ex base bytes len args sp p u ∧
      isa.eval .e u = some (decide (g = 2))) (fun x h => (hP x h).1.1) congHead_check fun x h => ?_) ?_
  · obtain ⟨R, hg⟩ := hP x h
    have gl : g < 2 ^ 32 := by rw [← hg]; exact (x.mem.readW _ 32).isLt
    refine wp_movS (hdr_read R.1.1 hdr_gen) fun u₁ U₁ _ => wp_cmpi fun u₂ F₂ _ z₂ => WP.block_nil ⟨?_, ?_⟩
    · have m₂ : u₂.mem = x.mem := by rw [F₂.mem, U₁.mem]
      exact ⟨run_step R.1 (Step.regs R.1.1 m₂ (U₁.keeps.trans (F₂.keeps _))), by rw [m₂, R.2]⟩
    · show u₂.zf = _
      rw [z₂, U₁.gpr, hg, show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, sub_beq gl (by decide)]
  refine ite_fixed (b := decide (g = 2)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · unfold gen2
    refine RelCT.seq (aRel (F := fun u => PRun Ex base bytes len args sp p u ∧
        isa.eval .e u = some (decide (p % 8 = 3))) (fun x h => h.1.1) gen2Head_check fun x ⟨R, _⟩ => ?_) ?_
    · refine lowWord_ok R.1.1 (j := 9) (by decide) fun u₃ m₃ K₃ e₃ => wp_andi fun u₄ U₄ =>
        wp_cmpi fun u₅ F₅ _ z₅ => WP.block_nil ⟨?_, ?_⟩
      · have m₅ : u₅.mem = x.mem := by rw [F₅.mem, U₄.mem, m₃]
        exact ⟨run_step R.1 (Step.regs R.1.1 m₅ ((K₃.trans (U₄.keeps.mono (by decide))).trans (F₅.keeps _))),
          by rw [m₅, R.2]⟩
      · have e₄ : u₄.gpr .eax = BitVec.ofNat 32 (p % 8) := by
          rw [U₄.gpr, e₃, R.2]
          apply BitVec.eq_of_toNat_eq
          have e8 : p % 2 ^ 32 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by decide)
          rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
            show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, e8,
            Nat.mod_eq_of_lt (by omega : p % 8 < 2 ^ 32)]
        show u₅.zf = _
        rw [z₅, e₄, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_beq (by omega) (by decide)]
    refine ite_fixed (b := decide (p % 8 = 3)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
    · exact RelCT.seq (aRel (fun x h => h.1.1) minus2_check fun x h => minus_run (by omega) (by decide) h.1)
        (divides_trace (by decide) bounds12_check divSetup3_check fun _ h => h.1)
    · exact aEnd (fun x h => h.1.1) mov0_check
  · unfold gen5
    refine RelCT.seq (aRel (fun x h => h.1.1) minus2_check fun x h => minus_run (by omega) (by decide) h.1) ?_
    refine RelCT.seq (relCT_both (divides_trace (by decide) bounds12_check divSetup5_check fun _ h => h.1)
      fun x h => divides_run (by decide) (by decide) (by decide) (by decide) (by decide) h) ?_
    refine RelCT.seq (aRel (F := PRun Ex base bytes len args sp p) (fun x h => h.1) storeOk_check fun x R =>
      hdr_store R.1.1 hdr_ok fun t S _ k _ _ _ _ => WP.block_nil ⟨run_step R.1 S, by rw [k.slot_eq, R.2]⟩) ?_
    refine RelCT.seq (aRel (fun x h => h.1) minus3_check fun x h => minus_run (by omega) (by decide) h) ?_
    refine RelCT.seq (relCT_both (divides_trace (by decide) bounds12_check divSetup5_check fun _ h => h.1)
      fun x h => divides_run (by decide) (by decide) (by decide) (by decide) (by decide) h) ?_
    exact aEnd (fun x h => h.1) orOk_check

/-- p from the tape, for runs with the same `bits`. -/
theorem shape_trace {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits : Nat} (hb1 : 1 ≤ bits) {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base bitsOff = bits) :
    RelCT isa (Both P) shape fun _ _ => True := by
  unfold shape
  refine RelCT.seq (aRel (F := fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base bitsOff = bits)
    (fun x h => (hP x h).1) load9_check fun x h => ?_) ?_
  · obtain ⟨R, hb⟩ := hP x h
    have hh := R.1
    have bl := hh.bytes_lt
    have f9 := slot_fit1 hh (j := 9) (by decide)
    have c1 := cb1 len
    have lb := len_le_bc len
    have lo' := hh.lower'
    have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [R.2.2]; exact G
    have fit := Gx.fit
    have small := Gx.small
    refine WP.mono (load_ok hh (one_ok .wide) f9 (p := 2) (l := 3) (L := len) (by decide) (by decide) h3
      (by omega) (by omega) (by omega)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        VG.CallLay.inRegions_sub (off := 0) (Gx.rd _ _ hh.extra) (by omega : 0 + len ≤ T.length) (by omega))
      (Gx.apart.sub_left (Region.sub_prefix hL))) fun u ⟨_, O, K⟩ => ?_
    rw [c1] at O
    exact ⟨run_step R (Step.slot hh (by decide) O K), by rw [(kept_slot hh O).word_eq, hb]⟩
  refine RelCT.seq (aRel (F := fun u => Run Ex base bytes len args sp u ∧ w32 u.mem base kOff = bits)
    (fun x h => h.1) shapeB_check fun x ⟨R, hb⟩ => ?_) ?_
  · have h₁ := R.1
    have bl : bits < 2 ^ 32 := by rw [← hb]; exact (x.mem.readW _ 32).isLt
    refine wp_movS (h₁.arg (i := 3) (by decide)) fun u₂ U₂ _ => ?_
    refine hdr_store (h₁.regs U₂.keeps U₂.mem) hdr_cur fun u₃ S₃ W₃ k₃ O₃ g₃ _ _ => ?_
    refine wp_movS (hdr_read S₃.inp hdr_bits) fun u₄ U₄ _ => ?_
    refine hdr_store (S₃.inp.regs U₄.keeps U₄.mem) hdr_k fun u₅ S₅ W₅ k₅ O₅ _ _ _ => WP.block_nil ⟨?_, ?_⟩
    · exact run_step R ((Step.regs h₁ U₂.mem U₂.keeps).trans (S₃.trans ((Step.regs S₃.inp U₄.mem U₄.keeps).trans S₅)))
    · rw [W₅, U₄.gpr, k₃.word_eq, U₂.mem, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bl]
  exact cutThen_trace cutSetLow9_check hb1 fun _ h => h

/-- `main`'s state: what results need, `bits`, the generator and RSA's table. -/
abbrev MAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (x : State) : Prop :=
  TCtx Ex base bytes len args sp up T x ∧ w32 x.mem base bitsOff = bits ∧ w32 x.mem base genOff = g ∧ Table Tb sp x

theorem MAt.step {up Tb : BitVec 32} {T : List Byte} {bits g : Nat} {x u : State}
    (A : MAt Ex base bytes len args sp up T bits g Tb x) (G : TapeGeo Ex args base bytes sp T.length)
    (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) (S : Step Ex base bytes len args x u)
    (sy : u.syms = x.syms) (hb : w32 u.mem base bitsOff = w32 x.mem base bitsOff)
    (hg : w32 u.mem base genOff = w32 x.mem base genOff) (hu : w32 u.mem base usedOff = w32 x.mem base usedOff) :
    MAt Ex base bytes len args sp up T bits g Tb u := by
  obtain ⟨C, b, gg, TT⟩ := A
  refine ⟨C.step G S hu, by rw [hb, b], by rw [hg, gg], ?_⟩
  have := Table.step (by rw [C.1.2.2]; exact TT) S sy TA
  rwa [S.esp, C.1.2.2] at this

theorem MAt.regs {up Tb : BitVec 32} {T : List Byte} {bits g : Nat} {x u : State}
    (A : MAt Ex base bytes len args sp up T bits g Tb x) (m : u.mem = x.mem) (K : Keeps [] x u)
    (sy : u.syms = x.syms) : MAt Ex base bytes len args sp up T bits g Tb u := by
  obtain ⟨C, b, gg, TT⟩ := A
  refine ⟨C.regs m K, by rw [m, b], by rw [m, gg], ?_⟩
  refine ⟨by rw [sy]; exact TT.sym, fun i hi d hd => by rw [K.2.1, K.2.2]; exact TT.read i hi d hd,
    fun i hi => by rw [m]; exact TT.words i hi, TT.fit, TT.far⟩

/-- p in wide slot 9 and the cursor past its octets. -/
abbrev PAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (p : Nat) (x : State) : Prop :=
  MAt Ex base bytes len args sp up T bits g Tb x ∧ sv x.mem base len .wide 9 = p ∧ w32 x.mem base curOff = len

/-- And q in wide slot 10. -/
abbrev QAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (bits g : Nat) (Tb : BitVec 32) (p : Nat) (x : State) : Prop :=
  PAt Ex base bytes len args sp up T bits g Tb p x ∧ sv x.mem base len .wide 10 = (p - 1) / 2

theorem QAt.regs {up Tb : BitVec 32} {T : List Byte} {bits g p : Nat} {x u : State}
    (A : QAt Ex base bytes len args sp up T bits g Tb p x) (m : u.mem = x.mem) (K : Keeps [] x u)
    (sy : u.syms = x.syms) : QAt Ex base bytes len args sp up T bits g Tb p u :=
  ⟨⟨A.1.1.regs m K sy, by rw [m, A.1.2.1], by rw [m, A.1.2.2]⟩, by rw [m, A.2]⟩

/-- `test eax, eax` of a flag in `eax`, with what holds through a comparison kept. -/
theorem testEax_run {Q : State → Prop} {b : Bool} (hcl : ∀ x v, Q x → v.mem = x.mem → Keeps [] x v →
    v.syms = x.syms → Q v) {x : State} (hq : Q x) (he : x.gpr .eax = BitVec.ofNat 32 b.toNat) :
    WP isa testEax x fun v => Q v ∧ isa.eval .e v = some (!b) ∧ isa.eval .ne v = some b :=
  VG.X86.WP.mono_syms (testEax_ok he) fun v ⟨m, K, z⟩ sy => ⟨hcl x v hq m K sy, z, by
    show v.zf.map (!·) = _; rw [show v.zf = _ from z]; simp⟩

/-- Runs of `main` with the same tape, `bits` and generator. -/
theorem main_trace {T : List Byte} (G : TapeGeo Ex args base bytes sp T.length) (h3 : args 3 = BitVec.ofNat 32 len)
    (hL : len ≤ T.length) {bits g : Nat} (hbl : len = (bits + 7) / 8) (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192)
    (hg25 : g = 2 ∨ g = 5) {up Tb : BitVec 32} (TA : Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) :
    RelCT isa (Both (MAt Ex base bytes len args sp up T bits g Tb)) main fun _ _ => True := by
  generalize hx : Spec.Rsa.os2ip (T.take len) = x
  obtain ⟨hpo, hpl, hpu⟩ := ParameterCandidate.candidate_shape (bits := bits) (by omega) x
  obtain ⟨hbp', hbp⟩ := ParameterCandidate.candidate_bitLength (bits := bits) (by omega) x
  have hbq' := ParameterCandidate.half_bitLength (bits := bits) (by omega) x
  have hbqp := fun qo => ParameterCandidate.half_pred_bitLength (bits := bits) (by omega) x qo
  generalize hp : Spec.Ffdh.candidateOf bits x = p at hpo hpl hpu hbp' hbp hbq' hbqp
  have big : 2 ^ 20 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have p8 : p < 2 ^ (8 * len) := Nat.lt_of_lt_of_le hpu (Nat.pow_le_pow_right (by decide) (by omega))
  have hp3 : 3 ≤ p := by omega
  have pcl : ∀ x v, PAt Ex base bytes len args sp up T bits g Tb p x → v.mem = x.mem → Keeps [] x v →
      v.syms = x.syms → PAt Ex base bytes len args sp up T bits g Tb p v :=
    fun x v A m K sy => ⟨A.1.regs m K sy, by rw [m, A.2.1], by rw [m, A.2.2]⟩
  unfold main
  -- p.
  refine RelCT.seq (relCT_both (F := PAt Ex base bytes len args sp up T bits g Tb p)
    (shape_trace G h3 hL (by omega) fun x h => ⟨h.1.1, h.2.1⟩) fun x A => ?_) ?_
  · have C := A.1
    exact VG.X86.WP.mono_syms (shape_ok C.1.1 (by rw [C.1.2.2]; exact G) C.2.2.2 h3 hL A.2.1 hbl hb1 hb2)
      fun u ⟨S, P₁, C₁, k₁⟩ sy => ⟨A.step G TA S sy k₁.word_eq k₁.word_eq k₁.word_eq, by rw [P₁, hx, hp], C₁⟩
  -- Its congruences.
  refine RelCT.seq (relCT_both (F := fun u => PAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (Spec.Ffdh.generationShape bits g p).toNat)
    (congruences_trace hp3 fun x h => ⟨⟨h.1.1.1, h.2.1⟩, h.1.2.2.1⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (congruences_ok A.1.1.1.1 A.2.1 hp3 hpo hbp' ⟨hb1, hb2⟩ A.1.2.2.1 hg25)
      fun u ⟨S, E, k⟩ sy => ⟨⟨A.1.step G TA S sy k.word_eq k.word_eq k.word_eq, by rw [k.slot_eq, A.2.1],
        by rw [k.word_eq, A.2.2]⟩, E⟩
  refine RelCT.seq (aRel (F := fun v => PAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!Spec.Ffdh.generationShape bits g p) ∧
      isa.eval .ne v = some (Spec.Ffdh.generationShape bits g p))
    (fun x h => h.1.1.1.1) testEax_check fun x h => testEax_run pcl h.1 h.2) ?_
  refine ite_fixed (b := !Spec.Ffdh.generationShape bits g p) (fun _ h => h.2.1)
    (fun _ => reject_trace fun x h => h.1.1.1) fun _ => ?_
  -- q, odd.
  refine RelCT.seq (aRel (F := QAt Ex base bytes len args sp up T bits g Tb p) (fun x h => h.1.1.1.1) half_check
    fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (half_ok A.1.1.1.1.1 A.1.2.1) fun u ⟨S, Q₄, k₄⟩ sy =>
      ⟨⟨A.1.1.step G TA S sy k₄.word_eq k₄.word_eq k₄.word_eq, by rw [k₄.slot_eq, A.1.2.1], by rw [k₄.word_eq, A.1.2.2]⟩,
        by rw [Q₄]; omega⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (decide ((p - 1) / 2 % 2 = 0))) (fun x h => h.1.1.1.1) oddQ_check fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (oddQ_ok A.1.1.1.1.1 A.2) fun u ⟨S, m, z⟩ sy =>
      ⟨⟨⟨A.1.1.step G TA S sy (by rw [m]) (by rw [m]) (by rw [m]), by rw [m, A.1.2.1], by rw [m, A.1.2.2]⟩,
        by rw [m, A.2]⟩, z⟩
  refine ite_fixed (b := decide ((p - 1) / 2 % 2 = 0)) (fun _ h => h.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun e => ?_
  have qo : (p - 1) / 2 % 2 = 1 := by simp at e; omega
  -- RSA's sieve of p, then of q.
  refine RelCT.seq (relCT_both (F := fun u => QAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)).toNat)
    (sieve_trace (j := 9) (by decide) sieveHead9_check (c := p) fun x h =>
      ⟨h.1.1.1.1.1, h.1.1.1.2.2.2, h.1.1.1.2.1, h.1.1.2.1⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (sieveS_ok A.1.1.1.1.1.1 (j := 9) (by decide) (by rw [A.1.1.1.1.1.2.2]; exact A.1.1.1.2.2.2)
      A.1.1.1.2.1) fun u ⟨S, E, k⟩ sy => ⟨⟨⟨A.1.1.1.step G TA S sy k.word_eq k.word_eq k.word_eq,
        by rw [k.slot_eq, A.1.1.2.1], by rw [k.word_eq, A.1.1.2.2]⟩, by rw [k.slot_eq, A.1.2]⟩, by rw [E, A.1.1.2.1]⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) ∧
      isa.eval .ne v = some (VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)))
    (fun x h => h.1.1.1.1.1) testEax_check fun x h => testEax_run (fun x v A m K sy => A.regs m K sy) h.1 h.2) ?_
  refine ite_fixed (b := VG.Proof.RsaKeyGen.trialPrefix p (sieveCount bits)) (fun _ h => h.2.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun _ => ?_
  refine RelCT.seq (relCT_both (F := fun u => QAt Ex base bytes len args sp up T bits g Tb p u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)).toNat)
    (sieve_trace (j := 10) (by decide) sieveHead10_check (c := (p - 1) / 2) fun x h =>
      ⟨h.1.1.1.1.1, h.1.1.1.2.2.2, h.1.1.1.2.1, h.1.2⟩) fun x A => ?_) ?_
  · exact VG.X86.WP.mono_syms (sieveS_ok A.1.1.1.1.1.1 (j := 10) (by decide) (by rw [A.1.1.1.1.1.2.2]; exact A.1.1.1.2.2.2)
      A.1.1.1.2.1) fun u ⟨S, E, k⟩ sy => ⟨⟨⟨A.1.1.1.step G TA S sy k.word_eq k.word_eq k.word_eq,
        by rw [k.slot_eq, A.1.1.2.1], by rw [k.word_eq, A.1.1.2.2]⟩, by rw [k.slot_eq, A.1.2]⟩, by rw [E, A.1.2]⟩
  refine RelCT.seq (aRel (F := fun v => QAt Ex base bytes len args sp up T bits g Tb p v ∧
      isa.eval .e v = some (!VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) ∧
      isa.eval .ne v = some (VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)))
    (fun x h => h.1.1.1.1.1) testEax_check fun x h => testEax_run (fun x v A m K sy => A.regs m K sy) h.1 h.2) ?_
  refine ite_fixed (b := VG.Proof.RsaKeyGen.trialPrefix ((p - 1) / 2) (sieveCount bits)) (fun _ h => h.2.2)
    (fun _ => reject_trace fun x h => h.1.1.1.1) fun _ => ?_
  -- The tests.
  have get : ∀ {x : State}, QAt Ex base bytes len args sp up T bits g Tb p x →
      TestsAt Ex base bytes len args sp up T bits p ((p - 1) / 2) len x :=
    fun h => ⟨h.1.1.1, h.1.1.2.1, h.1.2.1, h.2, h.1.2.2⟩
  exact (tests_trace G hb1 hb2 hp3 hpo (by omega) qo hbp (hbqp qo) p8 hL).mono
    (fun x y h => ⟨get h.1.1, get h.2.1⟩)
    fun _ _ h => h

end VG.Proof.Ffdh.X86.Cand
