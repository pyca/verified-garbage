module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Tests
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTPhase
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The FFDH candidate on i686: the tests' timing

Runs with the same moduli and tape run the same phases: each phase's status
is a function of them (`phase_ok`), so `onPass` takes the same side in both.
A result writes `used` through a pointer read from the header, which the
runs pin to the same argument (`usedTail_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86 VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate

theorem zeroOut_check : ACheck zeroOut := by dsimp only [ACheck]; taint_decide
theorem acceptOut_check : ACheck acceptOut := by dsimp only [ACheck]; taint_decide
theorem readUsed0_check : ACheck (.block [.mov .eax (.imm 0), .mov .ecx (.mem (sc usedOff))]) := by
  dsimp only [ACheck]; taint_decide
theorem readUsedCur_check : ACheck (.block [.mov .eax (.mem (sc curOff)), .mov .ecx (.mem (sc usedOff))]) := by
  dsimp only [ACheck]; taint_decide
theorem writeUsed0_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 0)]) := by dsimp only [PCheck]; taint_decide
theorem writeUsed1_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 1)]) := by dsimp only [PCheck]; taint_decide
theorem writeUsed2_check : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0),
    .store (at_ .ecx 4) .eax, .mov .eax (.imm 2)]) := by dsimp only [PCheck]; taint_decide
theorem cmp1_check : ACheck (.block [.alu .cmp .eax (.imm 1)]) := by dsimp only [ACheck]; taint_decide
theorem cmp2_check : ACheck (.block [.alu .cmp .eax (.imm 2)]) := by dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- What a result needs of a run: `out`'s place, `used` in the header and the tape. -/
abbrev TCtx (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp up : BitVec 32) (T : List Byte) (x : State) : Prop :=
  Run Ex base bytes len args sp x ∧ OutAt args base bytes len 0 sp x.wr ∧ w32 x.mem base usedOff = up.toNat ∧
    Spec.Rsa.bytesAt x.mem (byteAddr (args 2)) T.length = T

theorem TCtx.step {up : BitVec 32} {T : List Byte} {x u : State} (C : TCtx Ex base bytes len args sp up T x)
    (G : TapeGeo Ex args base bytes sp T.length) (S : Step Ex base bytes len args x u)
    (hu : w32 u.mem base usedOff = w32 x.mem base usedOff) : TCtx Ex base bytes len args sp up T u :=
  ⟨run_step C.1 S, C.2.1.keep rfl S.keeps, by rw [hu, C.2.2.1],
    by rw [tape_keep (by rw [C.1.2.2]; exact G) S, C.2.2.2]⟩

/-- `used` written through the pointer in the header, after `i` sets `eax`. -/
theorem usedTail_trace {i : Instr} {r : BitVec 32} {up : BitVec 32}
    (hc₁ : ACheck (.block [i, .mov .ecx (.mem (sc usedOff))]))
    (hc₂ : PCheck [.ecx] (.block [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0), .store (at_ .ecx 4) .eax,
      .mov .eax (.imm r)]))
    (hi : ∀ x, In Ex base bytes len args x → WP isa (.block [i]) x fun v => Keeps [.eax] x v ∧ v.mem = x.mem)
    {P : State → Prop} (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ w32 x.mem base usedOff = up.toNat) :
    RelCT isa (Both P) (.block ([i] ++ storeUsed ++ [.mov .eax (.imm r)])) fun _ _ => True := by
  have e : [i] ++ storeUsed ++ [.mov .eax (.imm r)] = [i, .mov .ecx (.mem (sc usedOff))] ++
      [.store (at_ .ecx 0) .eax, .mov .eax (.imm 0), .store (at_ .ecx 4) .eax, .mov .eax (.imm r)] := rfl
  rw [e]
  refine RelCT.block_append (RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧ v.gpr .ecx = up)
    (fun x h => (hP x h).1) hc₁ fun x h => ?_)
    (pinned_end (rs := [.ecx]) (fun _ h => h.1) (fun x y hx hy r hr => ?_) hc₂))
  · obtain ⟨R, hu⟩ := hP x h
    refine (WP.block_append_iff (M := isa) (l₁ := [i]) (l₂ := [Instr.mov .ecx (.mem (sc usedOff))])).mpr
      (WP.mono (hi x R.1) fun s₁ ⟨K₁, m₁⟩ => ?_)
    have h₁ : In Ex base bytes len args s₁ := R.1.regs K₁ m₁
    refine wp_movS (hdr_read h₁ hdr_used) fun v U _ => WP.block_nil ⟨?_, ?_⟩
    · have K : Keeps [.eax, .ecx] x v := (K₁.mono (by decide)).trans (U.keeps.mono (by decide))
      exact ⟨h₁.regs U.keeps U.mem, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
    · rw [U.gpr, m₁, hu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rw [hx.2, hy.2]

theorem movImm_keeps {x : State} {v : BitVec 32} :
    WP isa (.block [.mov .eax (.imm v)]) x fun u => Keeps [.eax] x u ∧ u.mem = x.mem :=
  wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩

theorem movCur_keeps {x : State} (h : In Ex base bytes len args x) :
    WP isa (.block [.mov .eax (.mem (sc curOff))]) x fun u => Keeps [.eax] x u ∧ u.mem = x.mem :=
  wp_movS (hdr_read h hdr_cur) fun _ U _ => WP.block_nil ⟨U.keeps, U.mem⟩

/-- `out` zeroed: what follows has the run and `used`. -/
theorem zeroOut_both {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) zeroOut (Both fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base usedOff = up.toNat) :=
  aRel (fun x h => (hP x h).1) zeroOut_check fun x h => by
    obtain ⟨R, Ox, hu, -⟩ := hP x h
    exact WP.mono (zeroOut_ok R.1 (by rw [R.2.2]; exact Ox)) fun v ⟨_, _, K, I, k⟩ =>
      ⟨⟨I, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [k.word_eq, hu]⟩

theorem short_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) short fun _ _ => True := by
  unfold short
  exact RelCT.seq (zeroOut_both hP) (usedTail_trace readUsed0_check writeUsed0_check (fun _ _ => movImm_keeps)
    fun _ h => h)

theorem reject_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x) :
    RelCT isa (Both P) reject fun _ _ => True := by
  unfold reject
  exact RelCT.seq (zeroOut_both hP) (usedTail_trace readUsedCur_check writeUsed2_check (fun _ h => movCur_keeps h)
    fun _ h => h)

theorem accept_trace {up : BitVec 32} {T : List Byte} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x ∧ sv x.mem base len .wide 9 < 2 ^ (8 * len)) :
    RelCT isa (Both P) Impl.Ffdh.X86.Candidate.accept fun _ _ => True := by
  unfold Impl.Ffdh.X86.Candidate.accept
  refine RelCT.seq (aRel (F := fun v => Run Ex base bytes len args sp v ∧ w32 v.mem base usedOff = up.toNat)
    (fun x h => (hP x h).1.1) acceptOut_check fun x h => ?_)
    (usedTail_trace readUsedCur_check writeUsed1_check (fun _ h => movCur_keeps h) fun _ h => h)
  obtain ⟨⟨R, Ox, hu, -⟩, hpl⟩ := hP x h
  exact WP.mono (acceptOut_ok R.1 (by rw [R.2.2]; exact Ox) rfl hpl) fun v ⟨_, _, K, I, k⟩ =>
    ⟨⟨I, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [k.word_eq, hu]⟩

/-- The status compared with `k`. -/
theorem cmpStatus_ok {s : State} {D : Option (Bool × Spec.RsaKeyGen.Rand)}
    (he : s.gpr .eax = BitVec.ofNat 32 (drawStatus D)) {k : Nat} (hk : k < 4) :
    WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))]) s fun u =>
      isa.eval .e u = some (decide (drawStatus D = k)) ∧ u.mem = s.mem ∧ Keeps [] s u ∧ u.gpr .eax = s.gpr .eax := by
  have st : drawStatus D < 4 := by unfold drawStatus; split <;> decide
  refine wp_cmpi fun u F _ z => WP.block_nil ⟨?_, F.mem, F.keeps [], congrFun F.gpr _⟩
  show u.zf = _
  rw [z, he]
  exact congrArg some (sub_beq (by omega) (by omega))

/-- After a phase whose result `D` the runs share: on to `rest` if it passed, else a rejection or a
shortage. `P` holds through a comparison. -/
theorem onPass_trace {up : BitVec 32} {T : List Byte} {D : Option (Bool × Spec.RsaKeyGen.Rand)} {P : State → Prop}
    (hP : ∀ x, P x → TCtx Ex base bytes len args sp up T x ∧ x.gpr .eax = BitVec.ofNat 32 (drawStatus D))
    (hcl : ∀ x v, P x → v.mem = x.mem → Keeps [] x v → P v)
    {rest : Prog isa} (hrest : drawStatus D = 1 → RelCT isa (Both P) rest fun _ _ => True) :
    RelCT isa (Both P) (onPass rest) fun _ _ => True := by
  have cmp : ∀ k, k < 4 → ∀ x, P x → WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 k))]) x fun v =>
      P v ∧ isa.eval .e v = some (decide (drawStatus D = k)) := fun k hk x h =>
    WP.mono (cmpStatus_ok (hP x h).2 hk) fun v ⟨e, m, K, _⟩ => ⟨hcl x v h m K, e⟩
  unfold onPass
  refine RelCT.seq (aRel (fun x h => (hP x h).1.1) cmp1_check (cmp 1 (by decide))) ?_
  refine ite_fixed (b := decide (drawStatus D = 1)) (fun _ h => h.2) (fun e => ?_) fun _ => ?_
  · exact (hrest (by simpa using e)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h
  refine RelCT.seq (aRel (fun x h => (hP x h.1).1.1) cmp2_check fun x h => cmp 2 (by decide) x h.1) ?_
  refine ite_fixed (b := decide (drawStatus D = 2)) (fun _ h => h.2) (fun _ => ?_) fun _ => ?_
  · exact reject_trace fun x h => (hP x h.1).1
  · exact short_trace fun x h => (hP x h.1).1

end VG.Proof.Ffdh.X86.Cand
