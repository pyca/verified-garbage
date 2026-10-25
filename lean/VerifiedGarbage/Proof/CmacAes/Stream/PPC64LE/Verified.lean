module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.AbsorbCorrect
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.AbsorbCorrect
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Init
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Init
import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Finish
meta import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Finish
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming AES-CMAC on PPC64LE: constant time of `absorb`, and `Verified`

Two runs of `vg_cmac_aes_absorb` from states that agree on the public
arguments are related piece by piece (`RelCT`): the taint analysis covers
the code between the calls, from the registers the correctness proof pins
to values of the public arguments (`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`)
and the stack pointer, which no code changes (`wp_sp`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).

Then correctness and constant time of the three functions, a state
satisfying each precondition, and the shared contracts with the working
space as an argument (`Proof/CmacAes/Stream/Scratch.lean`), with no stack:
a call stores nothing in memory, and each function saves the return address
in the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
open VG.Proof.AesCbc.PPC64LE (taintRegs wp_sp)

/-! ## Constant time of `absorb` -/

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) (hsp : s.sp = s₀.sp) : WP isa updCall s (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .r14 (by decide), h.r14], by rw [h₆.saved .r15 (by decide), h.r15],
      by rw [h₆.saved .r16 (by decide), h.r16], by rw [h₆.saved .r17 (by decide), h.r17],
      by rw [h₆.saved .r19 (by decide), h.r19], by rw [h₆.sp, hsp], by rw [h₆.rd, h.rd],
      by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)) S R
    (nbOf (s₀.gpr .r5).toNat L)
  r14 : s.gpr .r14 = St
  r18 : s.gpr .r18 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .r5).toNat L)
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .r5).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x14₆, x15₆, x16₆, x17₆, x19₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x16₆ x17₆
  refine WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith) x17₆)) fun s₇ ⟨h₇, sp₇⟩ => ?_
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L), 16 * nbOf (s₀.gpr .r5).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L))
    (n := nbOf (s₀.gpr .r5).toNat L)
    (by rw [x3₇, x14₆]) (by rw [x4₇, x15₆]) (by rw [x5₇, x14₆]) (by rw [x6₇, x16₆]) x7₇
    (by rw [x8₇, x19₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega_arith)
    ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf (s₀.gpr .r5).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .r5).toNat L, rfl, by simp; omega_arith⟩,
    by rw [sv₇ .r14 (by decide) (by decide), x14₆], x18₇,
    by rw [sv₇ .r16 (by decide) (by decide), x16₆],
    by rw [sv₇ .r17 (by decide) (by decide), x17₆],
    by rw [sv₇ .r19 (by decide) (by decide), x19₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = St
  r18 : s.gpr .r18 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .r5).toNat L)
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  sp : s.sp = s₀.sp

theorem call2_after {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) : WP isa updCall s (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .r14 (by decide), h.r14], by rw [h₈.saved .r18 (by decide), h.r18],
      by rw [h₈.saved .r16 (by decide), h.r16], by rw [h₈.saved .r17 (by decide), h.r17],
      by rw [h₈.saved .r19 (by decide), h.r19], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbPPC64LE.pre s₀) (h0' : absorbPPC64LE.pre s₀')
    (hq : absorbPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat := by
    rw [q3, q4, q6, q7, q8]; exact APre.of h0'
  generalize s₀.gpr .r3 = St at hp hp'
  generalize s₀.gpr .r6 = D at hp hp'
  generalize s₀.gpr .r8 = S at hp hp'
  generalize (s₀.gpr .r7).toNat = L at hp hp'
  generalize (s₀.gpr .r4).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r17, .r19]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r16, .r17, .r18, .r19]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := fun (s : State) => AMid₁ s₀ St D S L R s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => AMid₁ s₀' St D S L R s ∧ s.sp = s₀'.sp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨wp_sp (absorbPre_wp hp), wp_sp (absorbPre_wp hp')⟩
  have c₁ := (upd_rel (P := fun a b => (AMid₁ s₀ St D S L R a ∧ a.sp = s₀.sp) ∧
      (AMid₁ s₀' St D S L R b ∧ b.sp = s₀'.sp))
    fun a b h => ⟨h.1.1.args, by rw [q5]; exact h.2.1.args, by rw [h.1.2, h.2.2, qsp]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h =>
      ⟨call1_after h.1.1 h.1.2, call1_after h.2.1 h.2.2⟩
  have m := (taintRegs (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b)
    [.r14, .r15, .r16, .r17, .r19]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r14, h.2.r14]
      · rw [h.1.r15, h.2.r15, q4]
      · rw [h.1.r16, h.2.r16, q5]
      · rw [h.1.r17, h.2.r17, q5]
      · rw [h.1.r19, h.2.r19]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q5]; exact h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after h.1, call2_after h.2⟩
  have p := taintRegs (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b)
    [.r14, .r16, .r17, .r18, .r19]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r14, h.2.r14]
      · rw [h.1.r16, h.2.r16, q5]
      · rw [h.1.r17, h.2.r17, q5]
      · rw [h.1.r18, h.2.r18, q5]
      · rw [h.1.r19, h.2.r19]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct : ConstantTime isa absorbPPC64LE.pre absorbPPC64LE.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem absorb_correct (s : State) (hs : absorbPPC64LE.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem finish_correct (s : State) (hs : finishPPC64LE.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finish_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 16 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified PPC64LE.target init (initScratchContract PPC64LE.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost,
      initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified PPC64LE.target absorb (absorbScratchContract PPC64LE.abi) :=
  Verified.of_correct absorb_correct absorb_ct (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost,
      absorbPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [absorbSat] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r6 => 0x2000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified PPC64LE.target finish (finishScratchContract PPC64LE.abi) :=
  Verified.of_correct finish_correct finish_ct (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost,
      finishPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [finishSat] using finishSat)

end VG.Proof.CmacAes.Stream.PPC64LE
