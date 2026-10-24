module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Sieve
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTSmall
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTBase
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Divides

/-!
# The FFDH candidate on i686: the sieve's timing

The sieve's frame is set up through the stack and the table's symbol, whose
addresses only `esp` fixes (`sieveSetup_trace`); RSA's sieve loop then
leaks which primes of the table divide the number (`loop_trace`), the same
for runs of the same number (`sieve_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Proof.RsaKeyGen.X86.Sieve (Geometry StackContext StateAt)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- The sieve's frame set up, from runs with `esp` at `p`. -/
theorem sieveSetup_trace {p : BitVec 32} (low : 4 ≤ p.toNat) :
    RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p) sieveSetup fun _ _ => True := by
  have first : RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p)
      (.block [.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .eax, .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx,
        .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 12) .edx])
      (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact S.trans T.symm
    refine ⟨((VG.Proof.Dsa.X86.checkedBlockInvariant (τ := τr [.esp]) rfl rfl) _ _ _ _ _ _ A E G).1, ?_, ?_⟩
    · rw [Exec.gpr (by decide) E, S]
    · rw [Exec.gpr (by decide) G, T]
  have middle : RelCT isa (fun a b => a.gpr .esp = p ∧ b.gpr .esp = p)
      VG.Impl.RsaKeyGen.X86.Sieve.tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := VG.Proof.Dsa.X86.wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := VG.Proof.Dsa.X86.wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  unfold sieveSetup
  exact RelCT.seq first (RelCT.seq middle ((VG.Proof.Dsa.X86.checkedBlockInvariant rfl rfl).mono
    (fun _ _ h => h) fun _ _ _ => trivial))

/-- The count block before the sieve's frame. -/
abbrev countBlock : List Instr := [.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025), .alu .sbb .edx (.reg .edx),
  .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)]

/-- Before the sieve's frame, from the state `s₀`: the number's address and end and the count. -/
abbrev SieveIn (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (P : State → Prop) (j bits : Nat) (u : State) : Prop :=
  ∃ s₀, P s₀ ∧ Run Ex base bytes len args sp u ∧ u.gpr .eax = slotPtr base len j ∧
    u.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide) ∧
    u.gpr .edx = BitVec.ofNat 32 (sieveCount bits) ∧ Keeps [.eax, .ecx, .edx] s₀ u ∧ u.mem = s₀.mem ∧
    u.syms = s₀.syms

/-- Runs of the sieve of the same number of wide slot `j`, for the same `bits`, with RSA's table at
`T`. -/
theorem sieve_trace {j : Nat} (hj : j ≤ 27) (hc : ACheck (.block (bounds (.slot .wide j) ++ countBlock)))
    {T : BitVec 32} {bits c : Nat} {P : State → Prop}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x ∧ Table T sp x ∧ w32 x.mem base bitsOff = bits ∧
      sv x.mem base len .wide j = c) :
    RelCT isa (Both P) (sieve (.slot .wide j)) fun _ _ => True := by
  refine relCT_of_imp (A := (sieveGeo sp (slotPtr base len j) T len bits).Valid ∧ 20 + 4 ≤ sp.toNat ∧
      (slotPtr base len j).toNat = base.toNat + lo len (.slot .wide j))
    (fun ⟨v, low, au⟩ => ?_) fun x _ h => by
      obtain ⟨R, TT, -, -⟩ := hP x h.1
      have hh := R.1
      have f := slot_fit1 hh hj
      rw [cb1] at f
      have nw := hh.scratch.nowrap
      have lw := hh.lower'
      have : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega
      have bc8 : bc len .wide = 8 * mw len := rfl
      have au : (slotPtr base len j).toNat = base.toNat + lo len (.slot .wide j) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have v := (sieveGeo_valid hh hj (by rw [R.2.2]; exact TT) au bits).1
      rw [R.2.2] at v
      exact ⟨v, by have := hh.room.low; rw [R.2.2] at this; omega, au⟩
  unfold sieve
  refine RelCT.seq (aRel (F := SieveIn Ex base bytes len args sp P j bits) (fun x h => (hP x h).1) hc
    fun x h => ?_) ?_
  · obtain ⟨R, TT, hb, -⟩ := hP x h
    have hh := R.1
    have pre : WP isa (.block (bounds (.slot .wide j) ++ (countBlock ++ []))) x fun u' =>
        Run Ex base bytes len args sp u' ∧ u'.gpr .eax = slotPtr base len j ∧
        u'.gpr .ecx = slotPtr base len j + BitVec.ofNat 32 (bc len .wide) ∧
        u'.gpr .edx = BitVec.ofNat 32 (sieveCount bits) ∧ Keeps [.eax, .ecx, .edx] x u' ∧ u'.mem = x.mem := by
      refine bounds_ok hh hj fun u mu Ku au' cu =>
        countBlock_ok (bits := bits) (hh.regs Ku mu) (by rw [mu]; exact hb) fun u' mu' Ku' du' => WP.block_nil ?_
      have K : Keeps [.eax, .ecx, .edx] x u' := Ku.trans (Ku'.mono (by decide))
      have m : u'.mem = x.mem := by rw [mu', mu]
      have e : u.gpr .eax = slotPtr base len j := by
        apply BitVec.eq_of_toNat_eq; rw [au', au]
      exact ⟨⟨hh.regs K m, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by rw [Ku'.1 _ (by decide), e],
        by rw [Ku'.1 _ (by decide), cu, e], du', K, m⟩
    rw [List.append_nil] at pre
    exact VG.X86.WP.mono_syms pre fun u ⟨a, b, c, d, e, f⟩ S => ⟨x, h, a, b, c, d, e, f, S⟩
  refine RelCT.seq (relCT_frame ?_) (restoreEdi_trace fun x y ⟨x₀, y₀, ⟨⟨_, _, R₀, _⟩, ⟨_, _, R₁, _⟩⟩, ex, ey⟩ => by
    rw [ex, ey, R₀.2.2, R₁.2.2])
  have setup : ∀ a, (∃ s₁, SieveIn Ex base bytes len args sp P j bits s₁ ∧ a = allocFrame 20 s₁) →
      WP isa sieveSetup a (StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits)) := by
    rintro a ⟨s₁, ⟨s₀, h₀, R, ea, ec, ed, K, m, Sy⟩, rfl⟩
    obtain ⟨R₀, TT, -, hc⟩ := hP s₀ h₀
    have W := sieveSetup_ok R₀.1 hj (by rw [R₀.2.2]; exact TT) au ea ec ed K m Sy
    rw [R₀.2.2, hc] at W
    exact WP.mono W fun _ h => h.1
  refine RelCT.seq ((((sieveSetup_trace (p := sp - BitVec.ofNat 32 20) (by rw [VG.X86.sub_toNat (by omega)]; omega)).mono
      (fun a b ⟨s₁, s₂, ⟨⟨_, _, R₁, _⟩, ⟨_, _, R₂, _⟩⟩, ea, eb⟩ => ⟨by rw [ea, allocFrame_esp, R₁.2.2],
        by rw [eb, allocFrame_esp, R₂.2.2]⟩) fun _ _ h => h).wp
    (F₁ := StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits))
    (F₂ := StateAt (sieveGeo sp (slotPtr base len j) T len bits) c 0 (sieveCount bits))
    fun a b ⟨s₁, s₂, ⟨B₁, B₂⟩, ea, eb⟩ => ⟨setup a ⟨s₁, B₁, ea⟩, setup b ⟨s₂, B₂, eb⟩⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2)
    ((VG.Proof.RsaKeyGen.X86.Sieve.loop_trace v (c := c) (d := c) fun _ _ => rfl).mono (fun _ _ h => h)
      fun _ _ _ => trivial)

end VG.Proof.Ffdh.X86.Cand
