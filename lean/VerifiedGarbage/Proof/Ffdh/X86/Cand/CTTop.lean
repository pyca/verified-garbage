module

public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Top
import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTMain
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Impl.Ffdh.X86.Candidate
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Body
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Main
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# `vg_ffdh_parameter_candidate_sieved` on i686 in constant time

Runs with the same public arguments, table and tape take the same branch on
whether the tape is long enough, and then run `main` alike (`body_trace`);
the frame around the body is `wrap`'s (`constantTime`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86.Candidate
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Candidate.args)) (.block [])).isSome =
      true := by
  taint_decide
theorem bodyHead_check : ACheck (.block (entryWords ++ ([.mov .eax (.mem (argAt 0 12)), .alu .cmp .eax (.mem (argAt 0 3))] : List Instr))) := by
  dsimp only [ACheck]; taint_decide

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- Runs of the body with the same tape, `bits`, generator, `used` and table. -/
theorem body_trace {T : List Byte} {up Tb : BitVec 32} {bits g : Nat} (hbl : len = (bits + 7) / 8)
    (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg25 : g = 2 ∨ g = 5) :
    RelCT isa (Both fun f => Run Ex base bytes len args sp f ∧ Facts Ex base bytes len args sp T up Tb bits g f)
      Impl.Ffdh.X86.Candidate.body fun _ _ => True := by
  refine relCT_of_imp (A := TapeGeo Ex args base bytes sp T.length ∧ args 3 = BitVec.ofNat 32 len ∧
      Region.Disjoint ⟨Tb.setWidth 64, 8192⟩ ⟨base, bytes⟩) (fun ⟨G, h3, TA⟩ => ?_)
    fun x _ h => ⟨h.1.2.G, h.1.2.h3, h.1.2.TA⟩
  unfold Impl.Ffdh.X86.Candidate.body
  refine RelCT.seq (aRel (F := fun u => MAt Ex base bytes len args sp up T bits g Tb u ∧
      u.cf = some (decide (T.length < len))) (fun x h => h.1) bodyHead_check fun x ⟨R, F⟩ => ?_) ?_
  · have Gx : TapeGeo Ex args base bytes (x.gpr .esp) T.length := by rw [R.2.2]; exact G
    exact VG.X86.WP.mono_syms (bodyHead_ok R.1 G.len G.small h3 F.rb F.rg F.ru F.dws (by rw [R.2.2]; exact F.d40)
      hb2 hg25) fun u ⟨S, B, Gn, Us, _, c⟩ sy => by
        refine ⟨⟨⟨run_step R S, F.Ox.keep rfl S.keeps, Us, by rw [tape_keep Gx S, F.hT]⟩, B, Gn, ?_⟩, c⟩
        have := Table.step (by rw [R.2.2]; exact F.TT) S sy TA
        rwa [S.esp, R.2.2] at this
  refine ite_fixed (b := decide (T.length < len)) (fun _ h => h.2)
    (fun _ => short_trace fun x h => h.1.1) fun e => ?_
  have hL : len ≤ T.length := by simp at e; omega
  exact (main_trace G h3 hL hbl hb1 hb2 hg25 TA).mono (fun x y h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

/-! ## Against the contract -/

open VG.Proof.Ffdh.X86.KeyGen
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem pub_facts {s t : State} (H : contract.pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 9, arg s i = arg t i) ∧
      s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol ∧
      entryRand s = entryRand t := by
  sig_pub [contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi, argSlots,
    argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  refine ⟨SP, fun i hi => ?_, sy, inj L⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8

/-- What the body may read and write, once only the working space, `out` and `used` are writable. -/
theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (w : Region) :
    Rd s (rd ++ wr) [w, outR s, usedR s] :=
  let ⟨⟨r₁, h₁, c₁⟩, _, _, ⟨r₄, h₄, c₄⟩, ⟨r₅, h₅, c₅⟩⟩ := h
  ⟨⟨r₁, List.mem_append_left _ h₁, c₁⟩, ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩,
    ⟨r₄, List.mem_append_left _ h₄, c₄⟩, ⟨r₅, List.mem_append_left _ h₅, c₅⟩⟩

/-- The body's narrowed state, run from the frame's: a run with what the body needs. -/
theorem narrowed_facts {s f : State} (A : CandABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.Candidate.args s f)
    (sy : f.syms = s.syms) :
    Run (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
        (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s))
        (s.gpr .esp - BitVec.ofNat 32 argsFrame)
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s) f
          [outR s, usedR s]) ∧
      Facts (Rd s) (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s)
        (pLenOf Impl.Ffdh.X86.Candidate.args s) (synth Impl.Ffdh.X86.Candidate.args (arg s))
        (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryRand s) (arg s 2)
        (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (arg s 3).toNat (arg s 4).toNat
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args s) (wsSize Impl.Ffdh.X86.Candidate.args s) f
          [outR s, usedR s]) := by
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ (belowR s) := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have I := VG.Proof.Ffdh.X86.In.narrow Bf.1 (narrowRd Bf.1.extra
    ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩)
  refine ⟨⟨I, Bf.argsOk (wrapABI A) (Out := [outR s, usedR s]) fun r hr => ?_, Bf.2.1⟩,
    frame_facts A _ I Bf.2.1 Bf.2.2.2.2 sy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.belowOut.sub_left sub
  · exact A.belowUsed.sub_left sub

theorem constantTime : ConstantTime isa contract.pre contract.pub Impl.Ffdh.X86.Candidate.code := by
  intro s t tr ur sf tf S T H E F
  have A := candABI_of S
  have B := candABI_of T
  obtain ⟨SP, args, sy, tape⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.Candidate.args s = wsBase Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 7).setWidth 64 = (arg t 7).setWidth 64
    rw [args 7 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.Candidate.args s = wsSize Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 8).toNat * 8 = (arg t 8).toNat * 8
    rw [args 8 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.Candidate.args s = pLenOf Impl.Ffdh.X86.Candidate.args t := by
    show (arg s 1).toNat = (arg t 1).toNat
    rw [args 1 (by decide)]
  have hsy : synth Impl.Ffdh.X86.Candidate.args (arg t) = synth Impl.Ffdh.X86.Candidate.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hout : outR t = outR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hused : usedR t = usedR s := by
    show (⟨(arg t 2).setWidth 64, 8⟩ : Region) = ⟨(arg s 2).setWidth 64, 8⟩
    rw [args 2 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat ∧ InRegions wr ((arg t 2).setWidth 64) 8 ∧
        InRegions (rd ++ wr) (argAddr t 0) 36 ∧
        InRegions (rd ++ wr) ((t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64) 8192) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat ∧ InRegions wr ((arg s 2).setWidth 64) 8 ∧
        InRegions (rd ++ wr) (argAddr s 0) 36 ∧
        InRegions (rd ++ wr) ((s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).setWidth 64) 8192
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 5 (by decide), args 6 (by decide), sy,
      show argAddr t 0 = argAddr s 0 by simp only [argAddr, SP]]
  have ho : ∀ {x f : State}, CandABI x → BodyAt (Rd x) Impl.Ffdh.X86.Candidate.args x f →
      ∀ r ∈ [outR x, usedR x], r ∈ f.wr := fun X Bf r hr => by
    rw [Bf.2.2.2.1, X.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hw : ∀ {x f : State} (X : CandABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.Candidate.args x f),
      f.syms = x.syms → ∃ F, WP isa Impl.Ffdh.X86.Candidate.body
        (narrowed (wsBase Impl.Ffdh.X86.Candidate.args x) (wsSize Impl.Ffdh.X86.Candidate.args x) f
          [outR x, usedR x]) F := fun X Bf y => by
    obtain ⟨R, Fc⟩ := narrowed_facts X Bf y
    exact ⟨_, frame_ok X _ R.1 Bf.2.1 Bf.2.2.2.2 y⟩
  refine wrap_trace_syms (wrapABI A) (wrapABI B) args SP (rd_of A) (rd_of B) fill_check
    (fun f Bf y => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2)
    (fun f Bf y => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2 y) fun _ h => h.2.2) ?_ E F
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun f => f.rd ++ f.wr)
    (fun _ => ⟨wsBase Impl.Ffdh.X86.Candidate.args s, wsSize Impl.Ffdh.X86.Candidate.args s⟩ ::
      [outR s, usedR s]) (fun f g ⟨⟨B₁, y₁⟩, ⟨B₂, y₂⟩⟩ => ?_)
    (body_trace (Ex := Rd s) (base := wsBase Impl.Ffdh.X86.Candidate.args s)
      (bytes := wsSize Impl.Ffdh.X86.Candidate.args s) (args := synth Impl.Ffdh.X86.Candidate.args (arg s))
      (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) (T := entryRand s) (up := arg s 2)
      (Tb := s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) (hbl := A.outLen) A.bitsLow A.bitsHigh A.gen)
  have c₁ := B₁.covers (ho A B₁)
  have c₂ := B₂.covers (ho B B₂)
  have w₂ := hw B B₂ y₂
  have D₂ := narrowed_facts B B₂ y₂
  rw [← hws, ← hwz, hout, hused] at c₂ w₂ D₂
  rw [hRd, ← hpl, hsy, ← SP, ← tape, ← args 2 (by decide), ← args 3 (by decide), ← args 4 (by decide), ← sy] at D₂
  exact ⟨c₁.1, c₁.2, c₂.1, c₂.2, hw A B₁ y₁, w₂, narrowed_facts A B₁ y₁, D₂⟩

end VG.Proof.Ffdh.X86.Cand
