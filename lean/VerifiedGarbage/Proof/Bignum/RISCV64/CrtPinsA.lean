module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
public import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Bignum.RISCV64.CrtCTBase`, which only this module used -/

section

/-!
# The RSA private-key operation on RISC-V: constant time, the front

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. Two runs are related by `Two` for the same public
data. The taint analysis keeps memory secret, so the working space's
address, from the stack, is pinned once loaded (`L1`); the code's list of
programs (`crtF`) is cut after each later block that loads the header's
words (`Reach.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero)

variable {pc : Bool}

/-- The argument registers of `vg_rsa_private_crt`, and with `pc`, of
`vg_rsa_private_crt_precomputed`: `s1` too. -/
abbrev argRegsG (pc : Bool) : List Reg := if pc then argRegs ++ [.s1] else argRegs

/-- The public data of a run. -/
def dataOf (pc : Bool) (s : State) : List (BitVec 64) × List (BitVec 64) × List Byte :=
  ((argRegsG pc).map s.gpr, (List.range 10).map (stackArg s),
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)

/-- The precondition: `fnContract`'s, or with `pc`, `fnContractP`'s. -/
def preG : Bool → State → Prop
  | false => fnContract.pre
  | true => fnContractP.pre

/-- The regions read beyond `baseRd`: with `pc`, the cached values'. -/
def xRd : Bool → State → List Region
  | false, _ => []
  | true, s => [r2R s]

theorem preG_core {s : State} (h : preG pc s) : preCore (baseRd s ++ xRd pc s) s := by
  cases pc
  · show preCore (baseRd s ++ []) s; rw [List.append_nil]; exact h
  · exact h.1

/-- On entry. -/
def C0 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  preG pc s ∧ dataOf pc s = d

theorem C0.pf {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 pc d s) : PF s :=
  pre_factsG (preG_core h.1)

/-- What the public data fixes. -/
structure DataEq (pc : Bool) (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  a6 : s₀.gpr .a6 = s₀'.gpr .a6
  a7 : s₀.gpr .a7 = s₀'.gpr .a7
  s1 : pc = true → s₀.gpr .s1 = s₀'.gpr .s1
  sa : ∀ i < 10, stackArg s₀ i = stackArg s₀' i
  nb : Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat =
    Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .a2) (s₀'.gpr .a3).toNat

theorem dataEq_of {s₀ s₀' : State} (h : dataOf pc s₀ = dataOf pc s₀') : DataEq pc s₀ s₀' := by
  have h1 : (argRegsG pc).map s₀.gpr = (argRegsG pc).map s₀'.gpr := congrArg Prod.fst h
  have h2 : (List.range 10).map (stackArg s₀) = (List.range 10).map (stackArg s₀') :=
    congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  have m := List.map_inj_left.mp h1
  have a : ∀ r ∈ argRegs, r ∈ argRegsG pc := fun r hr => by
    cases pc
    · exact hr
    · exact List.mem_append_left _ hr
  exact ⟨m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)),
    m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)), m _ (a _ (by decide)),
    fun hp => m _ (by subst hp; decide), fun i hi => List.map_inj_left.mp h2 i (List.mem_range.mpr hi), h3⟩

theorem two_data {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') : DataEq pc s₀ s₀' := dataEq_of (h.2.trans h'.2.symm)

theorem pins_C0 : Pins (C0 pc) [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

/-- After loading the working space's address. -/
def L1 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  ∃ s₀, C0 pc d s₀ ∧ s.gpr .t0 = stackArg s₀ 8 ∧ Keep [.t0] s₀ s

theorem pins_L1 : Pins (L1 pc) [.t0, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a0', k⟩ ⟨s₀', h₀', b0', k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0', b0', E.sa 8 (by decide)]
  all_goals rw [k.gpr (by decide), k'.gpr (by decide)]
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

theorem loadS_L1 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 pc d s) :
    WP isa (.block [.addSp .t0 64, .load .d .t0 .t0 0]) s (L1 pc d) := by
  have hp := preG_core h.1
  obtain ⟨hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl, alS, alsp⟩ := hp
  have hst : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := by
    refine ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; exact List.mem_append_left _ (by simp [baseRd])), ?_⟩
    show (s.sp + BitVec.ofNat 64 64 - (s.sp + BitVec.ofNat 64 (8 * 0))).toNat + 8 ≤ 80
    rw [show 8 * 0 = 0 from rfl, Offset.sub_toNat s.sp (by omega_using []) (by omega_using [])]; omega_using []
  have hsa : (s.sp + BitVec.ofNat 64 64).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = stackArg s 8) ?_ (by rfl) (by rfl))
    fun t ⟨a0, k⟩ => ⟨s, h, a0, k⟩
  brun [exec_addSp (show 64 < 2048 by decide), add_ofNat_zero, hst, hsa]
  rfl

/-- The code's list of programs. -/
abbrev crtF (pc : Bool) : List (Prog isa) := Code.flat (crtG pc)

theorem crt_run (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) (h : C0 pc d s) :
    WP isa (Code.seqL (crtF pc)) s fun _ => True := by
  cases pc
  · let ⟨tr, t, e, _⟩ := fn_correct s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩
  · let ⟨tr, t, e, _⟩ := fn_correctP s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩

theorem front_rel : RelCT isa (Two (C0 pc)) (.block (Crt.save ++ argsG pc ++ setupX)) fun _ _ => True := by
  unfold Crt.save
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.block_append (M := isa) (l₁ := ([.addSp .t0 64, .load .d .t0 .t0 0] : List Instr)) ?_
  cases pc
  · exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide))
  · exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide))

end VG.Proof.Bignum.RISCV64.Crt

end

end

/-!
# The RSA private-key operation on RISC-V: the registers at the cuts of `loadX`

The code's list of programs (`crtF`) is cut after each block that loads a
buffer's address and length from the header, and after `n`'s first byte
(`check1`): the registers there, from the initial state (`pins*`). In
`loadX`, `XI` is what a buffer's load needs: `X`'s registers and the header
as the front left it.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero At pins_at_list)
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)

variable {pc : Bool}

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := ⟨[], s, .block rfl, h⟩

theorem wp_seqL_nil {l : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa (Code.seqL (l ++ ([.block []] : List (Prog isa)))) s Q) : WP isa (Code.seqL l) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  obtain ⟨_, _, u, -, e₁, e₂⟩ := exec_seqL_append.mp e
  cases e₂ with
  | seq x y =>
    obtain ⟨-, rfl⟩ := exec_nil_iff.mp x
    obtain ⟨-, rfl⟩ := exec_nil_iff.mp y
    exact ⟨_, _, e₁, hq⟩

/-- What two initial states with the same public data share. -/
theorem data_vals {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') :
    cS s₀ = cS s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' ∧ s₀.gpr .a0 = s₀'.gpr .a0 ∧
      s₀.gpr .a2 = s₀'.gpr .a2 ∧ s₀.gpr .a4 = s₀'.gpr .a4 ∧ s₀.gpr .a6 = s₀'.gpr .a6 ∧
      stackArg s₀ 0 = stackArg s₀' 0 ∧ stackArg s₀ 2 = stackArg s₀' 2 ∧ stackArg s₀ 4 = stackArg s₀' 4 ∧
      stackArg s₀ 6 = stackArg s₀' 6 ∧
      Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀) = Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .a2) (ck s₀') := by
  have E := two_data h h'
  exact ⟨E.sa 8 (by decide), by simp only [ck, E.a3], by simp only [cpL, E.a7],
    by show (stackArg s₀ 1).toNat = (stackArg s₀' 1).toNat; rw [E.sa 1 (by decide)],
    E.a0, E.a2, E.a4, E.a6, E.sa 0 (by decide), E.sa 2 (by decide), E.sa 4 (by decide), E.sa 6 (by decide), E.nb⟩

/-- Two header words into `s7` and `s8`. -/
theorem ld2_ok {t : State} {S A : Addr} {Z oA oL L : Nat} (hs : Scr t S Z) (hZ : 256 ≤ Z)
    (h6 : t.gpr .s6 = S) (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : Mont.word t.mem S oA = Mont.off A 0) (hLw : Mont.word t.mem S oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]) t fun u =>
      (u.gpr .s7 = Mont.off A 0 ∧ u.gpr .s8 = BitVec.ofNat 64 L ∧ u.mem = t.mem) ∧ Keep [.s7, .s8] t u := by
  have h6' : t.gpr .s6 = Mont.off S 0 := h6.trans (z0 _)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h6', Nat.zero_add, hs.ld (show oA + 8 ≤ Z by omega_arith), hs.al8 (show oA + 8 ≤ Z by omega_arith) hoA.2,
    hs.ld (show oL + 8 ≤ Z by omega_arith), hs.al8 (show oL + 8 ≤ Z by omega_arith) hoL.2,
    show oA < 2048 by omega_arith, show oL < 2048 by omega_arith, hA, hLw]

/-- In `loadX`, after the front left `s`. -/
structure XI (s₀ s t : State) : Prop where
  scr : Scr t (cS s₀) (cZ s₀)
  s6 : t.gpr .s6 = cS s₀
  a7 : t.gpr .a7 = Mont.off (cS s₀) (slot (cwX s₀) 0)
  ra : t.gpr .ra = Mont.off (cS s₀) (slot (cwX s₀) 0)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  s11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  t0 : t.gpr .t0 = BitVec.ofNat 64 (cwX s₀)
  out : Mont.Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem
  rd : t.rd ++ t.wr = s₀.rd ++ s₀.wr

theorem xi_front {s₀ s : State} (F : Front s₀ s) : XI s₀ s s :=
  ⟨F.scr, F.s6, F.a7, F.ra, F.s5, F.s11, F.t0, Mont.Outside.refl _ _ _ _, by rw [F.keep.2.1, F.keep.2.2]⟩

theorem XI.hdr {s₀ s t : State} (hP : PF s₀) (X : XI s₀ s t) {d : Nat} (hd : d + 8 ≤ 256) :
    Mont.word t.mem (cS s₀) d = Mont.word s.mem (cS s₀) d := by
  have hn := hP.nw; have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  exact Mont.Outside.word X.out (Or.inl hd) (by unfold slot at room; omega_arith)

/-- `XI` through code that keeps `X`'s registers and changes only its arrays. -/
theorem XI.step {s₀ s t u : State} (hP : PF s₀) (X : XI s₀ s t) {rs : List Reg} (k : Keep rs t u)
    (h : ∀ r ∈ [Reg.s6, .ra, .s5, .s11, .t0], r ∉ rs)
    (h7 : u.gpr .a7 = Mont.off (cS s₀) (slot (cwX s₀) 0)) {o n : Nat}
    (o' : Mont.Outside (cS s₀) o n t.mem u.mem) (ho : 256 ≤ o) (hn : o + n ≤ slot (cwX s₀) 8) : XI s₀ s u := by
  have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨X.scr.congr k.2.2, (k.gpr h.1).trans X.s6, h7, (k.gpr h.2.1).trans X.ra, (k.gpr h.2.2.1).trans X.s5,
    (k.gpr h.2.2.2.1).trans X.s11, (k.gpr h.2.2.2.2).trans X.t0,
    X.out.trans (o'.mono ho (by unfold slot at room; omega_arith)), by rw [k.2.1, k.2.2]; exact X.rd⟩

/-- `t3 := a7`, then `X`'s array 0 := all ones. -/
theorem xi_ones {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (X : XI s₀ s t)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.block [.addi .t3 .a7 0]) (.seq onesWords c)) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e0 : slot (cwX s₀) 0 = 256 + 0 * (8 * (cwX s₀ + 2)) := rfl
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = Mont.off (cS s₀) (slot (cwX s₀) 0) ∧
    u.mem = t.mem) (by brun [X.a7, BitVec.add_zero]) (by rfl) (by rfl)) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (X.scr.congr k1.2.2) a3 ((k1.gpr (by decide)).trans X.t0) (by omega_arith)
    (by omega_arith) (slot_al _ _) (by unfold slot at room; omega_arith)) fun t₂ ⟨⟨_, _, o2⟩, k2⟩ => hc t₂ ?_)
  rw [m1] at o2
  exact XI.step hP X (k1.trans k2) (by decide) ((k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans X.a7))
    o2 (by omega_arith) (by omega_arith)

/-- A buffer into `X`'s array `j`. -/
theorem xi_load {s₀ s t : State} {c : Prog isa} {Q : State → Prop} {j oA oL : Nat} {A : Addr} {L : Nat}
    (hP : PF s₀) (X : XI s₀ s t) (hj : j < 8)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : Mont.word s.mem (cS s₀) oA = Mont.off A 0) (hLw : Mont.word s.mem (cS s₀) oL = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hLk : L ≤ ck s₀) (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (Mont.off A i) 1)
    (hsep : ∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → Mont.off A i ≠ x)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.seq (.block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]) (loadArr j)) c) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (loadOne_ok X.scr (by unfold slot at room; omega_arith) hj (by omega_arith)
    (X.s6.trans (z0 _)) X.a7 X.ra X.s5 X.t0 hoA hoL (by rw [X.hdr hP hoA.1]; exact hA)
    (by rw [X.hdr hP hoL.1]; exact hLw) hL (by omega_arith) ⟨by rw [X.rd]; exact hrd, hsep⟩)
    fun u ⟨⟨_, _, o, u7⟩, k⟩ => hc u ?_)
  have := VG.Proof.Bignum.slot_le (w := cwX s₀) hj
  have h256 : 256 ≤ slot (cwX s₀) j := Nat.le_add_right _ _
  exact XI.step hP X k (by decide) u7 o h256 (by omega_arith)

/-- `X`'s registers. -/
abbrev rsX : List Reg := [.a7, .ra, .s5, .s11, .t0, .s6]

abbrev valsX (s₀ : State) : List (BitVec 64) :=
  [Mont.off (cS s₀) (slot (cwX s₀) 0), Mont.off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
    BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (cwX s₀), cS s₀]

theorem valsX_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') : valsX s₀ = valsX s₀' := by
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [valsX, cwX, eS, ek]

/-- The registers after a buffer's address and length. -/
theorem xi_ld {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : Mont.word s.mem (cS s₀) oA = Mont.off A 0) (hLw : Mont.word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]) t fun u =>
      (rsX ++ ([.s7, .s8] : List Reg)).map u.gpr = valsX s₀ ++ [Mont.off A 0, BitVec.ofNat 64 L] := by
  have room := hP.room
  refine WP.mono (ld2_ok (A := A) (L := L) X.scr (by unfold slot at room; omega_arith) X.s6 hoA hoL
    (by rw [X.hdr hP hoA.1]; exact hA) (by rw [X.hdr hP hoL.1]; exact hLw)) fun u ⟨⟨a7, a8, _⟩, k⟩ => ?_
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, a7, a8, k.gpr (r := .a7) (by decide),
    k.gpr (r := .ra) (by decide), k.gpr (r := .s5) (by decide), k.gpr (r := .s11) (by decide),
    k.gpr (r := .t0) (by decide), k.gpr (r := .s6) (by decide), X.a7, X.ra, X.s5, X.s11, X.t0, X.s6]

theorem pins1 : Pins (At (C0 pc) (crtF pc) 1) rsX :=
  pins_at_list valsX
    (fun _ s₀ h => WP.of_flat (c := .block (Crt.save ++ argsG pc ++ setupX)) (by cases pc <;> rfl)
      (WP.mono (front_okG (pc := pc) s₀ (preG_core h.1)) fun s ⟨F, _⟩ => by
        simp only [rsX, valsX, List.map_cons, List.map_nil, F.a7, F.ra, F.s5, F.s11, F.t0, F.s6]))
    fun _ _ _ h h' => valsX_eq h h'

/-- A buffer's address and length, as a block. -/
abbrev LD (oA oL : Nat) : Prog isa := .block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]

/-- The front, then `X`'s array 0 := all ones, then `c`. -/
abbrev N0 (pc : Bool) (c : Prog isa) : Prog isa :=
  .seq (.block (Crt.save ++ argsG pc ++ setupX)) (.seq (.block [.addi .t3 .a7 0]) (.seq onesWords c))

/-- A buffer into array `j`, then `c`. -/
abbrev LJ (j oA oL : Nat) (c : Prog isa) : Prog isa := .seq (.seq (LD oA oL) (loadArr j)) c

theorem xi_start {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → XI s₀ s t → WP isa c t Q) :
    WP isa (N0 pc c) s₀ Q :=
  WP.seq (WP.mono (front_okG (pc := pc) s₀ (preG_core h.1)) fun s F => xi_ones h.pf (xi_front F.1) fun t X =>
    hc s t h.pf F.1 X)

theorem ldv_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') {A A' : Addr} {L L' : Nat} (hA : A = A') (hL : L = L') :
    valsX s₀ ++ [Mont.off A 0, BitVec.ofNat 64 L] = valsX s₀' ++ [Mont.off A' 0, BitVec.ofNat 64 L'] := by
  rw [valsX_eq h h', hA, hL]

theorem pins5 : Pins (At (C0 pc) (crtF pc) 5) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a2) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LD oN oNLen)) (by cases pc <;> rfl) (xi_start h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) F.hN F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.1 E.2.1

theorem pins13 : Pins (At (C0 pc) (crtF pc) 13) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a6) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LD oP oPLen))) (by cases pc <;> rfl) (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hP F.hPL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.2.1 E.2.2.1

theorem pins21 : Pins (At (C0 pc) (crtF pc) 21) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (stackArg s₀ 0) 0, BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LD oQ oQLen)))) (by cases pc <;> rfl)
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hQ F.hQL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.2.2.1 E.2.2.2.1

theorem pins29 : Pins (At (C0 pc) (crtF pc) 29) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a4) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LD oIn oNLen))))) (by cases pc <;> rfl)
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
        hP.rQ hP.sQ fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hIn F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.1 E.2.1

theorem pins37 : Pins (At (C0 pc) (crtF pc) 37) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (stackArg s₀ 6) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat
      (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LJ 6 oIn oNLen (LD oQInv oPLen)))))) (by cases pc <;> rfl)
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
        hP.rQ hP.sQ fun _ X =>
      xi_load (j := 6) hP X (by decide) (by decide) (by decide) F.hIn F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rI hP.sI fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hQI F.hPL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.2.2.2.2.2.1 E.2.2.1

/-- `loadX`, from the front, then `c`. -/
abbrev NX (pc : Bool) (c : Prog isa) : Prog isa :=
  N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LJ 6 oIn oNLen (LJ 7 oQInv oPLen c)))))

theorem xi_loadX {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → XI s₀ s t → WP isa c t Q) :
    WP isa (NX pc c) s₀ Q :=
  xi_start h fun s _ hP F X =>
    xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
      (Nat.le_refl _) hP.rN hP.sN fun _ X =>
    xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
      hP.rP hP.sP fun _ X =>
    xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
      hP.rQ hP.sQ fun _ X =>
    xi_load (j := 6) hP X (by decide) (by decide) (by decide) F.hIn F.hNL (by have := hP.k64; omega_arith)
      (Nat.le_refl _) hP.rI hP.sI fun _ X =>
    xi_load (j := 7) hP X (by decide) (by decide) (by decide) F.hQI F.hPL hP.p1 (Nat.le_of_lt hP.pk)
      hP.rQI hP.sQI fun t X => hc s t hP F X

theorem pins45 : Pins (At (C0 pc) (crtF pc) 45) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a2) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := NX pc (LD oN oNLen)) (by cases pc <;> rfl) (xi_loadX h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) F.hN F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.1 E.2.1

/-- `n`'s first byte. -/
abbrev nb0 (s₀ : State) : BitVec 64 :=
  BitVec.ofNat 64 ((Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀)).getD 0 0).toNat

theorem pins46 : Pins (At (C0 pc) (crtF pc) 46) (rsX ++ ([.s8, .t4] : List Reg)) := by
  refine pins_at_list (fun s₀ => valsX s₀ ++ [BitVec.ofNat 64 (ck s₀), nb0 s₀])
    (fun _ s₀ h => WP.of_flat (c := NX pc (.seq (LD oN oNLen) (.block Precompute.check1))) (by cases pc <;> rfl)
      (xi_loadX h fun s t hP F X => ?_)) fun _ _ _ h h' => ?_
  · have k64 := hP.k64; have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    refine WP.seq (WP.mono (ld2_ok (A := s₀.gpr .a2) (L := ck s₀) X.scr hZ X.s6 (by decide) (by decide)
      (by rw [X.hdr hP (by decide)]; exact F.hN) (by rw [X.hdr hP (by decide)]; exact F.hNL))
      fun u ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
    refine WP.mono (VG.Proof.Bignum.RISCV64.check1_ok (nb := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀)) a7 a8 k64
      (VG.Proof.Bignum.bytesAt_length _ _ _) (by rw [k1.2.1, k1.2.2, X.rd]; exact hP.rN) fun i hi => ?_)
      fun v ⟨⟨_, v4, _⟩, k2⟩ => ?_
    · have hs := hP.sN i hi
      have hx : ¬ Mont.ofs (cS s₀) (Mont.off (s₀.gpr .a2) i) < cZ s₀ := fun hc => hs _ hc rfl
      rw [m1, X.out _ (Or.inr (by omega_arith)), F.mem _ (Or.inr (by omega_arith))]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    · have k12 := k1.trans k2
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v4, k2.gpr (r := .s8) (by decide), a8,
        k12.gpr (r := .a7) (by decide), k12.gpr (r := .ra) (by decide), k12.gpr (r := .s5) (by decide),
        k12.gpr (r := .s11) (by decide), k12.gpr (r := .t0) (by decide), k12.gpr (r := .s6) (by decide),
        X.a7, X.ra, X.s5, X.s11, X.t0, X.s6, nb0, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 0 < (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .a2) (ck s₀)).length by
          rw [VG.Proof.Bignum.bytesAt_length]; omega_arith), Option.getD_some]
  · obtain ⟨eS, ek, -, -, -, -, -, -, -, -, -, -, en⟩ := data_vals h h'
    rw [valsX_eq h h']; simp only [nb0]; rw [en, ek]

end VG.Proof.Bignum.RISCV64.Crt
