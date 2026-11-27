module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtArgs

/-! ### `Bignum.PPC64LE.CrtCTBase`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: constant time, the front

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. Two runs are related by `Two` (`MontCT.lean`)
for the same public data. The taint analysis keeps memory secret, so the
working space's address, from the stack, is pinned once loaded (`L1`), and
the front (`front_rel`) ends with `Front`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

variable {pc : Bool}

/-- The argument registers of `vg_rsa_private_crt`, and with `pc`, of
`vg_rsa_private_crt_precomputed`: `r31` too. -/
abbrev argRegsG (pc : Bool) : List Reg := if pc then argRegs ++ [.r31] else argRegs

/-- The public data of a run. -/
def dataOf (pc : Bool) (s : State) : List (BitVec 64) × List (BitVec 64) × List Byte :=
  ((argRegsG pc).map s.gpr, (List.range 10).map (stackArg s),
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)

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
  · exact preCore_nil h
  · exact h.1

/-- On entry. -/
def C0 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  preG pc s ∧ dataOf pc s = d

/-- What the public data fixes. -/
structure DataEq (pc : Bool) (s₀ s₀' : State) : Prop where
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  r4 : s₀.gpr .r4 = s₀'.gpr .r4
  r5 : s₀.gpr .r5 = s₀'.gpr .r5
  r6 : s₀.gpr .r6 = s₀'.gpr .r6
  r7 : s₀.gpr .r7 = s₀'.gpr .r7
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  r10 : s₀.gpr .r10 = s₀'.gpr .r10
  r31 : pc = true → s₀.gpr .r31 = s₀'.gpr .r31
  sa : ∀ i < 10, stackArg s₀ i = stackArg s₀' i
  nb : Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat =
    Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .r5) (s₀'.gpr .r6).toNat

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

theorem pins_C0 : Pins (C0 pc) [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

/-- After loading the working space's address. -/
def L1 (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  ∃ s₀, C0 pc d s₀ ∧ s.gpr .r11 = stackArg s₀ 8 ∧ Keep [.r11] s₀ s

theorem pins_L1 : Pins (L1 pc) [.r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a11, k⟩ ⟨s₀', h₀', b11, k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a11, b11, E.sa 8 (by decide)]
  all_goals rw [k.gpr _ (by decide), k'.gpr _ (by decide)]
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

/-- After the front. -/
def LF (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) : Prop :=
  ∃ s₀, C0 pc d s₀ ∧ Front s₀ s

theorem loadS_L1 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s : State} (h : C0 pc d s) :
    WP isa (.block [.addSp .r11 160, .load .d .r11 .r11 0]) s (L1 pc d) := by
  have hp := preG_core h.1
  refine WP.mono (loadS_ok s ⟨⟨stackArgAddr s 0, 80⟩,
    List.mem_append_left _ (by rw [hp.2.1]; exact List.mem_append_left _ (by simp [baseRd])), ?_⟩)
    fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨s, h, a11, k⟩
  show Region.Contains _ (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 8))) 8
  rw [show s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 8)) = (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0))) +
    BitVec.ofNat 64 64 by rw [BitVec.add_assoc]; rfl]
  exact Offset.contains_base _ (by omega_using []) (by omega_using [])

theorem front_rel : RelCT isa (Two (C0 pc)) (.block (Crt.save ++ argsG pc ++ setupX)) (Two (LF pc)) := by
  refine two_post ?_ fun _ _ h => WP.mono (front_okG pc _ (preG_core h.1)) fun t ht => ⟨_, h, ht.1⟩
  unfold Crt.save
  simp only [List.append_assoc]
  cases pc
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide)))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
      (two_taint _ pins_L1 (by taint_decide)))

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-! ### `Bignum.PPC64LE.CrtPinsA`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: the registers at the cuts of `loadX`

The code's list of programs (`crtF`) is cut after each block that loads a
buffer's address and length from the header, and after `n`'s first byte
(`check1`): the registers there, from the initial state (`pins*`). In
`loadX`, `XI` is what a buffer's load needs: the registers of `X` and the
header as the front left it.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

variable {pc : Bool}

/-- The code's list of programs. -/
abbrev crtF (pc : Bool) : List (Prog isa) := Code.flat (crtG pc)

/-- In `loadX`, after the front left `s`. -/
structure XI (s₀ s t : State) : Prop where
  scr : Scr t (cS s₀) (cZ s₀)
  r23 : t.gpr .r23 = cS s₀
  r10 : t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : t.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : t.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem
  rd : t.rd ++ t.wr = s₀.rd ++ s₀.wr

theorem xi_front {s₀ s : State} (F : Front s₀ s) : XI s₀ s s :=
  ⟨F.scr, F.r23, F.r10, F.r21, F.r29, F.r11, F.r27, F.r28, Outside.refl _ _ _ _, by rw [F.keep.rd, F.keep.wr]⟩

theorem XI.hdr {s₀ s t : State} (hP : PF s₀) (X : XI s₀ s t) {d : Nat} (hd : d + 8 ≤ 256) :
    word t.mem (cS s₀) d = word s.mem (cS s₀) d := by
  have hn := hP.nw; have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  exact X.out.word (Or.inl hd) (by omega_arith)

/-- `XI` through code that keeps the registers and changes only the arrays. -/
theorem XI.step {s₀ s t u : State} (hP : PF s₀) (X : XI s₀ s t) {rs : List Reg} (k : Keep rs t u)
    (h : ∀ r ∈ [Reg.r23, .r21, .r29, .r11, .r27, .r28], r ∉ rs)
    (h10 : u.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0))
    (o : Outside (cS s₀) 256 (slot (cwX s₀) 8 - 256) t.mem u.mem) : XI s₀ s u := by
  have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨X.scr.congr k.wr, (k.gpr _ h.1).trans X.r23, h10, (k.gpr _ h.2.1).trans X.r21,
    (k.gpr _ h.2.2.1).trans X.r29, (k.gpr _ h.2.2.2.1).trans X.r11, (k.gpr _ h.2.2.2.2.1).trans X.r27,
    (k.gpr _ h.2.2.2.2.2).trans X.r28, X.out.trans (o.mono (Nat.le_refl _) (by omega_arith)),
    by rw [k.rd, k.wr]; exact X.rd⟩

/-- `r14 := r10`, then `X`'s array 0 := all ones. -/
theorem xi_ones {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (X : XI s₀ s t)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c)) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e0 : slot (cwX s₀) 0 = 256 + 0 * (8 * (cwX s₀ + 2)) := rfl
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun u => u.gpr .r14 = off (cS s₀) (slot (cwX s₀) 0) ∧
    u.mem = t.mem) (by prun [X.r10, BitVec.add_zero]) (by decide)) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (onesWords_ok (X.scr.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans X.r11) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₂ ⟨⟨_, o2⟩, k2⟩ => hc t₂ ?_)
  rw [m1] at o2
  exact XI.step hP X (k1.trans k2) (by decide) (((k1.trans k2).gpr _ (by decide)).trans X.r10)
    (o2.mono (by omega_arith) (by omega_arith))

/-- A buffer's address and length from the header's words `oA`, `oL`. -/
theorem ld2_ok {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) t fun u =>
      (u.gpr .r12 = off A 0 ∧ u.gpr .r6 = BitVec.ofNat 64 L ∧ u.mem = t.mem) ∧ Keep [.r12, .r6] t u := by
  have room := hP.room
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have hA' : t.mem.readW (off (cS s₀) oA) 64 = off A 0 := by rw [← hA]; exact X.hdr hP hoA.1
  have hL' : t.mem.readW (off (cS s₀) oL) 64 = BitVec.ofNat 64 L := by rw [← hLw]; exact X.hdr hP hoL.1
  refine WP.keep _ ?_ rfl
  prun [X.r23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oA < 2 ^ 15 by omega_arith, show oA % 4 = 0 by omega_arith⟩,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oL < 2 ^ 15 by omega_arith, show oL % 4 = 0 by omega_arith⟩,
    X.scr.ld (show oA + 8 ≤ cZ s₀ by omega_arith), X.scr.ld (show oL + 8 ≤ cZ s₀ by omega_arith), hA', hL']

/-- A buffer into `X`'s array `j`. -/
theorem xi_load {s₀ s t : State} {c : Prog isa} {Q : State → Prop} {j oA oL : Nat} {A : Addr} {L : Nat}
    (hP : PF s₀) (X : XI s₀ s t) (hj : j < 8)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLk : L ≤ ck s₀) (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (off A i) 1)
    (hsep : ∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x)
    (hc : ∀ u, XI s₀ s u → WP isa c u Q) :
    WP isa (.seq (.seq (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) (loadArr j)) c) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (loadOne_ok X.scr (by omega_arith) hj (by omega_arith) X.r23 X.r10 X.r21 X.r29 X.r11 hoA hoL
    (by rw [X.hdr hP hoA.1]; exact hA) (by rw [X.hdr hP hoL.1]; exact hLw) hL (by omega_arith)
    (by rw [X.rd]; exact hrd) hsep) fun u ⟨⟨_, _, o, u10⟩, k⟩ => hc u ?_)
  have := slot_le (w := cwX s₀) hj
  have h256 : 256 ≤ slot (cwX s₀) j := Nat.le_add_right _ _
  exact XI.step hP X k (by decide) u10 (o.mono (by omega_arith) (by omega_arith))

/-- The registers after a buffer's address and length. -/
theorem xi_ld {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word s.mem (cS s₀) oA = off A 0) (hLw : word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) t fun u =>
      [Reg.r6, .r10, .r11, .r12, .r21, .r23, .r29].map u.gpr =
        [BitVec.ofNat 64 L, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), off A 0,
          off (cS s₀) (slot (cwX s₀) 0), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))] :=
  WP.mono (ld2_ok hP X hoA hoL hA hLw) fun u ⟨⟨a12, a6, _⟩, k⟩ => by
    simp only [List.map_cons, List.map_nil, a12, a6, k.gpr .r10 (by decide), k.gpr .r11 (by decide),
      k.gpr .r21 (by decide), k.gpr .r23 (by decide), k.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r29]

/-- What two initial states with the same public data share. -/
theorem data_vals {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') :
    cS s₀ = cS s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' ∧ s₀.gpr .r3 = s₀'.gpr .r3 ∧
      s₀.gpr .r5 = s₀'.gpr .r5 ∧ s₀.gpr .r7 = s₀'.gpr .r7 ∧ s₀.gpr .r9 = s₀'.gpr .r9 ∧
      stackArg s₀ 0 = stackArg s₀' 0 ∧ stackArg s₀ 2 = stackArg s₀' 2 ∧ stackArg s₀ 4 = stackArg s₀' 4 ∧
      stackArg s₀ 6 = stackArg s₀' 6 ∧
      Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀) = Spec.Rsa.bytesAt s₀'.mem (s₀'.gpr .r5) (ck s₀') := by
  have E := two_data h h'
  exact ⟨E.sa 8 (by decide), by simp only [ck, E.r6], by simp only [cpL, E.r10], by show (stackArg s₀ 1).toNat = (stackArg s₀' 1).toNat; rw [E.sa 1 (by decide)],
    E.r3, E.r5, E.r7, E.r9, E.sa 0 (by decide), E.sa 2 (by decide), E.sa 4 (by decide), E.sa 6 (by decide), E.nb⟩

/-- The registers at the cut after a buffer's address and length. -/
abbrev ldVals (s₀ : State) (A : Addr) (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 L, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), off A 0,
    off (cS s₀) (slot (cwX s₀) 0), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))]

theorem pins1 : Pins (At (C0 pc) (crtF pc) 1) [.r10, .r11, .r23] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), cS s₀])
    (fun _ s₀ h => WP.of_flat (c := .block (Crt.save ++ argsG pc ++ setupX)) rfl
      (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, _⟩ => by simp only [List.map_cons, List.map_nil, F.r10, F.r11, F.r23]))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [cwX, eS, ek]

/-- A buffer's address and length, as a block. -/
abbrev LD (oA oL : Nat) : Prog isa := .block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]

/-- The front, then `X`'s array 0 := all ones, then `c`. -/
abbrev N0 (pc : Bool) (c : Prog isa) : Prog isa :=
  .seq (.block (Crt.save ++ argsG pc ++ setupX)) (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c))

/-- A buffer into array `j`, then `c`. -/
abbrev LJ (j oA oL : Nat) (c : Prog isa) : Prog isa := .seq (.seq (LD oA oL) (loadArr j)) c

theorem xi_start {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀) (hc : ∀ s t, PF s₀ → Front s₀ s → XI s₀ s t → WP isa c t Q) :
    WP isa (N0 pc c) s₀ Q :=
  WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, _⟩ => xi_ones (pre_factsG (preG_core h.1)) (xi_front F) fun t X =>
    hc s t (pre_factsG (preG_core h.1)) F X)

theorem ldVals_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') {A A' : Addr} {L L' : Nat} (hA : A = A') (hL : L = L') :
    ldVals s₀ A L = ldVals s₀' A' L' := by
  obtain ⟨eS, ek, -⟩ := data_vals h h'
  simp only [ldVals, cwX, eS, ek, hA, hL]

theorem pins5 : Pins (At (C0 pc) (crtF pc) 5) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r5) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LD oN oNLen)) rfl (xi_start h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) F.hN F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.1 E.2.1

theorem pins13 : Pins (At (C0 pc) (crtF pc) 13) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r9) (cpL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LD oP oPLen))) rfl (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hP F.hPL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.1 E.2.2.1

theorem pins21 : Pins (At (C0 pc) (crtF pc) 21) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (stackArg s₀ 0) (cqL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LD oQ oQLen)))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hQ F.hQL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.2.1 E.2.2.2.1

theorem pins29 : Pins (At (C0 pc) (crtF pc) 29) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r7) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LD oIn oNLen))))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) F.hN F.hNL (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) F.hP F.hPL hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_load (j := 5) hP X (by decide) (by decide) (by decide) F.hQ F.hQL hP.q1 (Nat.le_of_lt hP.qk)
        hP.rQ hP.sQ fun _ X =>
      xi_ld hP X (by decide) (by decide) F.hIn F.hNL))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.1 E.2.1

theorem pins37 : Pins (At (C0 pc) (crtF pc) 37) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (stackArg s₀ 6) (cpL s₀))
    (fun _ s₀ h => WP.of_flat
      (c := N0 pc (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen (LJ 6 oIn oNLen (LD oQInv oPLen)))))) rfl
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
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.2.2.2.2.1 E.2.2.1

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

theorem pins45 : Pins (At (C0 pc) (crtF pc) 45) [.r6, .r12] :=
  pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (s₀.gpr .r5) 0])
    (fun _ s₀ h => WP.of_flat (c := NX pc (LD oN oNLen)) rfl (xi_loadX h fun _ _ hP F X =>
      WP.mono (ld2_ok hP X (by decide) (by decide) F.hN F.hNL) fun u ⟨⟨a12, a6, _⟩, _⟩ => by
        simp only [List.map_cons, List.map_nil, a12, a6]))
    fun _ _ _ h h' => by
      obtain ⟨-, ek, -, -, -, e5, -⟩ := data_vals h h'
      rw [ek, e5]

/-- `n`'s first byte. -/
abbrev nb0 (s₀ : State) : BitVec 64 :=
  BitVec.ofNat 64 ((Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)).getD 0 0).toNat

theorem pins46 : Pins (At (C0 pc) (crtF pc) 46) [.r6, .r10, .r11, .r15, .r21, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (2 * cwX s₀), nb0 s₀, off (cS s₀) (slot (cwX s₀) 0), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NX pc (.seq (LD oN oNLen) (.block Precompute.check1))) rfl (xi_loadX h fun s t hP F X => ?_))
    fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have k64 := hP.k64
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine WP.seq (WP.mono (ld2_ok hP X (by decide) (by decide) F.hN F.hNL) fun u ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
    refine WP.mono (VG.Proof.Bignum.PPC64LE.check1_ok (nb := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀)) a12 a6 k64
      (VG.Proof.Bignum.bytesAt_length _ _ _) (by rw [k1.rd, k1.wr, X.rd]; exact hP.rN) fun i hi => ?_)
      fun v ⟨⟨_, v15, _, _⟩, k2⟩ => ?_
    · have hs := hP.sN i hi
      have hx : ¬ ofs (cS s₀) (Mont.off (s₀.gpr .r5) i) < cZ s₀ := fun hc => hs _ hc rfl
      rw [m1, X.out _ (Or.inr (by omega_arith)), F.mem _ (Or.inr (by omega_arith))]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    · have k12 := k1.trans k2
      simp only [List.map_cons, List.map_nil, v15, k2.gpr .r6 (by decide), a6, k12.gpr .r10 (by decide),
        k12.gpr .r11 (by decide), k12.gpr .r21 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide),
        k12.gpr .r28 (by decide), k12.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r27, X.r28, X.r29,
        nb0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (Spec.Rsa.bytesAt s₀.mem
          (s₀.gpr .r5) (ck s₀)).length by rw [VG.Proof.Bignum.bytesAt_length]; omega_arith), Option.getD_some]
  · obtain ⟨eS, ek, -, -, -, -, -, -, -, -, -, -, en⟩ := data_vals h h'
    simp only [nb0, cwX]; rw [en, eS, ek]

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: the registers at the later cuts

After `checks`, the cuts are after the blocks that start a power, `m₂`'s
export, `recombineP` and each half of `recombineX`, and the output: their
registers, from the initial state (`pins*`), through the correctness proof's
phases (`mid1A_ok`, `mid1B_ok`, `mid1_ok`, `mid2A_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

variable {pc : Bool}

/-- A power's first block. -/
abbrev PW1 (xj : Nat) : List Instr := [.load .d .r25 .r23 oNLen, .addi .r14 .r10 0] ++ xb .r15 xj

/-- `setupP` and a power's first block: the registers. -/
theorem pw1_ok {t : State} {BX : Addr} {Z oA wX xj k L oB oLen : Nat} (hs : Scr t BX Z) (hZ : 256 ≤ Z)
    (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : word t.mem BX oB = off BX oA) (hLw : word t.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word t.mem BX oNLen = BitVec.ofNat 64 k) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) :
    WP isa (.seq (.block (setupP oB oLen)) (.block (PW1 xj))) t fun u =>
      [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29].map u.gpr =
        [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
          off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
          BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] := by
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL hZ hB hLw hL hL') fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  obtain hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by rw [m1]; exact hK
  obtain hs1 := hs.congr k1.wr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 k ∧
    u.gpr .r14 = off BX (oA + slot (wsWords L) 0) ∧ u.mem = s₁.mem) (by
      prun [(k1.gpr _ (by decide)).trans h23, a10, oNLen, hs1.ld (show 16 + 8 ≤ Z by omega_arith), hK',
        BitVec.add_zero, off_off]) rfl) fun s₂ ⟨⟨a25, a14, _⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) xj) fun u ⟨⟨a15, _⟩, k3⟩ => ?_
  simp only [List.map_cons, List.map_nil, a15, k3.gpr .r10 (by decide), k3.gpr .r11 (by decide),
    k3.gpr .r14 (by decide), k3.gpr .r21 (by decide), k3.gpr .r23 (by decide), k3.gpr .r25 (by decide),
    k3.gpr .r27 (by decide), k3.gpr .r28 (by decide), k3.gpr .r29 (by decide), k2.gpr .r10 (by decide),
    k2.gpr .r11 (by decide), k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r27 (by decide),
    k2.gpr .r28 (by decide), k2.gpr .r29 (by decide), k1.gpr .r23 (by decide), k1.gpr .r27 (by decide),
    k1.gpr .r28 (by decide), a10, a11, a14, a21, a25, a29, h23, h27, h28]

/-- The registers a power's first block leaves public: with `pc`, `r30` too. -/
abbrev pwRegs (pc : Bool) : List Reg :=
  [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29] ++ if pc then [.r30] else []

/-- `setupP` and a power's first block with `r2Ptr pc q`: the registers. -/
theorem pw1G_ok {pc q : Bool} {t : State} {BX : Addr} {Z oA wX xj k L oB oLen pL : Nat} (hs : Scr t BX Z)
    (hZ : 256 ≤ Z) (h23 : t.gpr .r23 = BX) (h27 : t.gpr .r27 = off BX (slot wX 0))
    (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : word t.mem BX oB = off BX oA) (hLw : word t.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word t.mem BX oNLen = BitVec.ofNat 64 k) (hL : 1 ≤ L) (hL' : L < 2 ^ 60)
    (hpl : q = true → word t.mem BX oPLen = BitVec.ofNat 64 pL) (hp1 : 1 ≤ pL) (hp2 : pL < 2 ^ 60) :
    WP isa (.seq (.block (setupP oB oLen)) (.block (PW1 xj ++ r2Ptr pc q))) t fun u =>
      (pwRegs pc).map u.gpr =
        [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
          off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
          BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] ++
        if pc then [word t.mem BX oR2 + BitVec.ofNat 64 (if q then 8 * wsWords pL else 0)] else [] := by
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL hZ hB hLw hL hL') fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  obtain hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by rw [m1]; exact hK
  obtain hs1 := hs.congr k1.wr
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r25, .r14] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 k ∧
    u.gpr .r14 = off BX (oA + slot (wsWords L) 0) ∧ u.mem = s₁.mem) (by
      prun [(k1.gpr _ (by decide)).trans h23, a10, oNLen, hs1.ld (show 16 + 8 ≤ Z by omega_arith), hK',
        BitVec.add_zero, off_off]) rfl) fun s₂ ⟨⟨a25, a14, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) xj) fun u' ⟨⟨a15, m3⟩, k3⟩ => ?_
  obtain hu' : [Reg.r10, .r11, .r14, .r15, .r21, .r23, .r25, .r27, .r28, .r29].map u'.gpr =
      [off (off BX oA) (slot (wsWords L) 0), BitVec.ofNat 64 (2 * wsWords L), off BX (oA + slot (wsWords L) 0),
        off BX (slot wX xj), off (off BX oA) (slot (wsWords L) 0), BX, BitVec.ofNat 64 k, off BX (slot wX 0),
        BitVec.ofNat 64 (8 * (wX + 2)), BitVec.ofNat 64 (8 * (wsWords L + 2))] := by
    simp only [List.map_cons, List.map_nil, a15, k3.gpr .r10 (by decide), k3.gpr .r11 (by decide),
      k3.gpr .r14 (by decide), k3.gpr .r21 (by decide), k3.gpr .r23 (by decide), k3.gpr .r25 (by decide),
      k3.gpr .r27 (by decide), k3.gpr .r28 (by decide), k3.gpr .r29 (by decide), k2.gpr .r10 (by decide),
      k2.gpr .r11 (by decide), k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r27 (by decide),
      k2.gpr .r28 (by decide), k2.gpr .r29 (by decide), k1.gpr .r23 (by decide), k1.gpr .r27 (by decide),
      k1.gpr .r28 (by decide), a10, a11, a14, a21, a25, a29, h23, h27, h28]
  cases pc
  · exact WP.block_nil_iff.mpr (by simpa only [pwRegs, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hu')
  · have m' : u'.mem = t.mem := by rw [m3, m2, m1]
    obtain k' := k12.trans k3
    refine WP.mono (r2Src_ok (hs.congr k'.wr) hZ ((k'.gpr _ (by decide)).trans h23)
      (fun hq => by rw [m']; exact hpl hq) hp1 hp2) fun u ⟨⟨a30, _⟩, k4⟩ => ?_
    simp only [pwRegs, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, a30, m']
    rw [← hu']
    congr 1
    simp only [List.map_cons, List.map_nil, k4.gpr .r10 (by decide), k4.gpr .r11 (by decide),
      k4.gpr .r14 (by decide), k4.gpr .r15 (by decide), k4.gpr .r21 (by decide), k4.gpr .r23 (by decide),
      k4.gpr .r25 (by decide), k4.gpr .r27 (by decide), k4.gpr .r28 (by decide), k4.gpr .r29 (by decide)]

/-- Two header words into `ra` and `rb`, for `r12` and `r6` or `r30` and `r31`. -/
theorem hdr2_ok {t : State} {BX : Addr} {Z oA oB : Nat} {va vb : BitVec 64} (hs : Scr t BX Z) (hZ : 256 ≤ Z)
    (h23 : t.gpr .r23 = BX) (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0)
    (hA : word t.mem BX oA = va) (hB : word t.mem BX oB = vb) :
    (WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oB]) t fun u =>
      (u.gpr .r12 = va ∧ u.gpr .r6 = vb ∧ u.mem = t.mem) ∧ Keep [.r12, .r6] t u) ∧
    (WP isa (.block [.load .d .r30 .r23 oA, .load .d .r31 .r23 oB]) t fun u =>
      (u.gpr .r30 = va ∧ u.gpr .r31 = vb ∧ u.mem = t.mem) ∧ Keep [.r30, .r31] t u) := by
  have hA' : t.mem.readW (off BX oA) 64 = va := hA
  have hB' : t.mem.readW (off BX oB) 64 = vb := hB
  refine ⟨WP.keep _ ?_ rfl, WP.keep _ ?_ rfl⟩ <;>
  prun [h23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oA < 2 ^ 15 by omega_arith, show oA % 4 = 0 by omega_arith⟩,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oB < 2 ^ 15 by omega_arith, show oB % 4 = 0 by omega_arith⟩,
    hs.ld (show oA + 8 ≤ Z by omega_arith), hs.ld (show oB + 8 ≤ Z by omega_arith), hA', hB']

/-- What two initial states with the same public data share, of the layout. -/
theorem layout_eq {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s₀' : State} (h : C0 pc d s₀)
    (h' : C0 pc d s₀') :
    cS s₀ = cS s₀' ∧ cwX s₀ = cwX s₀' ∧ cwP s₀ = cwP s₀' ∧ cwQ s₀ = cwQ s₀' ∧ oPa s₀ = oPa s₀' ∧
      oQa s₀ = oQa s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' := by
  obtain ⟨eS, ek, ep, eq, -⟩ := data_vals h h'
  simp only [cwX, cwP, cwQ, oPa, oQa, eS, ek, ep, eq, and_self]

/-- The cut index of `crt` (`a`), or with `pc` of `crtP` (`b`). -/
abbrev ix (pc : Bool) (a b : Nat) : Nat := if pc then b else a

/-- With `pc`, the cached values (`R2F`) and the header's word of their address. -/
theorem c0_r2 {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ s : State} (h : C0 pc d s₀)
    (hhd : pc = true → word s.mem (cS s₀) oR2 = s₀.gpr .r31) :
    pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r31 := fun hp => by
  subst hp; exact ⟨r2F_of h.1, hhd rfl⟩

/-- The front, `loadX` and `checks`, then `c`. -/
abbrev NA (pc : Bool) (c : Prog isa) : Prog isa := .seq (.block (Crt.save ++ argsG pc ++ setupX)) (.seq loadX (.seq checks c))

/-- Then `loadIn`. -/
abbrev NL (pc : Bool) (c : Prog isa) : Prog isa := NA pc (.seq loadIn c)

theorem pins91 : Pins (At (C0 pc) (crtF pc) 91) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r7) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := NA pc (LD oIn oNLen)) (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => by
        obtain hP := pre_factsG (preG_core h.1)
        obtain hn := hP.nw; have room := hP.room
        have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
        refine mid1A_ok hP F fun t X a10 k1 => ?_
        obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
          X.out.word (Or.inl hd) (by omega_arith)
        refine WP.mono (hdr2_ok (va := off (s₀.gpr .r7) 0) (vb := BitVec.ofNat 64 (ck s₀)) (F.scr.congr k1.wr) (by omega_arith) ((k1.gpr _ (by decide)).trans F.r23)
          (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hIn) (by rw [hd _ (by decide)]; exact F.hNL)).1
          fun u ⟨⟨a12, a6, _⟩, k2⟩ => ?_
        simp only [ldVals, List.map_cons, List.map_nil, a12, a6, k2.gpr .r10 (by decide), k2.gpr .r11 (by decide),
          k2.gpr .r21 (by decide), k2.gpr .r23 (by decide), k2.gpr .r29 (by decide), a10,
          (k1.gpr .r11 (by decide)).trans F.r11, (k1.gpr .r21 (by decide)).trans F.r21,
          (k1.gpr .r23 (by decide)).trans F.r23, (k1.gpr .r29 (by decide)).trans F.r29])))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.1 E.2.1

/-- A power's head, then `c`. -/
abbrev PH (pc q : Bool) (xj : Nat) (c : Prog isa) : Prog isa :=
  .seq (.block (PW1 xj ++ r2Ptr pc q)) (.seq copyN (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++
    PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3)) (.seq (r2Step pc) (.seq reduceIn c))))

theorem pins100 : Pins (At (C0 pc) (crtF pc) 100) (pwRegs pc) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (cS s₀) (oPa s₀ + slot (cwP s₀) 0), off (cS s₀) (slot (cwX s₀) 4),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2))] ++
      if pc then [s₀.gpr .r31] else [])
    (fun _ s₀ h => WP.of_flat (c := NL pc (.seq (.block (setupP oBP oPLen)) (.block (PW1 4 ++ r2Ptr pc false))))
      (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t X _ k1 => ?_
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      X.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (pw1G_ok (pc := pc) (q := false) (pL := 1) (F.scr.congr k1.wr) (by omega_arith)
      ((k1.gpr _ (by decide)).trans F.r23)
      ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL)
      (by rw [hd _ (by decide)]; exact F.hNL) p1 (by omega_arith) nofun (Nat.le_refl _) (by decide)) fun u hu => ?_
    rw [hu]
    cases pc
    · rfl
    · rw [hd oR2 (by unfold oR2; omega_arith), hhd rfl]
      simp only [↓reduceIte, Bool.false_eq_true, BitVec.add_zero]
  · obtain ⟨eS, eX, eP, -, eoP, -, ek, -, -⟩ := layout_eq h h'
    obtain E := two_data h h'
    cases pc
    · simp only [eS, eX, eP, eoP, ek, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eoP, ek, E.r31 rfl, ↓reduceIte]

/-- The front through `p`'s power head and its exponent's registers. -/
theorem pins124 : Pins (At (C0 pc) (crtF pc) (ix pc 124 118)) [.r10, .r11, .r23, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwP s₀ + 2)), off (stackArg s₀ 2) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NL pc (.seq (.block (setupP oBP oPLen))
      (PH pc false 4 (.block [.load .d .r30 .r23 oDP, .load .d .r31 .r23 oPLen])))) (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have pq := hP.pq
    obtain k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk
    obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    obtain eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24; have fP8 := e (wsWords (cpL s₀)) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    obtain hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
    obtain ⟨_, mPo, _, _, mPb, _, _, _, _⟩ := masked_facts hP
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t X _ k1 => ?_
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      X.out.word (Or.inl hd) (by omega_arith)
    refine phasePA_ok (q := false) (hR2 := fun hp => by
      subst hp; exact ⟨_, _, _, (c0_r2 h hhd rfl).1.p hP F (c0_r2 h hhd rfl).2 X.out
        (by rw [k1.rd, k1.wr, F.keep.rd, F.keep.wr]) X.r26⟩) (wX := cwX s₀) (xj := 4) (oA := oPa s₀) (L := cpL s₀) (k := ck s₀) (Pv := mP s₀) (Cv := vC s₀)
      (F.scr.congr k1.wr) (by omega_arith) (Nat.le_refl _) rfl (by unfold wsWords; omega_arith) hwX (by decide)
      ((k1.gpr _ (by decide)).trans F.r23) ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28)
      (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL)
      (by rw [hd _ (by decide)]; exact F.hNL) p1 (by omega_arith) (by omega_arith) (by omega_arith)
      X.v4 mPb (by have := (masked_facts hP).1; omega_arith) mPo X.v6
      (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) fun u out u10 u11 _ u29 ku => ?_
    obtain hdu : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.mono (hdr2_ok (va := off (stackArg s₀ 2) 0) (vb := BitVec.ofNat 64 (cpL s₀)) ((F.scr.congr k1.wr).congr ku.wr) (by omega_arith)
      ((ku.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans F.r23)) (by decide) (by decide)
      (by rw [hdu _ (by decide)]; exact F.hDP) (by rw [hdu _ (by decide)]; exact F.hPL)).2
      fun v ⟨⟨v30, v31, _⟩, kv⟩ => ?_
    simp only [List.map_cons, List.map_nil, v30, v31, kv.gpr .r10 (by decide), kv.gpr .r11 (by decide),
      kv.gpr .r23 (by decide), kv.gpr .r29 (by decide), u10, u11, u29, ku.gpr .r23 (by decide),
      (k1.gpr .r23 (by decide)).trans F.r23]
  · obtain ⟨eS, -, eP, -, eoP, -, -, ep, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, -, -, -, e2, -⟩ := data_vals h h'
    simp only [eS, eP, eoP, ep, e2]

/-- The phases through `p`'s power, then `c`. -/
abbrev NP (pc : Bool) (c : Prog isa) : Prog isa :=
  NL pc (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen) c))

theorem pins129 : Pins (At (C0 pc) (crtF pc) (ix pc 129 123)) (pwRegs pc) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), BitVec.ofNat 64 (2 * cwQ s₀),
      off (cS s₀) (oQa s₀ + slot (cwQ s₀) 0), off (cS s₀) (slot (cwX s₀) 5),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), cS s₀, BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwQ s₀ + 2))] ++
      if pc then [s₀.gpr .r31 + BitVec.ofNat 64 (8 * cwP s₀)] else [])
    (fun _ s₀ h => WP.of_flat (c := NP pc (.seq (.block (setupP oBQ oQLen)) (.block (PW1 5 ++ r2Ptr pc true))))
      (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    obtain p1 := hP.p1; have pk := hP.pk
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t₁ X _ k1 => mid1B_ok hP F (c0_r2 h hhd) X k1 (by decide) (by decide) (by decide) fun t Y k2 => ?_
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      Y.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (pw1G_ok (pc := pc) (q := true) (pL := cpL s₀) (F.scr.congr k2.wr) (by omega_arith)
      ((k2.gpr _ (by decide)).trans F.r23)
      ((k2.gpr _ (by decide)).trans F.r27) ((k2.gpr _ (by decide)).trans F.r28) (by decide) (by decide)
      (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL)
      (by rw [hd _ (by decide)]; exact F.hNL) q1 (by omega_arith)
      (fun _ => by rw [hd oPLen (by unfold oPLen; omega_arith)]; exact F.hPL) p1 (by omega_arith)) fun u hu => ?_
    rw [hu]
    cases pc
    · rfl
    · rw [hd oR2 (by unfold oR2; omega_arith), hhd rfl]
      simp only [↓reduceIte]
  · obtain ⟨eS, eX, eP, eQ, -, eoQ, ek, -, -⟩ := layout_eq h h'
    obtain E := two_data h h'
    cases pc
    · simp only [eS, eX, eQ, eoQ, ek, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eQ, eoQ, ek, E.r31 rfl, ↓reduceIte]

theorem pins153 : Pins (At (C0 pc) (crtF pc) (ix pc 153 141)) [.r10, .r11, .r23, .r29, .r30, .r31] := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      BitVec.ofNat 64 (8 * (cwQ s₀ + 2)), off (stackArg s₀ 4) 0, BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := NP pc (.seq (.block (setupP oBQ oQLen))
      (PH pc true 5 (.block [.load .d .r30 .r23 oDQ, .load .d .r31 .r23 oQLen])))) (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have pq := hP.pq
    obtain k64 := hP.k64; have k1024 := hP.k1024; have q1 := hP.q1; have qk := hP.qk
    obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    obtain eX8 := e (cwX s₀) 8; have eQ8 := e (cwQ s₀) 24; have eP8 := e (cwP s₀) 24
    obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    obtain hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
    obtain ⟨_, _, _, mQo, _, mQb, _, _, _⟩ := masked_facts hP
    refine mid1A_ok hP F fun t₀ X₀ a10 k0 => mid1L_ok hP F X₀ a10 k0 (by decide) (by decide) (by decide)
      (by decide) fun t₁ X _ k1 => mid1B_ok hP F (c0_r2 h hhd) X k1 (by decide) (by decide) (by decide) fun t Y k2 => ?_
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      Y.out.word (Or.inl hd) (by omega_arith)
    refine phasePA_ok (q := true) (hR2 := fun hp => by
      subst hp; exact ⟨_, _, _, (c0_r2 h hhd rfl).1.q hP F (c0_r2 h hhd rfl).2 Y.out
        (by rw [k2.rd, k2.wr, F.keep.rd, F.keep.wr]) Y.r26⟩) (wX := cwX s₀) (xj := 5) (oA := oQa s₀) (L := cqL s₀) (k := ck s₀) (Pv := mQ s₀) (Cv := vC s₀)
      (F.scr.congr k2.wr) (by omega_arith) (by omega_arith) rfl (by unfold wsWords; omega_arith) hwX (by decide)
      ((k2.gpr _ (by decide)).trans F.r23) ((k2.gpr _ (by decide)).trans F.r27) ((k2.gpr _ (by decide)).trans F.r28)
      (by decide) (by decide) (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL)
      (by rw [hd _ (by decide)]; exact F.hNL) q1 (by omega_arith) (by omega_arith) (by omega_arith)
      Y.v5 mQb (by have := (masked_facts hP).2.2.1; omega_arith) mQo Y.v6
      (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) fun u out u10 u11 _ u29 ku => ?_
    obtain hdu : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.mono (hdr2_ok (va := off (stackArg s₀ 4) 0) (vb := BitVec.ofNat 64 (cqL s₀)) ((F.scr.congr k2.wr).congr ku.wr) (by omega_arith)
      ((ku.gpr _ (by decide)).trans ((k2.gpr _ (by decide)).trans F.r23)) (by decide) (by decide)
      (by rw [hdu _ (by decide)]; exact F.hDQ) (by rw [hdu _ (by decide)]; exact F.hQL)).2
      fun v ⟨⟨v30, v31, _⟩, kv⟩ => ?_
    simp only [List.map_cons, List.map_nil, v30, v31, kv.gpr .r10 (by decide), kv.gpr .r11 (by decide),
      kv.gpr .r23 (by decide), kv.gpr .r29 (by decide), u10, u11, u29, ku.gpr .r23 (by decide),
      (k2.gpr .r23 (by decide)).trans F.r23]
  · obtain ⟨eS, -, -, eQ, -, eoQ, -, -, eq⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, e4, -⟩ := data_vals h h'
    simp only [eS, eQ, eoQ, eq, e4]

/-- The phases through both powers, then `c`. -/
abbrev NQ (pc : Bool) (c : Prog isa) : Prog isa :=
  NP pc (.seq (.block (setupP oBQ oQLen)) (.seq (powerG pc true 5 oDQ oQLen) c))

/-- `m₂`'s export, its first block. -/
abbrev EX1 : List Instr :=
  setupP oBQ oQLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0] ++ xb .r14 6 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

theorem pins157 : Pins (At (C0 pc) (crtF pc) (ix pc 157 145)) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 6),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NQ pc (.block EX1)) (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    obtain hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    refine mid1_ok hP F (c0_r2 h hhd) fun t _ _ _ _ _ _ _ _ _ _ O1 k1 => ?_
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega_arith)
    obtain h23 := (k1.gpr _ (by decide)).trans F.r23
    obtain h27 := (k1.gpr _ (by decide)).trans F.r27
    obtain h28 := (k1.gpr _ (by decide)).trans F.r28
    refine WP.mono (blk_ok (j := 6) (oA := oQa s₀) _ (fun t h11 _ => midQ_ok h11) (F.scr.congr k1.wr) h23
      (by decide) (by decide) (by omega_arith) (by rw [hd _ (by decide)]; exact F.hBQ)
      (by rw [hd _ (by decide)]; exact F.hQL) q1 (by omega_arith) hwX h27 h28)
      fun v ⟨⟨b14, b11, b22, b15, _⟩, k3⟩ => ?_
    simp only [List.map_cons, List.map_nil, b14, b11, b22, b15, k3.gpr .r23 (by decide), k3.gpr .r27 (by decide),
      k3.gpr .r28 (by decide), h23, h27, h28]
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ]

/-- `m₂`'s export and `p`'s registers, then `c`. -/
abbrev NE (pc : Bool) (c : Prog isa) : Prog isa := NQ pc (.seq exportM2 (.seq (.block (setupP oBP oPLen)) c))

theorem pins164 : Pins (At (C0 pc) (crtF pc) (ix pc 164 152))
    (([.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r25] : List Reg) ++ if pc then [.r30] else []) := by
  refine pins_at_list (fun s₀ => [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2)), BitVec.ofNat 64 (ck s₀)] ++
      if pc then [s₀.gpr .r31] else [])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.block ([.load .d .r25 .r23 oNLen] ++ r2Ptr pc false)))
      (by cases pc <;> kernel_rfl)
      (WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ => ?_))) fun _ _ _ h h' => ?_
  · have hP := pre_factsG (preG_core h.1)
    obtain hn := hP.nw; have room := hP.room; have q1 := hP.q1; have qk := hP.qk; have k1024 := hP.k1024
    obtain p1 := hP.p1; have pk := hP.pk
    obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    obtain eX1 := e (cwX s₀) 1; have eX8 := e (cwX s₀) 8; have eQ8 := e (cwQ s₀) 24; have eP8 := e (cwP s₀) 24
    obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    obtain hwQ : cwQ s₀ ≤ cwX s₀ := by have := hP.pq; unfold cwQ; omega_arith
    obtain eX6 := e (cwX s₀) 6
    obtain hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    refine mid1_ok hP F (c0_r2 h hhd) fun t _ _ _ _ _ _ _ _ _ _ O1 k1 => ?_
    obtain hs := F.scr.congr k1.wr
    obtain h23 := (k1.gpr _ (by decide)).trans F.r23
    obtain hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      O1.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (exportM2_ok (oQ := oQa s₀) (qL := cqL s₀) hs (by omega_arith) (by omega_arith) hwQ hwX
      h23 ((k1.gpr _ (by decide)).trans F.r27) ((k1.gpr _ (by decide)).trans F.r28)
      (by rw [hd _ (by decide)]; exact F.hBQ) (by rw [hd _ (by decide)]; exact F.hQL) q1 (by omega_arith))
      fun u₁ ⟨⟨_, o1⟩, k2⟩ => ?_)
    obtain hd1 : ∀ d, d + 8 ≤ 256 → word u₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [o1.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    refine WP.seq (WP.mono (setupP_ok (oA := oPa s₀) (hs.congr k2.wr) ((k2.gpr _ (by decide)).trans h23) (by decide) (by decide)
      (by omega_arith) (by rw [hd1 _ (by decide)]; exact F.hBP) (by rw [hd1 _ (by decide)]; exact F.hPL) p1 (by omega_arith))
      fun u₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k3⟩ => ?_)
    obtain k23 := k2.trans k3
    obtain hK' : u₂.mem.readW (off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) := by
      rw [m2]; exact (hd1 16 (by decide)).trans F.hNL
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.r25] (Q := fun v => v.gpr .r25 = BitVec.ofNat 64 (ck s₀) ∧ v.mem = u₂.mem) (by
      prun [(k23.gpr .r23 (by decide)).trans h23, oNLen, ((hs.congr k2.wr).congr k3.wr).ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
        hK']) rfl) fun v' ⟨⟨a25, mv⟩, k4⟩ => ?_
    obtain hv' : [Reg.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r25].map v'.gpr =
        [off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), BitVec.ofNat 64 (2 * cwP s₀),
          off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0),
          BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwP s₀ + 2)), BitVec.ofNat 64 (ck s₀)] := by
      simp only [List.map_cons, List.map_nil, a25, k4.gpr .r10 (by decide), k4.gpr .r11 (by decide),
        k4.gpr .r21 (by decide), k4.gpr .r23 (by decide), k4.gpr .r27 (by decide), k4.gpr .r28 (by decide),
        k4.gpr .r29 (by decide), a10, a11, a21, a29, k23.gpr .r23 (by decide), k23.gpr .r27 (by decide),
        k23.gpr .r28 (by decide), h23, (k1.gpr _ (by decide)).trans F.r27, (k1.gpr _ (by decide)).trans F.r28]
    cases pc
    · exact WP.block_nil_iff.mpr (by simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil] using hv')
    · have k' := k23.trans k4
      refine WP.mono (r2Src_ok (q := false) (pL := 1) ((hs.congr k'.wr)) (by omega_arith)
        ((k'.gpr _ (by decide)).trans h23) nofun (Nat.le_refl _) (by decide)) fun v ⟨⟨a30, _⟩, k5⟩ => ?_
      simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, a30, mv, m2, Bool.false_eq_true,
        BitVec.add_zero]
      rw [hd1 oR2 (by unfold oR2; omega_arith), hhd rfl, ← hv']
      simp only [List.map_cons, List.map_nil, k5.gpr .r10 (by decide), k5.gpr .r11 (by decide),
        k5.gpr .r21 (by decide), k5.gpr .r23 (by decide), k5.gpr .r27 (by decide), k5.gpr .r28 (by decide),
        k5.gpr .r29 (by decide), k5.gpr .r25 (by decide)]
  · obtain ⟨eS, eX, eP, -, eoP, -, ek, -, -⟩ := layout_eq h h'
    obtain E := two_data h h'
    cases pc
    · simp only [eS, eX, eP, eoP, ek, Bool.false_eq_true, ↓reduceIte]
    · simp only [eS, eX, eP, eoP, ek, E.r31 rfl, ↓reduceIte]

/-- Through `recombineP`, from the initial state. -/
theorem pre_rec {d : List (BitVec 64) × List (BitVec 64) × List Byte} {s₀ : State} {c : Prog isa}
    {Q : State → Prop} (h : C0 pc d s₀)
    (hc : ∀ s u, PF s₀ → Front s₀ s → XR s₀ s u →
      Keep (mid1Regs ++ (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs)) s u → WP isa c u Q) :
    WP isa (NE pc (.seq (recombinePG pc) c)) s₀ Q :=
  WP.seq (WP.mono (front_okG pc s₀ (preG_core h.1)) fun s ⟨F, hhd⟩ =>
    mid1_ok (pre_factsG (preG_core h.1)) F (c0_r2 h hhd) fun _ t26 v0 w0 v5 v7 p0 p4 q4 _ _ O1 k1 =>
      mid2A_ok (pre_factsG (preG_core h.1)) F (c0_r2 h hhd) t26 v0 w0 v5 v7 p0 p4 q4 O1 k1 fun u R k => hc s u (pre_factsG (preG_core h.1)) F R k)

/-- `recombineX`'s first block. -/
abbrev X1 : List Instr :=
  setupP oBP oPLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0, .lsl .r11 .r4 1] ++ xb .r14 7 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

/-- `recombineX`'s second block. -/
abbrev X2 : List Instr :=
  setupP oBQ oQLen ++ PublicChecked.base .r15 4 ++ [.addi .r22 .r11 0] ++ xb .r14 6 ++
    [.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2]

theorem pins214 : Pins (At (C0 pc) (crtF pc) (ix pc 214 196)) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 7),
      off (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4), BitVec.ofNat 64 (2 * cwP s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.block X1))) (by cases pc <;> kernel_rfl)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    obtain hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega_arith)))
      (F.scr.congr k.wr) ((k.gpr _ (by decide)).trans F.r23) (by decide) (by decide) (by omega_arith)
      (by rw [hd _ (by decide)]; exact F.hBP) (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega_arith)
      (by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith) ((k.gpr _ (by decide)).trans F.r27) ((k.gpr _ (by decide)).trans F.r28))
      fun v ⟨⟨a14, a11, a22, a15, _⟩, k'⟩ => ?_
    simp only [List.map_cons, List.map_nil, a14, a11, a22, a15, k'.gpr .r23 (by decide), k'.gpr .r27 (by decide),
      k'.gpr .r28 (by decide), (k.gpr _ (by decide)).trans F.r23, (k.gpr _ (by decide)).trans F.r27,
      (k.gpr _ (by decide)).trans F.r28]
  · obtain ⟨eS, eX, eP, -, eoP, -, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eP, eoP]

theorem pins220 : Pins (At (C0 pc) (crtF pc) (ix pc 220 202)) [.r11, .r14, .r15, .r22, .r23, .r27, .r28] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (2 * cwX s₀), off (cS s₀) (slot (cwX s₀) 6),
      off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4), BitVec.ofNat 64 (2 * cwQ s₀), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.seq (.block X1) (.seq (.seq Precompute.zeroWords
      (.seq (.block (xb .r14 7 ++ [.addi .r11 .r22 0])) copyN)) (.block X2))))) (by cases pc <;> kernel_rfl)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    obtain q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    obtain eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24
    obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    obtain hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    obtain hwP : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
    obtain hs := F.scr.congr k.wr
    obtain h23 := (k.gpr _ (by decide)).trans F.r23
    obtain h27 := (k.gpr _ (by decide)).trans F.r27
    obtain h28 := (k.gpr _ (by decide)).trans F.r28
    obtain hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (blk_ok (j := 7) (oA := oPa s₀) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt (by omega_arith)))
      hs h23 (by decide) (by decide) (by omega_arith) (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) p1 (by omega_arith) hwX h27 h28)
      fun v₁ ⟨⟨a14, a11, a22, a15, m1⟩, k1⟩ => ?_)
    refine WP.seq (WP.mono (xfer_ok (hs.congr k1.wr) (show oPa s₀ + slot (cwP s₀) 24 ≤ cZ s₀ by omega_arith)
      (Nat.le_of_eq doP.symm) (by decide) (by omega_arith) (by omega_arith) hwX a14 a11 a22 a15
      ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28)) fun v₂ ⟨⟨_, out2⟩, k2⟩ => ?_)
    obtain k12 := k1.trans k2
    obtain hd2 : ∀ d, d + 8 ≤ 256 → word v₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [out2.word (Or.inl (by omega_arith)) (by omega_arith), m1]; exact hd d hd'
    refine WP.mono (blk_ok (j := 6) (oA := oQa s₀) _ (fun t h11 _ => midQ_ok h11) (hs.congr k12.wr)
      ((k12.gpr _ (by decide)).trans h23) (by decide) (by decide) (by omega_arith)
      (by rw [hd2 _ (by decide)]; exact F.hBQ) (by rw [hd2 _ (by decide)]; exact F.hQL) q1 (by omega_arith) hwX
      ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28))
      fun v ⟨⟨b14, b11, b22, b15, _⟩, k3⟩ => ?_
    simp only [List.map_cons, List.map_nil, b14, b11, b22, b15, k3.gpr .r23 (by decide), k3.gpr .r27 (by decide),
      k3.gpr .r28 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide), k12.gpr .r28 (by decide),
      h23, h27, h28]
  · obtain ⟨eS, eX, -, eQ, -, eoQ, -, -, -⟩ := layout_eq h h'
    simp only [eS, eX, eQ, eoQ]

/-- The output's registers. -/
abbrev FIN : List Instr := [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut, .load .d .r28 .r23 oNLen]

theorem pins233 : Pins (At (C0 pc) (crtF pc) (ix pc 233 215)) [.r10, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), cS s₀, off (s₀.gpr .r3) 0,
      BitVec.ofNat 64 (ck s₀), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NE pc (.seq (recombinePG pc) (.seq recombineX (.block FIN)))) (by cases pc <;> kernel_rfl)
      (pre_rec h fun s u hP F R k => ?_)) fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have p1 := hP.p1; have pk := hP.pk; have k1024 := hP.k1024
    obtain q1 := hP.q1; have qk := hP.qk; have pq := hP.pq
    obtain e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
    obtain eX2 := e (cwX s₀) 2; have eX8 := e (cwX s₀) 8; have eP8 := e (cwP s₀) 24
    obtain fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
    have dP : cwP s₀ = wsWords (cpL s₀) := rfl
    have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
    have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
    have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
    obtain hwX : cwX s₀ < 2 ^ 31 := by have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl; omega_arith
    obtain ⟨-, -, -, -, -, mQb, -⟩ := masked_facts hP
    obtain hs := F.scr.congr k.wr
    obtain h23 := (k.gpr _ (by decide)).trans F.r23
    obtain h27 := (k.gpr _ (by decide)).trans F.r27
    obtain h28 := (k.gpr _ (by decide)).trans F.r28
    obtain hd : ∀ d, d + 8 ≤ 256 → word u.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
      R.out.word (Or.inl hd) (by omega_arith)
    refine WP.seq (WP.mono (recombineX_ok (oP := oPa s₀) (oQ := oQa s₀) hs (by omega_arith) (Nat.le_of_eq doP.symm)
      (by omega_arith) (by omega_arith) pq hwX h23 h27 h28 (by rw [hd _ (by decide)]; exact F.hBP)
      (by rw [hd _ (by decide)]; exact F.hPL) (by rw [hd _ (by decide)]; exact F.hBQ)
      (by rw [hd _ (by decide)]; exact F.hQL) p1 (by omega_arith) q1 (by omega_arith) R.v0 R.w0 R.v5 mQb R.h4 R.q4)
      fun v₁ ⟨⟨_, o1⟩, k1⟩ => ?_)
    obtain O1 : Outside (cS s₀) (slot (cwX s₀) 2) (6 * (8 * (cwX s₀ + 2))) u.mem v₁.mem := by
      intro x hx
      refine o1 x fun r hr => ?_
      change ofs (cS s₀) x < r.1 ∨ r.1 + r.2 ≤ ofs (cS s₀) x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      change ofs (cS s₀) x < slot (cwX s₀) 2 ∨ slot (cwX s₀) 2 + 6 * (8 * (cwX s₀ + 2)) ≤ ofs (cS s₀) x at hx
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp only [e] at hx ⊢ <;> omega_arith
    obtain hd1 : ∀ d, d + 8 ≤ 256 → word v₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd' => by
      rw [O1.word (Or.inl (by omega_arith)) (by omega_arith)]; exact hd d hd'
    obtain hs1 := hs.congr k1.wr
    obtain e0 : off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
    obtain hO' : v₁.mem.readW (cS s₀) 64 = off (s₀.gpr .r3) 0 := by
      obtain h0 : word v₁.mem (cS s₀) 0 = off (s₀.gpr .r3) 0 := (hd1 0 (by decide)).trans F.hOut
      rw [← e0]; exact h0
    obtain ld0 : InRegions (v₁.rd ++ v₁.wr) (cS s₀) 8 := by
      obtain e0' : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
      have := hs1.ld (show 0 + 8 ≤ cZ s₀ by omega_arith); rwa [e0'] at this
    obtain hK' : v₁.mem.readW (off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) := by
      show word v₁.mem (cS s₀) 16 = _; rw [hd1 16 (by decide)]; exact F.hNL
    refine WP.mono (WP.keep [.r10, .r29, .r27, .r28] (Q := fun t =>
      t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) ∧
        t.gpr .r27 = off (s₀.gpr .r3) 0 ∧ t.gpr .r28 = BitVec.ofNat 64 (ck s₀)) (by
      prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28,
        (k1.gpr .r23 (by decide)).trans h23, oOut, oNLen, ld0, hs1.ld (show 16 + 8 ≤ cZ s₀ by omega_arith), hO', hK',
        BitVec.add_zero]) (by decide)) fun v ⟨⟨a10, a29, a27, a28⟩, k2⟩ => ?_
    simp only [List.map_cons, List.map_nil, a10, a29, a27, a28, k2.gpr .r23 (by decide), k1.gpr .r23 (by decide),
      h23]
  · obtain ⟨eS, eX, -, -, -, -, ek, -, -⟩ := layout_eq h h'
    obtain ⟨-, -, -, -, e3, -⟩ := data_vals h h'
    simp only [eS, eX, ek, e3]

end VG.Proof.Bignum.PPC64LE.Crt
