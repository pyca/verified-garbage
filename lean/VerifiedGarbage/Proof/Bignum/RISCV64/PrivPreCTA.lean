module
-- separate module: the precomputation's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreE
public import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsA
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPrePQ

/-!
# An RSA private key's precomputed values on RISC-V: the registers at the cuts of the checks

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. The code's list of programs (`privF`) is cut
after each block that loads values of the header, which the taint analysis
finds secret: the registers there, from the initial state (`pins*`). In
`loadX`, `XI` is what a buffer's load needs, as `vg_rsa_private_crt`'s
(`CrtPinsA.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero At pins_at_list)
open VG.Proof.Bignum.RISCV64.Pre (Pins)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf loadOne_ok onesWords_ok ld2_ok wp_nil wp_seqL_nil z0 savW)

/-- The public data of a run. -/
abbrev PDat : Type := List (BitVec 64) × List (BitVec 64) × List Byte

/-- The public data of a state on entry. -/
def dataOf (s : State) : PDat := (argRegs.map s.gpr, (List.range 2).map (stackArg s), nB s)

/-- On entry. -/
def C0 (d : PDat) (s : State) : Prop := fnContract.pre s ∧ dataOf s = d

/-- The code's list of programs. -/
abbrev privF : List (Prog isa) := Code.flat PrivPre.code

/-- What the public data fixes. -/
structure DataEq (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  a6 : s₀.gpr .a6 = s₀'.gpr .a6
  a7 : s₀.gpr .a7 = s₀'.gpr .a7
  sa : ∀ i < 2, stackArg s₀ i = stackArg s₀' i
  nb : nB s₀ = nB s₀'

theorem two_data {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') : DataEq s₀ s₀' := by
  have e := h.2.trans h'.2.symm
  have h1 : argRegs.map s₀.gpr = argRegs.map s₀'.gpr := congrArg Prod.fst e
  have h2 : (List.range 2).map (stackArg s₀) = (List.range 2).map (stackArg s₀') := congrArg (fun x => x.2.1) e
  have m := List.map_inj_left.mp h1
  exact ⟨m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide), m _ (by decide),
    m _ (by decide), m _ (by decide), fun i hi => List.map_inj_left.mp h2 i (List.mem_range.mpr hi),
    congrArg (fun x => x.2.2) e⟩

/-- What two initial states with the same public data share. -/
theorem data_vals {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') :
    cS s₀ = cS s₀' ∧ cZ s₀ = cZ s₀' ∧ ck s₀ = ck s₀' ∧ cpL s₀ = cpL s₀' ∧ cqL s₀ = cqL s₀' ∧
      s₀.gpr .a0 = s₀'.gpr .a0 ∧ s₀.gpr .a2 = s₀'.gpr .a2 ∧ s₀.gpr .a4 = s₀'.gpr .a4 ∧
      s₀.gpr .a6 = s₀'.gpr .a6 ∧ nB s₀ = nB s₀' := by
  have E := two_data h h'
  exact ⟨E.sa 0 (by decide), by simp only [cZ, E.sa 1 (by decide)], by simp only [ck, E.a3],
    by simp only [cpL, E.a5], by simp only [cqL, E.a7], E.a0, E.a2, E.a4, E.a6, E.nb⟩

theorem pins_C0 : Pins C0 [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

/-- After loading the working space's address. -/
def L1 (d : PDat) (s : State) : Prop := ∃ s₀, C0 d s₀ ∧ s.gpr .t0 = stackArg s₀ 0 ∧ Keep [.t0] s₀ s

theorem pins_L1 : Pins L1 [.t0, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a0', k⟩ ⟨s₀', h₀', b0', k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0', b0', E.sa 0 (by decide)]
  all_goals rw [k.gpr (by decide), k'.gpr (by decide)]
  exacts [E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7]

theorem stack_in {s₀ : State} (h : fnContract.pre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 := by
  have hargs : argsR s₀ ∈ s₀.rd := by
    rw [h.2.1]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact ⟨_, List.mem_append_left _ hargs, by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [BitVec.add_zero] at this⟩

theorem loadS_L1 {d : PDat} {s : State} (h : C0 d s) :
    WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 0]) s (L1 d) := by
  have hp := h.1
  have hsp : s.sp.toNat % 8 = 0 := by have := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega_arith
  have hst' : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd, add_ofNat_zero] using stack_in hp
  have hv : s.mem.readW s.sp 64 = stackArg s 0 := by
    show s.mem.readW s.sp 64 = s.mem.readW (stackArgAddr s 0) 64
    simp only [stackArgAddr, Nat.reduceMul, add_ofNat_zero]
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = stackArg s 0) ?_ (by rfl) (by rfl))
    fun t ⟨a0, k⟩ => ⟨s, h, a0, k⟩
  brun [exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, hst', hsp, hv]

/-- The first block: the registers it keeps, and the working space in `t0`
and `s6`. -/
theorem front1_ok {s₀ : State} (h : fnContract.pre s₀) :
    WP isa (.block (PrivPre.save ++ PrivPre.args)) s₀ fun u =>
      Keep [.t0, .s6] s₀ u ∧ u.gpr .s6 = cS s₀ ∧ u.gpr .t0 = cS s₀ := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  have hP := pre_facts hpre0
  have room := hP.room
  have hscr : Scr s₀ (cS s₀) (cZ s₀) :=
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS alS
  have hn := hscr.nowrap
  have hZ : 256 + 112 ≤ cZ s₀ := by unfold slot hdrBytes at room; omega_arith
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have esav : ∀ i, off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := fun i => by
    simp only [off, savW]; rw [Offset.add_add]
  have hsavR : ∀ i < 13, (scrR s₀).Contains (off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [esav]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hsavA : ∀ i < 13, (off (savW (cS s₀)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [esav]; exact hscr.al8 (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ rfl (stack_in hpre0) (by omega_arith)
    (fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), hsavR i hi⟩) hsavA)
    fun t hSv => ?_
  have kt := hSv.keep
  refine WP.mono (args_ok (hscr.congr kt.2.2) (by omega_arith) (by rw [hSv.s6]; exact (BitVec.add_zero _).symm))
    fun u ⟨_, ku⟩ => ⟨(kt.trans ku).mono (by decide), by rw [ku.gpr (by decide)]; exact hSv.s6,
      by rw [ku.gpr (by decide)]; exact hSv.t0⟩

theorem pins1 : Pins (At C0 privF 1) [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .s6] := by
  refine pins_at_list (fun s₀ => [s₀.gpr .a0, s₀.gpr .a1, s₀.gpr .a2, s₀.gpr .a3, s₀.gpr .a4, s₀.gpr .a5,
      s₀.gpr .a6, s₀.gpr .a7, cS s₀, cS s₀])
    (fun _ s₀ h => WP.of_flat (c := .block (PrivPre.save ++ PrivPre.args)) rfl
      (WP.mono (front1_ok h.1) fun u ⟨k, a6, a0'⟩ => by
        simp only [List.map_cons, List.map_nil, a6, a0', k.gpr (r := .a0) (by decide),
          k.gpr (r := .a1) (by decide), k.gpr (r := .a2) (by decide), k.gpr (r := .a3) (by decide),
          k.gpr (r := .a4) (by decide), k.gpr (r := .a5) (by decide), k.gpr (r := .a6) (by decide),
          k.gpr (r := .a7) (by decide)]))
    fun _ s₀ s₀' h h' => ?_
  have E := two_data h h'
  simp only [cS, E.a0, E.a1, E.a2, E.a3, E.a4, E.a5, E.a6, E.a7, E.sa 0 (by decide)]

/-- The front, to `setupX`. -/
abbrev NF (c : Prog isa) : Prog isa :=
  .seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX) c))

/-- `X`'s registers. -/
abbrev rsX : List Reg := [.a7, .ra, .s5, .s11, .t0, .s6]

abbrev valsX (s₀ : State) : List (BitVec 64) :=
  [Mont.off (cS s₀) (slot (cwX s₀) 0), Mont.off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
    BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (cwX s₀), cS s₀]

theorem valsX_eq {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') : valsX s₀ = valsX s₀' := by
  obtain ⟨eS, -, ek, -⟩ := data_vals h h'
  simp only [valsX, cwX, cw, eS, ek]

theorem pins5 : Pins (At C0 privF 5) rsX :=
  pins_at_list valsX
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NF (.block [])) rfl (partA0_ok h.1 fun x X => wp_nil (by
      simp only [rsX, valsX, List.map_cons, List.map_nil, X.a7, X.ra, X.s5, X.s11, X.t0, X.s6]))))
    fun _ _ _ h h' => valsX_eq h h'

/-! ## `loadX` -/

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

theorem xi_front {s₀ s : State} (X : A0 s₀ s) : XI s₀ s s :=
  ⟨X.scr, X.s6, X.a7, X.ra, X.s5, X.s11, X.t0, Mont.Outside.refl _ _ _ _, by rw [X.keep.2.1, X.keep.2.2]⟩

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

/-- A buffer's address and length, as a block. -/
abbrev LD (oA oL : Nat) : Prog isa := .block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL]

/-- The front, then `X`'s array 0 := all ones, then `c`. -/
abbrev N0 (c : Prog isa) : Prog isa := NF (.seq (.block [.addi .t3 .a7 0]) (.seq onesWords c))

/-- A buffer into array `j`, then `c`. -/
abbrev LJ (j oA oL : Nat) (c : Prog isa) : Prog isa := .seq (.seq (LD oA oL) (loadArr j)) c

theorem xi_start {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → A0 s₀ s → XI s₀ s t → WP isa c t Q) : WP isa (N0 c) s₀ Q :=
  partA0_ok h.1 fun s F => xi_ones (pre_facts h.1) (xi_front F) fun t X => hc s t (pre_facts h.1) F X

theorem ldv_eq {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') {A A' : Addr} {L L' : Nat}
    (hA : A = A') (hL : L = L') :
    valsX s₀ ++ [Mont.off A 0, BitVec.ofNat 64 L] = valsX s₀' ++ [Mont.off A' 0, BitVec.ofNat 64 L'] := by
  rw [valsX_eq h h', hA, hL]

/-- The header's words that `loadX` reads. -/
theorem hdrN {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oN = Mont.off (s₀.gpr .a2) 0 := by
  rw [F.hN]; exact z0 _
theorem hdrNL {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oNLen = BitVec.ofNat 64 (ck s₀) :=
  F.hNL.trans (Pre.ofNat_toNat64 _).symm
theorem hdrP {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oP = Mont.off (s₀.gpr .a4) 0 := by
  rw [F.hP]; exact z0 _
theorem hdrPL {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oPLen = BitVec.ofNat 64 (cpL s₀) :=
  F.hPL.trans (Pre.ofNat_toNat64 _).symm
theorem hdrQ {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oQ = Mont.off (s₀.gpr .a6) 0 := by
  rw [F.hQ]; exact z0 _
theorem hdrQL {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oQLen = BitVec.ofNat 64 (cqL s₀) :=
  F.hQL.trans (Pre.ofNat_toNat64 _).symm
theorem hdrIn {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oIn = Mont.off (s₀.gpr .a0) 0 := by
  rw [F.hIn]; exact z0 _
theorem hdrQI {s₀ s : State} (F : A0 s₀ s) : Mont.word s.mem (cS s₀) oQInv = Mont.off (s₀.gpr .a0) 0 := by
  rw [F.hQI]; exact z0 _

theorem pins9 : Pins (At C0 privF 9) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a2) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 (LD oN oNLen)) rfl (xi_start h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) (hdrN F) (hdrNL F)))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.1 E.2.2.1

theorem pins17 : Pins (At C0 privF 17) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a4) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LD oP oPLen))) rfl (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) (hdrN F) (hdrNL F) (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_ld hP X (by decide) (by decide) (hdrP F) (hdrPL F)))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.2.1 E.2.2.2.1

theorem pins25 : Pins (At C0 privF 25) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a6) 0, BitVec.ofNat 64 (cqL s₀)])
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LD oQ oQLen)))) rfl
      (xi_start h fun _ _ hP F X =>
      xi_load (j := 1) hP X (by decide) (by decide) (by decide) (hdrN F) (hdrNL F) (by have := hP.k64; omega_arith)
        (Nat.le_refl _) hP.rN hP.sN fun _ X =>
      xi_load (j := 4) hP X (by decide) (by decide) (by decide) (hdrP F) (hdrPL F) hP.p1 (Nat.le_of_lt hP.pk)
        hP.rP hP.sP fun _ X =>
      xi_ld hP X (by decide) (by decide) (hdrQ F) (hdrQL F)))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.2.2.2.1 E.2.2.2.2.1

/-- `loadX`'s first three buffers, from the front, then `c`. -/
abbrev N3 (c : Prog isa) : Prog isa := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen c)))

theorem xi_three {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → A0 s₀ s → XI s₀ s t → WP isa c t Q) : WP isa (N3 c) s₀ Q :=
  xi_start h fun s _ hP F X =>
    xi_load (j := 1) hP X (by decide) (by decide) (by decide) (hdrN F) (hdrNL F) (by have := hP.k64; omega_arith)
      (Nat.le_refl _) hP.rN hP.sN fun _ X =>
    xi_load (j := 4) hP X (by decide) (by decide) (by decide) (hdrP F) (hdrPL F) hP.p1 (Nat.le_of_lt hP.pk)
      hP.rP hP.sP fun _ X =>
    xi_load (j := 5) hP X (by decide) (by decide) (by decide) (hdrQ F) (hdrQL F) hP.q1 (Nat.le_of_lt hP.qk)
      hP.rQ hP.sQ fun t X => hc s t hP F X

theorem pins33 : Pins (At C0 privF 33) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a0) 0, BitVec.ofNat 64 (ck s₀)])
    (fun _ s₀ h => WP.of_flat (c := N3 (LD oIn oNLen)) rfl (xi_three h fun _ _ hP F X =>
      xi_ld hP X (by decide) (by decide) (hdrIn F) (hdrNL F)))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.1 E.2.2.1

theorem pins41 : Pins (At C0 privF 41) (rsX ++ ([.s7, .s8] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a0) 0, BitVec.ofNat 64 (cpL s₀)])
    (fun _ s₀ h => WP.of_flat (c := N3 (LJ 6 oIn oNLen (LD oQInv oPLen))) rfl (xi_three h fun _ _ hP F X =>
      xi_load (j := 6) hP X (by decide) (by decide) (by decide) (hdrIn F) (hdrNL F)
        (by have := hP.k64; omega_arith) (Nat.le_refl _) hP.rPre hP.sPre fun _ X =>
      xi_ld hP X (by decide) (by decide) (hdrQI F) (hdrPL F)))
    fun _ _ _ h h' => let E := data_vals h h'; ldv_eq h h' E.2.2.2.2.2.1 E.2.2.2.1

/-- `loadX`, from the front, then `c`. -/
abbrev NX (c : Prog isa) : Prog isa := N3 (LJ 6 oIn oNLen (LJ 7 oQInv oPLen c))

theorem xi_loadX {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ s t, PF s₀ → A0 s₀ s → XI s₀ s t → WP isa c t Q) : WP isa (NX c) s₀ Q :=
  xi_three h fun s _ hP F X =>
    xi_load (j := 6) hP X (by decide) (by decide) (by decide) (hdrIn F) (hdrNL F)
      (by have := hP.k64; omega_arith) (Nat.le_refl _) hP.rPre hP.sPre fun _ X =>
    xi_load (j := 7) hP X (by decide) (by decide) (by decide) (hdrQI F) (hdrPL F) hP.p1 (Nat.le_of_lt hP.pk)
      (fun i hi => hP.rPre i (Nat.lt_trans hi hP.pk)) (fun i hi => hP.sPre i (Nat.lt_trans hi hP.pk))
      fun t X => hc s t hP F X

/-- `w_p` and `w_q`, as `PrivPre.pqLens` computes them. -/
abbrev vP (s₀ : State) : BitVec 64 := BitVec.ofNat 64 ((cpL s₀ + 7) / 8)
abbrev vQ (s₀ : State) : BitVec 64 := BitVec.ofNat 64 ((cqL s₀ + 7) / 8)

/-- `pqLens`, after `loadX`: `w_p` and `w_q` from the header, into `a3` and
`t1`. -/
theorem xi_lens {s₀ s t : State} (hP : PF s₀) (F : A0 s₀ s) (X : XI s₀ s t) :
    WP isa (.block PrivPre.pqLens) t fun u => (XI s₀ s u ∧ u.gpr .a3 = vP s₀ ∧ u.gpr .t1 = vQ s₀) := by
  have room := hP.room; have pk := hP.pk; have qk := hP.qk; have k1024 := hP.k1024
  have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
  have rPL : t.mem.readW (off (cS s₀) 40) 64 = BitVec.ofNat 64 (cpL s₀) :=
    (X.hdr hP (d := oPLen) (by decide)).trans (hdrPL F)
  have rQL : t.mem.readW (off (cS s₀) 56) 64 = BitVec.ofNat 64 (cqL s₀) :=
    (X.hdr hP (d := oQLen) (by decide)).trans (hdrQL F)
  refine WP.mono (WP.keep [.a3, .t1] (Q := fun u => u.gpr .a3 = vP s₀ ∧ u.gpr .t1 = vQ s₀ ∧ u.mem = t.mem) (by
    unfold PrivPre.pqLens
    brun [oPLen, oQLen, X.s6, rPL, rQL, len_words (cpL s₀) (Nat.lt_of_lt_of_le pk (by omega_arith)),
      len_words (cqL s₀) (Nat.lt_of_lt_of_le qk (by omega_arith)),
      X.scr.ld (show 40 + 8 ≤ cZ s₀ by omega_arith), X.scr.al8 (show 40 + 8 ≤ cZ s₀ by omega_arith) (by decide),
      X.scr.ld (show 56 + 8 ≤ cZ s₀ by omega_arith), X.scr.al8 (show 56 + 8 ≤ cZ s₀ by omega_arith) (by decide)])
    (by rfl) (by rfl)) fun u ⟨⟨u3, u1, um⟩, k⟩ => ⟨XI.step hP X k (by decide) ((k.gpr (by decide)).trans X.a7)
      (o := 256) (n := 0) (by rw [um]; exact Mont.Outside.refl _ _ _ _) (Nat.le_refl _)
      (by unfold slot hdrBytes; omega_arith), u3, u1⟩

/-- `pqLens`, then a buffer's address and length. -/
theorem xi_ld4 {s₀ s t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (F : A0 s₀ s) (X : XI s₀ s t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : Mont.word s.mem (cS s₀) oA = Mont.off A 0) (hLw : Mont.word s.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.seq (.block PrivPre.pqLens) (.block [.load .d .s7 .s6 oA, .load .d .s8 .s6 oL])) t fun u =>
      (rsX ++ ([.s7, .s8, .a3, .t1] : List Reg)).map u.gpr =
        valsX s₀ ++ [Mont.off A 0, BitVec.ofNat 64 L, vP s₀, vQ s₀] := by
  have room := hP.room
  refine WP.seq (WP.mono (xi_lens hP F X) fun u ⟨X', l3, l1⟩ => ?_)
  refine WP.mono (ld2_ok (A := A) (L := L) X'.scr (by unfold slot at room; omega_arith) X'.s6 hoA hoL
    (by rw [X'.hdr hP hoA.1]; exact hA) (by rw [X'.hdr hP hoL.1]; exact hLw)) fun v ⟨⟨a7, a8, _⟩, k⟩ => ?_
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, a7, a8, k.gpr (r := .a7) (by decide),
    k.gpr (r := .ra) (by decide), k.gpr (r := .s5) (by decide), k.gpr (r := .s11) (by decide),
    k.gpr (r := .t0) (by decide), k.gpr (r := .s6) (by decide), k.gpr (r := .a3) (by decide),
    k.gpr (r := .t1) (by decide), X'.a7, X'.ra, X'.s5, X'.s11, X'.t0, X'.s6, l3, l1]

theorem pins50 : Pins (At C0 privF 50) (rsX ++ ([.s7, .s8, .a3, .t1] : List Reg)) :=
  pins_at_list (fun s₀ => valsX s₀ ++ [Mont.off (s₀.gpr .a2) 0, BitVec.ofNat 64 (ck s₀), vP s₀, vQ s₀])
    (fun _ s₀ h => WP.of_flat (c := NX (.seq (.block PrivPre.pqLens) (LD oN oNLen))) rfl
      (xi_loadX h fun _ _ hP F X => xi_ld4 hP F X (by decide) (by decide) (hdrN F) (hdrNL F)))
    fun _ _ _ h h' => by
      obtain ⟨-, -, ek, ep, eq, -, e2, -⟩ := data_vals h h'
      simp only [vP, vQ]; rw [valsX_eq h h', ek, ep, eq, e2]

/-- `n`'s first byte. -/
abbrev nb0 (s₀ : State) : BitVec 64 := BitVec.ofNat 64 ((nB s₀).getD 0 0).toNat

theorem pins51 : Pins (At C0 privF 51) (rsX ++ ([.s8, .t4, .a3, .t1] : List Reg)) := by
  refine pins_at_list (fun s₀ => valsX s₀ ++ [BitVec.ofNat 64 (ck s₀), nb0 s₀, vP s₀, vQ s₀])
    (fun _ s₀ h => WP.of_flat (c := NX (.seq (.block PrivPre.pqLens) (.seq (LD oN oNLen)
      (.block Precompute.check1)))) rfl (xi_loadX h fun s t hP F X => ?_)) fun _ _ _ h h' => ?_
  · have k64 := hP.k64; have room := hP.room
    have hZ : 256 ≤ cZ s₀ := by unfold slot at room; omega_arith
    have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    refine WP.seq (WP.mono (xi_lens hP F X) fun t' ⟨X', l3, l1⟩ => ?_)
    refine WP.seq (WP.mono (ld2_ok (A := s₀.gpr .a2) (L := ck s₀) X'.scr hZ X'.s6 (by decide) (by decide)
      (by rw [X'.hdr hP (by decide)]; exact hdrN F) (by rw [X'.hdr hP (by decide)]; exact hdrNL F))
      fun u ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
    -- `n`'s bytes, apart from the working space and `pre`, are as on entry.
    have hbt : Spec.Rsa.bytesAt u.mem (s₀.gpr .a2) (ck s₀) = nB s₀ := by
      refine Eq.trans ?_ (bytes_frame F.frame hP.dN (Nat.le_of_lt (BitVec.isLt _)))
      rw [m1]
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => X'.out _ (Or.inr ?_)
      have hs := hP.sN i (List.mem_range.mp hi)
      have hx : ¬ Mont.ofs (cS s₀) (Mont.off (s₀.gpr .a2) i) < cZ s₀ := fun hc => hs _ hc rfl
      change ¬ (s₀.gpr .a2 + BitVec.ofNat 64 i - cS s₀).toNat < _ at hx
      change _ ≤ (s₀.gpr .a2 + BitVec.ofNat 64 i - cS s₀).toNat
      omega_arith
    refine WP.mono (VG.Proof.Bignum.RISCV64.check1_ok (nb := nB s₀) a7 a8 k64 hlen
      (by rw [k1.2.1, k1.2.2, X'.rd]; exact hP.rN) fun i hi => ?_) fun v ⟨⟨_, v4, _⟩, k2⟩ => ?_
    · rw [← List.getElem_of_eq hbt (by rw [Spec.Rsa.bytesAt, List.length_map, List.length_range]; omega_arith)]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    · have k12 := k1.trans k2
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, v4, k2.gpr (r := .s8) (by decide), a8,
        k12.gpr (r := .a7) (by decide), k12.gpr (r := .ra) (by decide), k12.gpr (r := .s5) (by decide),
        k12.gpr (r := .s11) (by decide), k12.gpr (r := .t0) (by decide), k12.gpr (r := .s6) (by decide),
        k12.gpr (r := .a3) (by decide), k12.gpr (r := .t1) (by decide), l3, l1,
        X'.a7, X'.ra, X'.s5, X'.s11, X'.t0, X'.s6, nb0, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 0 < (nB s₀).length by omega_arith), Option.getD_some]
  · obtain ⟨-, -, ek, ep, eq, -, -, -, -, en⟩ := data_vals h h'
    rw [valsX_eq h h']; simp only [nb0, vP, vQ]; rw [en, ek, ep, eq]

end VG.Proof.Bignum.RISCV64.PrivPre
