module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreE
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoadX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the registers at the cuts of the checks

The public data of a run (`dataOf`): the argument registers, the stack
arguments and `n`'s bytes. The code's list of programs (`privF`) is cut
after each block that loads values of the header, which the taint analysis
finds secret: the registers there, from the initial state (`pins*`). In
`loadX`, `XJ` is what a buffer's load needs, as `vg_rsa_private_crt`'s
(`CrtPinsA.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Pins At pins_at_list)

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
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  r4 : s₀.gpr .r4 = s₀'.gpr .r4
  r5 : s₀.gpr .r5 = s₀'.gpr .r5
  r6 : s₀.gpr .r6 = s₀'.gpr .r6
  r7 : s₀.gpr .r7 = s₀'.gpr .r7
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  r10 : s₀.gpr .r10 = s₀'.gpr .r10
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
      s₀.gpr .r3 = s₀'.gpr .r3 ∧ s₀.gpr .r5 = s₀'.gpr .r5 ∧ s₀.gpr .r7 = s₀'.gpr .r7 ∧
      s₀.gpr .r9 = s₀'.gpr .r9 ∧ nB s₀ = nB s₀' := by
  have E := two_data h h'
  exact ⟨E.sa 0 (by decide), by simp only [cZ, E.sa 1 (by decide)], by simp only [ck, E.r6],
    by simp only [cpL, E.r8], by simp only [cqL, E.r10], E.r3, E.r5, E.r7, E.r9, E.nb⟩

theorem pins_C0 : Pins C0 [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  have E := two_data h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

/-- After loading the working space's address. -/
def L1 (d : PDat) (s : State) : Prop := ∃ s₀, C0 d s₀ ∧ s.gpr .r11 = stackArg s₀ 0 ∧ Keep [.r11] s₀ s

theorem pins_L1 : Pins L1 [.r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro d s₁ s₂ ⟨s₀, h₀, a11, k⟩ ⟨s₀', h₀', b11, k'⟩ r hr
  have E := two_data h₀ h₀'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a11, b11, E.sa 0 (by decide)]
  all_goals rw [k.gpr _ (by decide), k'.gpr _ (by decide)]
  exacts [E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10]

theorem stack_in {s₀ : State} (h : fnContract.pre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 := by
  have hargs : argsR s₀ ∈ s₀.rd := by
    rw [h.2.1]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact ⟨_, List.mem_append_left _ hargs, by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [BitVec.add_zero] at this⟩

theorem loadS_L1 {d : PDat} {s : State} (h : C0 d s) :
    WP isa (.block [.addSp .r11 96, .load .d .r11 .r11 0]) s (L1 d) :=
  WP.mono (loadS_ok s (stack_in h.1)) fun _ ⟨⟨a11, _, _⟩, k⟩ => ⟨s, h, a11, k⟩

/-- The first block: the registers it keeps, and the working space in `r23`. -/
theorem front1_ok {s₀ : State} (h : fnContract.pre s₀) :
    WP isa (.block (PrivPre.save ++ PrivPre.args)) s₀ fun u => Keep [.r11, .r23] s₀ u ∧ u.gpr .r23 = cS s₀ := by
  have hst := stack_in h
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, nwS, ⟨hk, -⟩, -, -, -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hscr : Scr s₀ (cS s₀) (cZ s₀) :=
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS
  have hn := hscr.nowrap
  have hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .r6).toNat + 256 ≤ (stackArg s₀ 1).toNat * 8; omega_arith
  have hS : scrR s₀ ∈ s₀.wr := by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hsavR : ∀ i < 18, (scrR s₀).Contains (off (Crt.savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ hst fun i hi => ⟨_, hS, hsavR i hi⟩) fun t ⟨s₁, a11, _, k1, hSv⟩ => ?_
  have kt := k1.trans hSv.keep
  refine WP.mono (args_ok (hscr.congr kt.wr) (by omega_arith) (hSv.r23.trans a11)) fun u ⟨_, ku⟩ =>
    ⟨(kt.trans ku).mono (by decide), by rw [ku.gpr _ (by decide)]; exact hSv.r23.trans a11⟩

/-- `Code.seqL` of a list and an empty block, as of the list. -/
theorem wp_seqL_nil {l : List (Prog isa)} {s : State} {Q : State → Prop}
    (h : WP isa (Code.seqL (l ++ [.block []])) s Q) : WP isa (Code.seqL l) s Q := by
  obtain ⟨t, s', e, hq⟩ := h
  obtain ⟨_, _, u, -, e₁, e₂⟩ := exec_seqL_append.mp e
  cases e₂ with
  | seq x y =>
    obtain ⟨-, rfl⟩ := exec_nil_iff.mp x
    obtain ⟨-, rfl⟩ := exec_nil_iff.mp y
    exact ⟨_, _, e₁, hq⟩

theorem wp_skip {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := ⟨[], s, .block rfl, h⟩

theorem pins1 : Pins (At C0 privF 1) [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r23] := by
  refine pins_at_list (fun s₀ => [s₀.gpr .r3, s₀.gpr .r4, s₀.gpr .r5, s₀.gpr .r6, s₀.gpr .r7, s₀.gpr .r8,
      s₀.gpr .r9, s₀.gpr .r10, cS s₀])
    (fun _ s₀ h => WP.of_flat (c := .block (PrivPre.save ++ PrivPre.args)) rfl
      (WP.mono (front1_ok h.1) fun u ⟨k, a23⟩ => by
        simp only [List.map_cons, List.map_nil, a23, k.gpr .r3 (by decide), k.gpr .r4 (by decide),
          k.gpr .r5 (by decide), k.gpr .r6 (by decide), k.gpr .r7 (by decide), k.gpr .r8 (by decide),
          k.gpr .r9 (by decide), k.gpr .r10 (by decide)]))
    fun _ s₀ s₀' h h' => ?_
  have E := two_data h h'
  simp only [cS, E.r3, E.r4, E.r5, E.r6, E.r7, E.r8, E.r9, E.r10, E.sa 0 (by decide)]

/-- The front, to `setupX`. -/
abbrev NF (c : Prog isa) : Prog isa :=
  .seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX) c))

theorem pins5 : Pins (At C0 privF 5) [.r10, .r11, .r21, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀),
      off (cS s₀) (slot (cwX s₀) 0), cS s₀, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)),
      BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => wp_seqL_nil (WP.of_flat (c := NF (.block [])) rfl (partA0_ok h.1 fun x X => wp_skip (by
      simp only [List.map_cons, List.map_nil, X.r10, X.r11, X.r21, X.r23, X.r27, X.r28, X.r29]))))
    fun _ s₀ s₀' h h' => ?_
  obtain ⟨eS, -, ek, -⟩ := data_vals h h'
  simp only [cwX, cw, eS, ek]

/-! ## `loadX` -/

/-- In `loadX`, after the front left `x`. -/
structure XJ (s₀ x t : State) : Prop where
  scr : Scr t (cS s₀) (cZ s₀)
  r23 : t.gpr .r23 = cS s₀
  r10 : t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : t.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : t.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  out : Outside (cS s₀) 256 (cZ s₀ - 256) x.mem t.mem
  rd : t.rd ++ t.wr = s₀.rd ++ s₀.wr

theorem xj_front {s₀ x : State} (X : A0 s₀ x) : XJ s₀ x x :=
  ⟨X.scr, X.r23, X.r10, X.r21, X.r29, X.r11, X.r27, X.r28, Outside.refl _ _ _ _, by rw [X.keep.rd, X.keep.wr]⟩

theorem XJ.hdr {s₀ x t : State} (hP : PF s₀) (X : XJ s₀ x t) {d : Nat} (hd : d + 8 ≤ 256) :
    word t.mem (cS s₀) d = word x.mem (cS s₀) d := by
  have hn := hP.nw; have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  exact X.out.word (Or.inl hd) (by omega_arith)

/-- `XJ` through code that keeps the registers and changes only the arrays. -/
theorem XJ.step {s₀ x t u : State} (hP : PF s₀) (X : XJ s₀ x t) {rs : List Reg} (k : Keep rs t u)
    (h : ∀ r ∈ [Reg.r23, .r21, .r29, .r11, .r27, .r28], r ∉ rs)
    (h10 : u.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0))
    (o : Outside (cS s₀) 256 (slot (cwX s₀) 8 - 256) t.mem u.mem) : XJ s₀ x u := by
  have room := hP.room
  have : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨X.scr.congr k.wr, (k.gpr _ h.1).trans X.r23, h10, (k.gpr _ h.2.1).trans X.r21,
    (k.gpr _ h.2.2.1).trans X.r29, (k.gpr _ h.2.2.2.1).trans X.r11, (k.gpr _ h.2.2.2.2.1).trans X.r27,
    (k.gpr _ h.2.2.2.2.2).trans X.r28, X.out.trans (o.mono (Nat.le_refl _) (by omega_arith)),
    by rw [k.rd, k.wr]; exact X.rd⟩

/-- `r14 := r10`, then `X`'s array 0 := all ones. -/
theorem xj_ones {s₀ x t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (X : XJ s₀ x t)
    (hc : ∀ u, XJ s₀ x u → WP isa c u Q) :
    WP isa (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c)) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have e0 : slot (cwX s₀) 0 = 256 + 0 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun u => u.gpr .r14 = off (cS s₀) (slot (cwX s₀) 0) ∧
    u.mem = t.mem) (by prun [X.r10, BitVec.add_zero]) (by decide)) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (Crt.onesWords_ok (X.scr.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans X.r11) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₂ ⟨⟨_, o2⟩, k2⟩ => hc t₂ ?_)
  rw [m1] at o2
  exact XJ.step hP X (k1.trans k2) (by decide) (((k1.trans k2).gpr _ (by decide)).trans X.r10)
    (o2.mono (by omega_arith) (by omega_arith))

/-- A buffer's address and length from the header's words `oA`, `oL`. -/
theorem xj_ld2 {s₀ x t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XJ s₀ x t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word x.mem (cS s₀) oA = off A 0) (hLw : word x.mem (cS s₀) oL = BitVec.ofNat 64 L) :
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
theorem xj_load {s₀ x t : State} {c : Prog isa} {Q : State → Prop} {j oA oL : Nat} {A : Addr} {L : Nat}
    (hP : PF s₀) (X : XJ s₀ x t) (hj : j < 8)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word x.mem (cS s₀) oA = off A 0) (hLw : word x.mem (cS s₀) oL = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLk : L ≤ ck s₀) (hrd : ∀ i < L, InRegions (s₀.rd ++ s₀.wr) (off A i) 1)
    (hsep : ∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x)
    (hc : ∀ u, XJ s₀ x u → WP isa c u Q) :
    WP isa (.seq (.seq (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) (loadArr j)) c) t Q := by
  have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  refine WP.seq (WP.mono (Crt.loadOne_ok X.scr (by omega_arith) hj (by omega_arith) X.r23 X.r10 X.r21 X.r29 X.r11 hoA hoL
    (by rw [X.hdr hP hoA.1]; exact hA) (by rw [X.hdr hP hoL.1]; exact hLw) hL (by omega_arith)
    (by rw [X.rd]; exact hrd) hsep) fun u ⟨⟨_, _, o, u10⟩, k⟩ => hc u ?_)
  have := slot_le (w := cwX s₀) hj
  have h256 : 256 ≤ slot (cwX s₀) j := Nat.le_add_right _ _
  exact XJ.step hP X k (by decide) u10 (o.mono (by omega_arith) (by omega_arith))

/-- The registers at the cut after a buffer's address and length. -/
abbrev ldVals (s₀ : State) (A : Addr) (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 L, off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (2 * cwX s₀), off A 0,
    off (cS s₀) (slot (cwX s₀) 0), cS s₀, BitVec.ofNat 64 (8 * (cwX s₀ + 2))]

theorem xj_ld {s₀ x t : State} {oA oL : Nat} {A : Addr} {L : Nat} (hP : PF s₀) (X : XJ s₀ x t)
    (hoA : oA + 8 ≤ 256 ∧ oA % 8 = 0) (hoL : oL + 8 ≤ 256 ∧ oL % 8 = 0)
    (hA : word x.mem (cS s₀) oA = off A 0) (hLw : word x.mem (cS s₀) oL = BitVec.ofNat 64 L) :
    WP isa (.block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]) t fun u =>
      [Reg.r6, .r10, .r11, .r12, .r21, .r23, .r29].map u.gpr = ldVals s₀ A L :=
  WP.mono (xj_ld2 hP X hoA hoL hA hLw) fun u ⟨⟨a12, a6, _⟩, k⟩ => by
    simp only [List.map_cons, List.map_nil, a12, a6, k.gpr .r10 (by decide), k.gpr .r11 (by decide),
      k.gpr .r21 (by decide), k.gpr .r23 (by decide), k.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r29]

theorem ldVals_eq {d : PDat} {s₀ s₀' : State} (h : C0 d s₀) (h' : C0 d s₀') {A A' : Addr} {L L' : Nat}
    (hA : A = A') (hL : L = L') : ldVals s₀ A L = ldVals s₀' A' L' := by
  obtain ⟨eS, -, ek, -⟩ := data_vals h h'
  simp only [ldVals, cwX, cw, eS, ek, hA, hL]

/-- A buffer's address and length, as a block. -/
abbrev LD (oA oL : Nat) : Prog isa := .block [.load .d .r12 .r23 oA, .load .d .r6 .r23 oL]

/-- The front, then `X`'s array 0 := all ones, then `c`. -/
abbrev N0 (c : Prog isa) : Prog isa := NF (.seq (.block [.addi .r14 .r10 0]) (.seq onesWords c))

/-- A buffer into array `j`, then `c`. -/
abbrev LJ (j oA oL : Nat) (c : Prog isa) : Prog isa := .seq (.seq (LD oA oL) (loadArr j)) c

theorem z0 (a : Addr) : a = off a 0 := (BitVec.add_zero a).symm

theorem xj_start {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ x t, PF s₀ → A0 s₀ x → XJ s₀ x t → WP isa c t Q) : WP isa (N0 c) s₀ Q :=
  partA0_ok h.1 fun x X => xj_ones (pre_facts h.1) (xj_front X) fun t XX => hc x t (pre_facts h.1) X XX

theorem pins9 : Pins (At C0 privF 9) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r5) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LD oN oNLen)) rfl (xj_start h fun _ _ hP F X =>
      xj_ld hP X (by decide) (by decide) (by rw [F.hN]; exact z0 _) (by rw [F.hNL]; exact (ofNat_toNat64 _).symm)))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.1 E.2.2.1

theorem pins17 : Pins (At C0 privF 17) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r7) (cpL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LD oP oPLen))) rfl (xj_start h fun _ _ hP F X =>
      xj_load (j := 1) hP X (by decide) (by decide) (by decide) (by rw [F.hN]; exact z0 _)
        (by rw [F.hNL]; exact (ofNat_toNat64 _).symm) (by have := hP.k64; omega_arith) (Nat.le_refl _) hP.rN hP.sN
        fun _ X => xj_ld hP X (by decide) (by decide) (by rw [F.hP]; exact z0 _)
          (by rw [F.hPL]; exact (ofNat_toNat64 _).symm)))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.1 E.2.2.2.1

theorem pins25 : Pins (At C0 privF 25) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r9) (cqL s₀))
    (fun _ s₀ h => WP.of_flat (c := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LD oQ oQLen)))) rfl
      (xj_start h fun _ _ hP F X =>
      xj_load (j := 1) hP X (by decide) (by decide) (by decide) (by rw [F.hN]; exact z0 _)
        (by rw [F.hNL]; exact (ofNat_toNat64 _).symm) (by have := hP.k64; omega_arith) (Nat.le_refl _) hP.rN hP.sN
        fun _ X =>
      xj_load (j := 4) hP X (by decide) (by decide) (by decide) (by rw [F.hP]; exact z0 _)
        (by rw [F.hPL]; exact (ofNat_toNat64 _).symm) hP.p1 (Nat.le_of_lt hP.pk) hP.rP hP.sP fun _ X =>
      xj_ld hP X (by decide) (by decide) (by rw [F.hQ]; exact z0 _) (by rw [F.hQL]; exact (ofNat_toNat64 _).symm)))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.2.2.2.1 E.2.2.2.2.1

/-- `loadX`'s first three buffers, from the front, then `c`. -/
abbrev N3 (c : Prog isa) : Prog isa := N0 (LJ 1 oN oNLen (LJ 4 oP oPLen (LJ 5 oQ oQLen c)))

theorem xj_three {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ x t, PF s₀ → A0 s₀ x → XJ s₀ x t → WP isa c t Q) : WP isa (N3 c) s₀ Q :=
  xj_start h fun x _ hP F X =>
    xj_load (j := 1) hP X (by decide) (by decide) (by decide) (by rw [F.hN]; exact z0 _)
      (by rw [F.hNL]; exact (ofNat_toNat64 _).symm) (by have := hP.k64; omega_arith) (Nat.le_refl _) hP.rN hP.sN
      fun _ X =>
    xj_load (j := 4) hP X (by decide) (by decide) (by decide) (by rw [F.hP]; exact z0 _)
      (by rw [F.hPL]; exact (ofNat_toNat64 _).symm) hP.p1 (Nat.le_of_lt hP.pk) hP.rP hP.sP fun _ X =>
    xj_load (j := 5) hP X (by decide) (by decide) (by decide) (by rw [F.hQ]; exact z0 _)
      (by rw [F.hQL]; exact (ofNat_toNat64 _).symm) hP.q1 (Nat.le_of_lt hP.qk) hP.rQ hP.sQ fun t X =>
    hc x t hP F X

theorem pins33 : Pins (At C0 privF 33) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r3) (ck s₀))
    (fun _ s₀ h => WP.of_flat (c := N3 (LD oIn oNLen)) rfl (xj_three h fun _ _ hP F X =>
      xj_ld hP X (by decide) (by decide) (by rw [F.hIn]; exact z0 _) (by rw [F.hNL]; exact (ofNat_toNat64 _).symm)))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.1 E.2.2.1

theorem pins41 : Pins (At C0 privF 41) [.r6, .r10, .r11, .r12, .r21, .r23, .r29] :=
  pins_at_list (fun s₀ => ldVals s₀ (s₀.gpr .r3) (cpL s₀))
    (fun _ s₀ h => WP.of_flat (c := N3 (LJ 6 oIn oNLen (LD oQInv oPLen))) rfl (xj_three h fun _ _ hP F X =>
      xj_load (j := 6) hP X (by decide) (by decide) (by decide) (by rw [F.hIn]; exact z0 _)
        (by rw [F.hNL]; exact (ofNat_toNat64 _).symm) (by have := hP.k64; omega_arith) (Nat.le_refl _)
        hP.rPre hP.sPre fun _ X =>
      xj_ld hP X (by decide) (by decide) (by rw [F.hQI]; exact z0 _) (by rw [F.hPL]; exact (ofNat_toNat64 _).symm)))
    fun _ _ _ h h' => let E := data_vals h h'; ldVals_eq h h' E.2.2.2.2.2.1 E.2.2.2.1

/-- `loadX`, from the front, then `c`. -/
abbrev NX (c : Prog isa) : Prog isa := N3 (LJ 6 oIn oNLen (LJ 7 oQInv oPLen c))

theorem xj_loadX {d : PDat} {s₀ : State} {c : Prog isa} {Q : State → Prop} (h : C0 d s₀)
    (hc : ∀ x t, PF s₀ → A0 s₀ x → XJ s₀ x t → WP isa c t Q) : WP isa (NX c) s₀ Q :=
  xj_three h fun x _ hP F X =>
    xj_load (j := 6) hP X (by decide) (by decide) (by decide) (by rw [F.hIn]; exact z0 _)
      (by rw [F.hNL]; exact (ofNat_toNat64 _).symm) (by have := hP.k64; omega_arith) (Nat.le_refl _)
      hP.rPre hP.sPre fun _ X =>
    xj_load (j := 7) hP X (by decide) (by decide) (by decide) (by rw [F.hQI]; exact z0 _)
      (by rw [F.hPL]; exact (ofNat_toNat64 _).symm) hP.p1 (Nat.le_of_lt hP.pk)
      (fun i hi => hP.rPre i (Nat.lt_trans hi hP.pk)) (fun i hi => hP.sPre i (Nat.lt_trans hi hP.pk))
      fun t X => hc x t hP F X

theorem pins49 : Pins (At C0 privF 49) [.r6, .r12] :=
  pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (s₀.gpr .r5) 0])
    (fun _ s₀ h => WP.of_flat (c := NX (LD oN oNLen)) rfl (xj_loadX h fun _ _ hP F X =>
      WP.mono (xj_ld2 (A := s₀.gpr .r5) (L := ck s₀) hP X (by decide) (by decide) (by rw [F.hN]; exact z0 _)
        (by rw [F.hNL]; exact (ofNat_toNat64 _).symm)) fun u ⟨⟨a12, a6, _⟩, _⟩ => by
        simp only [List.map_cons, List.map_nil, a12, a6]))
    fun _ _ _ h h' => by
      obtain ⟨-, -, ek, -, -, -, e5, -⟩ := data_vals h h'
      rw [ek, e5]

/-- `n`'s first byte. -/
abbrev nb0 (s₀ : State) : BitVec 64 := BitVec.ofNat 64 ((nB s₀).getD 0 0).toNat

theorem pins50 : Pins (At C0 privF 50) [.r6, .r10, .r11, .r15, .r21, .r23, .r27, .r28, .r29] := by
  refine pins_at_list (fun s₀ => [BitVec.ofNat 64 (ck s₀), off (cS s₀) (slot (cwX s₀) 0),
      BitVec.ofNat 64 (2 * cwX s₀), nb0 s₀, off (cS s₀) (slot (cwX s₀) 0), cS s₀,
      off (cS s₀) (slot (cwX s₀) 0), BitVec.ofNat 64 (8 * (cwX s₀ + 2)), BitVec.ofNat 64 (8 * (cwX s₀ + 2))])
    (fun _ s₀ h => WP.of_flat (c := NX (.seq (LD oN oNLen) (.block Precompute.check1))) rfl
      (xj_loadX h fun x t hP F X => ?_))
    fun _ _ _ h h' => ?_
  · have hn := hP.nw; have room := hP.room; have k64 := hP.k64
    have e8 : slot (cwX s₀) 8 = 256 + 8 * (8 * (cwX s₀ + 2)) := rfl
    have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    refine WP.seq (WP.mono (xj_ld2 (A := s₀.gpr .r5) (L := ck s₀) hP X (by decide) (by decide) (by rw [F.hN]; exact z0 _)
      (by rw [F.hNL]; exact (ofNat_toNat64 _).symm)) fun u ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
    -- `n`'s bytes, apart from the working space and `pre`, are as on entry.
    have hbt : Spec.Rsa.bytesAt u.mem (s₀.gpr .r5) (ck s₀) = nB s₀ := by
      refine Eq.trans ?_ (bytes_frame F.frame hP.dN (Nat.le_of_lt (BitVec.isLt _)))
      rw [m1]
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => X.out _ (Or.inr ?_)
      have hs := hP.sN i (List.mem_range.mp hi)
      have hx : ¬ ofs (cS s₀) (s₀.gpr .r5 + BitVec.ofNat 64 i) < cZ s₀ := fun hc => hs _ hc rfl
      omega_arith
    refine WP.mono (check1_ok (N := s₀.gpr .r5) (nb := nB s₀) a12 a6 k64 hlen
      (by rw [k1.rd, k1.wr, X.rd]; exact hP.rN) fun i hi => ?_) fun v ⟨⟨_, v15, _, _⟩, k2⟩ => ?_
    · rw [← List.getElem_of_eq hbt (by rw [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hi)]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    · have k12 := k1.trans k2
      simp only [List.map_cons, List.map_nil, v15, k2.gpr .r6 (by decide), a6, k12.gpr .r10 (by decide),
        k12.gpr .r11 (by decide), k12.gpr .r21 (by decide), k12.gpr .r23 (by decide), k12.gpr .r27 (by decide),
        k12.gpr .r28 (by decide), k12.gpr .r29 (by decide), X.r10, X.r11, X.r21, X.r23, X.r27, X.r28, X.r29,
        nb0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (nB s₀).length by omega_arith),
        Option.getD_some]
  · obtain ⟨eS, -, ek, -, -, -, -, -, -, en⟩ := data_vals h h'
    simp only [nb0, cwX, cw]; rw [en, eS, ek]

end VG.Proof.Bignum.PPC64LE.PrivPre
