module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# The RSA private-key operation on RISC-V: the contract and the front

`fnContract`: `vg_rsa_private_crt` on the registers and the stack (`out`,
`n`, the input and `p` with their lengths in `a0`–`a7`, then `q`, `dP`, `dQ`,
`qInv` and the working space with theirs on the stack). `pre_facts` (`PF`):
what the code needs of it, the working space's room for `X`, `P` and `Q`
among them. `front_ok` (`Front`): `save`, `args` and `setupX`, which put the
callee-saved registers and the arguments in `X`'s header and set `X`'s
registers and the bases of `P` and `Q`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr)
open VG.Proof.Bignum (slot)

/-- The arguments on the stack: ten words. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- `vg_rsa_private_crt`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let n : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let inp : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let p : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    s.rd = [n, inp, p, q, dp, dq, qi, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      n.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a3).toNat ∧ (s.gpr .a1).toNat = (s.gpr .a3).toNat ∧
      (s.gpr .a5).toNat = (s.gpr .a3).toNat ∧ 1 ≤ (s.gpr .a7).toNat ∧
      (s.gpr .a7).toNat < (s.gpr .a3).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .a3).toNat ∧ (stackArg s 3).toNat = (s.gpr .a7).toNat ∧
      (stackArg s 7).toNat = (s.gpr .a7).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a3).toNat ≤ (stackArg s 9).toNat ∧
      (stackArg s 8).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .a7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .a7).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat

/-- The working space. -/
abbrev cS (s : State) : Addr := stackArg s 8
/-- Its size in bytes. -/
abbrev cZ (s : State) : Nat := (stackArg s 9).toNat * 8
/-- `k`. -/
abbrev ck (s : State) : Nat := (s.gpr .a3).toNat
/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * ((ck s + 7) / 8)
/-- `p`'s length. -/
abbrev cpL (s : State) : Nat := (s.gpr .a7).toNat
/-- `q`'s length. -/
abbrev cqL (s : State) : Nat := (stackArg s 1).toNat

theorem wordsOf_le {l : Nat} : wordsOf l ≤ (l + 7) / 8 + 2 := by unfold wordsOf; split <;> omega_arith

theorem two_le_wordsOf {l : Nat} : 2 ≤ wordsOf l := by unfold wordsOf; split <;> omega_arith

theorem wordsOf_ge {l : Nat} : (l + 7) / 8 ≤ wordsOf l := by unfold wordsOf; split <;> omega_arith

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wordsOf (cpL s₀)) 24 + slot (wordsOf (cqL s₀)) 24 ≤ cZ s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  al : (cS s₀).toNat % 8 = 0
  out : ∀ i < ck s₀, InRegions s₀.wr (off (s₀.gpr .a0) i) 1
  nwO : (s₀.gpr .a0).toNat + ck s₀ ≤ 2 ^ 64
  sepO : ∀ x, ofs (s₀.gpr .a0) x < ck s₀ → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a2) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a2) i ≠ x
  rI : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a4) i) 1
  sI : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a4) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a6) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a6) i ≠ x
  rQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 0) i) 1
  sQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 0) i ≠ x
  rDP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 2) i) 1
  sDP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 2) i ≠ x
  rDQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 4) i) 1
  sDQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 4) i ≠ x
  rQI : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (stackArg s₀ 6) i) 1
  sQI : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (stackArg s₀ 6) i ≠ x

theorem rd_of_mem {s : State} {A : Addr} {L n : Nat} (h : (⟨A, L⟩ : Region) ∈ s.rd) (hn : n ≤ L)
    (hL : L < 2 ^ 64) :
    ∀ i < n, InRegions (s.rd ++ s.wr) (off A i) 1 := fun i hi =>
  ⟨_, List.mem_append_left _ h, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := by
  obtain ⟨hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have wp := wordsOf_le (l := (s₀.gpr .a7).toNat)
  have wq := wordsOf_le (l := (stackArg s₀ 1).toNat)
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, nwS, alS,
    fun i hi => ⟨⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩, by rw [hwr]; simp,
      Offset.contains_base _ (by change i < (s₀.gpr .a3).toNat at hi; omega_arith)
        (by change i < (s₀.gpr .a3).toNat at hi; omega_arith)⟩,
    by show (s₀.gpr .a0).toNat + (s₀.gpr .a3).toNat ≤ 2 ^ 64; rw [← hOL]; exact nwO,
    fun x hx => Pub.sep_of_disjoint dOS x (by rw [hOL]; exact hx),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dNS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (s₀.gpr .a5).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hIL.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .a3).toNat at hi; omega_arith),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dPS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dQS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (stackArg s₀ 3).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hdpl.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDPS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .a7).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 5).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hdql.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDQS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (stackArg s₀ 1).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 7).toNat) (by rw [hrd]; simp) (Nat.le_of_eq hqil.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dQIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .a7).toNat at hi; omega_arith)⟩
  show slot (2 * (((s₀.gpr .a3).toNat + 7) / 8)) 8 + slot (wordsOf (s₀.gpr .a7).toNat) 24 +
    slot (wordsOf (stackArg s₀ 1).toNat) 24 ≤ (stackArg s₀ 9).toNat * 8
  unfold slot hdrBytes; omega_arith

/-! ## The front: `save`, `args`, `setupX` -/

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t0, .s6, .t2, .t3, .t4, .t5, .a7, .ra, .s5, .s11]

/-- What holds after the front, from the entry state `s₀`. -/
structure Front (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = Mont.off (s₀.gpr .a2) 0
  hNL : Mont.word s.mem (cS s₀) oNLen = BitVec.ofNat 64 (ck s₀)
  hIn : Mont.word s.mem (cS s₀) oIn = Mont.off (s₀.gpr .a4) 0
  hP : Mont.word s.mem (cS s₀) oP = Mont.off (s₀.gpr .a6) 0
  hPL : Mont.word s.mem (cS s₀) oPLen = BitVec.ofNat 64 (cpL s₀)
  hQ : Mont.word s.mem (cS s₀) oQ = Mont.off (stackArg s₀ 0) 0
  hQL : Mont.word s.mem (cS s₀) oQLen = BitVec.ofNat 64 (cqL s₀)
  hDP : Mont.word s.mem (cS s₀) oDP = stackArg s₀ 2
  hDQ : Mont.word s.mem (cS s₀) oDQ = stackArg s₀ 4
  hQI : Mont.word s.mem (cS s₀) oQInv = Mont.off (stackArg s₀ 6) 0
  hBP : Mont.word s.mem (cS s₀) oBP = Mont.off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ = Mont.off (cS s₀) (slot (cwX s₀) 8 + slot (wordsOf (cpL s₀)) 24)
  s6 : s.gpr .s6 = cS s₀
  a7 : s.gpr .a7 = Mont.off (cS s₀) (slot (cwX s₀) 0)
  ra : s.gpr .ra = Mont.off (cS s₀) (slot (cwX s₀) 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 (cwX s₀)
  keep : Keep frontRegs s₀ s
  sav : ∀ i < 13, s.mem.readW (Mont.off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  mem : Mont.Outside (cS s₀) 0 256 s₀.mem s.mem

theorem frame_sub {m m' : Mem} {B : Addr} {o n : Nat} (h : Frame [⟨Mont.off B o, n⟩] m m')
    (ho : o + n ≤ 2 ^ 64) : Mont.Outside B o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  change (x - (B + BitVec.ofNat 64 o)).toNat + 1 ≤ n at hc
  have := (Offset.lt_iff x B (d := o) (n := n) ho).mp (by omega_arith)
  change (x - B).toNat < o ∨ o + n ≤ (x - B).toNat at hx
  omega_arith

theorem z0 (x : Addr) : x = Mont.off x 0 := (BitVec.add_zero x).symm

theorem ofNat_toNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := (VG.Proof.Bignum.ofNat_toNat64 _).symm

theorem front_ok (s₀ : State) (h : fnContract.pre s₀) :
    WP isa (.block (Crt.save ++ Crt.args ++ setupX)) s₀ (Front s₀) := by
  have hP := pre_facts h
  obtain ⟨hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hscr : Scr s₀ (cS s₀) (cZ s₀) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hn := hscr.nowrap
  have alS' : (cS s₀).toNat % 8 = 0 := alS
  have dk : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .a3).toNat + 256 ≤ (stackArg s₀ 9).toNat * 8; omega_arith
  have hargs : stackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  -- The stack arguments' region does not wrap (it is apart from the scratch).
  have sa : ∀ i, stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := fun i => by
    simp only [stackArgAddr]; rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have hst : ∀ i < 10, InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8 := fun i hi =>
    ⟨_, List.mem_append_left _ hargs, by rw [sa i]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsavR : ∀ i < 13, (⟨cS s₀, cZ s₀⟩ : Region).Contains (Mont.off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    show Region.Contains _ (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hsal : ∀ i < 13, (Mont.off (savW (cS s₀)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    show (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ rfl (hst 8 (by decide)) (by omega_arith)
    (fun i hi => ⟨_, by rw [hwr]; simp, hsavR i hi⟩) hsal) fun t hSv => ?_
  have kt := hSv.keep
  have t6 : t.gpr .s6 = cS s₀ := hSv.s6
  have tsp : ∀ i, stackArgAddr t i = stackArgAddr s₀ i := fun i => by simp only [stackArgAddr, hSv.sp]
  have savSub : Region.Sub (savR (savW (cS s₀))) ⟨cS s₀, cZ s₀⟩ := by
    show Region.Sub ⟨cS s₀ + BitVec.ofNat 64 112, 104⟩ _
    exact Offset.sub_base _ (by omega_arith)
  have tst : ∀ i < 10, stackArg t i = stackArg s₀ i := fun i hi => by
    simp only [stackArg, tsp]
    refine hSv.frame.readW (r := ⟨stackArgAddr s₀ i, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr
    subst hr
    have argSub : Region.Sub ⟨stackArgAddr s₀ i, 8⟩ (stackArgs s₀) := by
      rw [sa i]; exact Offset.sub_base _ (by omega_arith)
    exact (dSA.symm.sub_left argSub).sub_right savSub
  have hsep : ∀ j < 56, ∀ d < 88, Mem.Sep (t.sp + BitVec.ofNat 64 j) 8 (Mont.off (cS s₀) d) 8 :=
    fun j hj d hd x hx hy => by
      rw [hSv.sp] at hx
      have h1 := (Offset.lt_iff x s₀.sp (d := j) (n := 8) (by omega_arith)).mp hx
      have h2 := (Offset.lt_iff x (cS s₀) (d := d) (n := 8) (by omega_arith)).mp hy
      refine dSA x ?_ ?_
      · show (x - cS s₀).toNat + 1 ≤ (stackArg s₀ 9).toNat * 8; omega_arith
      · show (x - (s₀.sp + BitVec.ofNat 64 (8 * 0))).toNat + 1 ≤ 80
        rw [show 8 * 0 = 0 from rfl, BitVec.add_zero]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (args_ok (hscr.congr kt.2.2) (by omega_arith) (by rw [t6]; exact z0 _)
    (by rw [hSv.sp]; omega_arith) (fun i hi => by rw [tsp, kt.2.1, kt.2.2]; exact hst i (by omega_arith)) hsep)
    fun u ⟨⟨A, Ou⟩, ku⟩ => ?_
  have ktu := kt.trans ku
  have u6 : u.gpr .s6 = cS s₀ := (ku.gpr (by decide)).trans t6
  refine WP.mono (setupX_ok (k := ck s₀) (pl := cpL s₀) (hscr.congr ktu.2.2) (by omega_arith)
    (by rw [u6]; exact z0 _) (by rw [ktu.gpr (by decide)]; exact ofNat_toNat _) (by rw [dk]; omega_arith) hk'
    (by rw [A.pLen, kt.gpr (by decide)]; exact ofNat_toNat _) hp1 (by show (s₀.gpr .a7).toNat ≤ 1024; omega_arith))
    fun v ⟨⟨v7, vra, v5, v11, v0, vBP, vBQ, Ov⟩, kv⟩ => ?_
  have k := ktu.trans kv
  have hw : ∀ d, d + 8 ≤ 96 → Mont.word v.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd =>
    Ov.word (Or.inl hd) (by omega_arith)
  refine ⟨hscr.congr k.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vBP, ?_,
    (kv.gpr (by decide)).trans u6, v7, vra, v5, v11, v0, k.mono (by decide), fun i hi => ?_, ?_⟩
  · rw [hw _ (by decide), A.out, kt.gpr (by decide)]
  · rw [hw _ (by decide), A.n, kt.gpr (by decide)]; exact z0 _
  · rw [hw _ (by decide), A.nLen, kt.gpr (by decide)]; exact ofNat_toNat _
  · rw [hw _ (by decide), A.inp, kt.gpr (by decide)]; exact z0 _
  · rw [hw _ (by decide), A.p, kt.gpr (by decide)]; exact z0 _
  · rw [hw _ (by decide), A.pLen, kt.gpr (by decide)]; exact ofNat_toNat _
  · rw [hw _ (by decide), A.q, tst 0 (by decide)]; exact z0 _
  · rw [hw _ (by decide), A.qLen, tst 1 (by decide)]; exact ofNat_toNat _
  · rw [hw _ (by decide), A.dp, tst 2 (by decide)]
  · rw [hw _ (by decide), A.dq, tst 4 (by decide)]
  · rw [hw _ (by decide), A.qinv, tst 6 (by decide)]; exact z0 _
  · rw [vBQ]; exact congrArg _ (by unfold slot; omega_arith)
  · have hs1 := hSv.saved i hi
    change t.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _ at hs1
    change v.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [Offset.add_add] at hs1 ⊢
    have h1 := Ov.word (d := 112 + 8 * i) (Or.inr (by unfold oBP; omega_arith)) (by omega_arith)
    have h2 := Ou.word (d := 112 + 8 * i) (Or.inr (by omega_arith)) (by omega_arith)
    simp only [Mont.word, Mont.off] at h1 h2
    rw [h1, h2]; exact hs1
  · have fr : Frame [⟨Mont.off (cS s₀) 112, 104⟩] s₀.mem t.mem := hSv.frame
    exact (((frame_sub fr (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      (Ou.mono (by omega_arith) (by omega_arith))).trans (Ov.mono (by omega_arith) (by unfold oBP; omega_arith))

end VG.Proof.Bignum.RISCV64.Crt
