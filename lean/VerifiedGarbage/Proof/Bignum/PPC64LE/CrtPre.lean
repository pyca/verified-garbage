module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtArgs
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute

/-! ### `Bignum.PPC64LE.CrtFront`, which this module and modules that import it used -/

section

/-! ### `Bignum.PPC64LE.CrtFn`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: the function

`vg_rsa_private_crt(out = r3, out_len = r4, n = r5, n_len = r6, input = r7,
input_len = r8, p = r9, p_len = r10, q, q_len, dp, dp_len, dq, dq_len,
qinv, qinv_len, scratch, scratch_len)`, the last ten on the stack
(`fnContract`); `vg_rsa_private_crt_precomputed`, which also takes the
primes' cached `R² mod p` and `R² mod q` in `r31` (`fnContractP`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE

/-- The regions `vg_rsa_private_crt` reads. -/
def baseRd (s : State) : List Region :=
  [⟨s.gpr .r5, (s.gpr .r6).toNat⟩, ⟨s.gpr .r7, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (s.gpr .r10).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArgAddr s 0, 80⟩]

/-- `vg_rsa_private_crt`'s precondition, with the regions it reads `rd`. -/
def preCore (rd : List Region) (s : State) : Prop :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let n : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let inp : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let p : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64 ∧
      s.rd = rd ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r6).toNat ∧ (s.gpr .r4).toNat = (s.gpr .r6).toNat ∧
      (s.gpr .r8).toNat = (s.gpr .r6).toNat ∧ 1 ≤ (s.gpr .r10).toNat ∧
      (s.gpr .r10).toNat < (s.gpr .r6).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .r6).toNat ∧ (stackArg s 3).toNat = (s.gpr .r10).toNat ∧
      (stackArg s 7).toNat = (s.gpr .r10).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 9).toNat

/-- `vg_rsa_private_crt`'s result. -/
def postCore (s s' : State) : Prop :=
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r10).toNat))

/-- `vg_rsa_private_crt`'s public data. -/
def pubCore (s₁ s₂ : State) : Prop :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat

/-- `vg_rsa_private_crt`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s := preCore (baseRd s) s
  post := postCore
  pub := pubCore

/-- `fnContract.pre` as `preCore` with no regions but `baseRd`'s. -/
theorem preCore_nil {s : State} (h : fnContract.pre s) : preCore (baseRd s ++ []) s := by
  rw [List.append_nil]; exact h

/-- The cached `R² mod p` and `R² mod q` of `vg_rsa_private_crt_precomputed`,
at `r31`: `max(2, ⌈len / 8⌉)` words each. -/
def r2R (s : State) : Region :=
  ⟨s.gpr .r31, 8 * (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat)⟩

/-- `vg_rsa_private_crt_precomputed`, which takes in `r31` the address of
the primes' `R² mod p` and `R² mod q` (`Spec.Rsa.primeR2`), and computes
what `vg_rsa_private_crt` does. -/
def fnContractP : Contract isa where
  pre s := preCore (baseRd s ++ [r2R s]) s ∧ (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint (r2R s) ∧
    (r2R s).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩ ∧ (s.gpr .r31).toNat + (r2R s).len ≤ 2 ^ 64 ∧
    Spec.Rsa.wordsAt s.mem (s.gpr .r31) (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat) =
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) ++
        Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  post := postCore
  pub s₁ s₂ := pubCore s₁ s₂ ∧ s₁.gpr .r31 = s₂.gpr .r31

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: the front

`front_ok`: `save`, `args` and `setupX`: the nonvolatile registers saved,
the arguments in the header and `X`'s registers (`Front`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The working space. -/
abbrev cS (s : State) : Addr := stackArg s 8
/-- Its size in bytes. -/
abbrev cZ (s : State) : Nat := (stackArg s 9).toNat * 8
/-- `k`. -/
abbrev ck (s : State) : Nat := (s.gpr .r6).toNat
/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * ((ck s + 7) / 8)
/-- `p`'s length. -/
abbrev cpL (s : State) : Nat := (s.gpr .r10).toNat
/-- `q`'s length. -/
abbrev cqL (s : State) : Nat := (stackArg s 1).toNat

/-- The registers the front writes. -/
def frontRegs : List Reg := [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r23, .r27, .r28, .r29]

/-- What holds after the front, from the entry state `s₀`. -/
structure Front (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = off (s₀.gpr .r3) 0
  hN : word s.mem (cS s₀) oN = off (s₀.gpr .r5) 0
  hNL : word s.mem (cS s₀) oNLen = BitVec.ofNat 64 (ck s₀)
  hIn : word s.mem (cS s₀) oIn = off (s₀.gpr .r7) 0
  hP : word s.mem (cS s₀) oP = off (s₀.gpr .r9) 0
  hPL : word s.mem (cS s₀) oPLen = BitVec.ofNat 64 (cpL s₀)
  hQ : word s.mem (cS s₀) oQ = off (stackArg s₀ 0) 0
  hQL : word s.mem (cS s₀) oQLen = BitVec.ofNat 64 (cqL s₀)
  hDP : word s.mem (cS s₀) oDP = off (stackArg s₀ 2) 0
  hDQ : word s.mem (cS s₀) oDQ = off (stackArg s₀ 4) 0
  hQI : word s.mem (cS s₀) oQInv = off (stackArg s₀ 6) 0
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24)
  r23 : s.gpr .r23 = cS s₀
  r10 : s.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0)
  r21 : s.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  keep : Keep frontRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  mem : Outside (cS s₀) 0 256 s₀.mem s.mem

theorem frame_sub {m m' : Mem} {B : Addr} {o n : Nat} (h : Frame [⟨off B o, n⟩] m m') (ho : o + n ≤ 2 ^ 64)
    (hn : 0 < n) :
    Outside B o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  obtain e := ofs_rebase B x (o := o) (by omega_arith)
  change ofs (off B o) x + 1 ≤ n at hc
  change ofs B x < o ∨ o + n ≤ ofs B x at hx
  rcases e with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith

theorem saved_ne11 : ∀ i < 18, Crt.saved i ≠ .r11 := by decide

/-- The front of `crtG pc`, and with `pc` the cached values' address in the
header. -/
theorem front_okG (pc : Bool) {X : List Region} (s₀ : State) (h : preCore (baseRd s₀ ++ X) s₀) :
    WP isa (.block (Crt.save ++ argsG pc ++ setupX)) s₀ fun s =>
      Front s₀ s ∧ (pc = true → word s.mem (cS s₀) oR2 = s₀.gpr .r31) := by
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  obtain hk1 := (s₀.gpr .r6).isLt
  obtain hscr : Scr s₀ (cS s₀) (cZ s₀) := Scr.of_mem (by rw [hwr]; simp) nwS
  have hn := hscr.nowrap
  obtain hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .r6).toNat + 256 ≤ (stackArg s₀ 9).toNat * 8; omega_arith
  obtain hargs : (⟨stackArgAddr s₀ 0, 80⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [baseRd]
  obtain sa : ∀ i, stackArgAddr s₀ i = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := fun i => by
    simp only [stackArgAddr]; rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain hst : ∀ i < 10, InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ i) 8 := fun i hi =>
    ⟨_, List.mem_append_left _ hargs, by rw [sa i]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hsep : ∀ j < 10, ∀ i < 8, ∀ x, ofs (cS s₀) x < cZ s₀ → stackArgAddr s₀ j + BitVec.ofNat 64 i ≠ x :=
    fun j hj i hi x hx e => by
      subst e
      refine dSA _ (by
        change ((stackArgAddr s₀ j + BitVec.ofNat 64 i) - cS s₀).toNat + 1 ≤ cZ s₀
        change ((stackArgAddr s₀ j + BitVec.ofNat 64 i) - cS s₀).toNat < cZ s₀ at hx; omega_arith) ?_
      rw [sa j, Offset.add_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hsavR : ∀ i < 18, (⟨cS s₀, cZ s₀⟩ : Region).Contains (off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ (hst 8 (by decide)) fun i hi => ⟨_, by rw [hwr]; simp, hsavR i hi⟩)
    fun t ⟨s₁, a11, m1, k1, hSv⟩ => ?_
  obtain kt := k1.trans hSv.keep
  obtain t23 : t.gpr .r23 = cS s₀ := hSv.r23.trans a11
  obtain tsp : ∀ i, stackArgAddr t i = stackArgAddr s₀ i := fun i => by simp only [stackArgAddr, kt.sp]
  obtain fr : Frame [savR (savW (cS s₀))] s₀.mem t.mem := by
    have := hSv.frame; rw [a11, m1] at this; exact this
  obtain savSub : Region.Sub (savR (savW (cS s₀))) ⟨cS s₀, cZ s₀⟩ := Offset.sub_base _ (by omega_arith)
  obtain tst : ∀ i < 10, stackArg t i = stackArg s₀ i := fun i hi => by
    simp only [stackArg, tsp]
    refine fr.readW (r := ⟨stackArgAddr s₀ i, 8⟩) (by simp [Region.Contains]) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr
    subst hr
    obtain argSub : Region.Sub ⟨stackArgAddr s₀ i, 8⟩ ⟨stackArgAddr s₀ 0, 80⟩ := by
      rw [sa i]; exact Offset.sub_base _ (by omega_arith)
    exact (dSA.symm.sub_left argSub).sub_right savSub
  rw [WP.block_append_iff]
  refine WP.mono (argsG_ok (pc := pc) (hscr.congr kt.wr) (by omega_arith) t23
    (fun i hi => by rw [tsp, kt.rd, kt.wr]; exact hst i hi)
    (fun j hj i hi x hx => by rw [tsp]; exact hsep j hj i hi x hx))
    fun u ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, Ou, w12⟩, ku⟩ => ?_
  obtain ktu := kt.trans ku
  refine WP.mono (setupX_ok (k := ck s₀) (pL := cpL s₀) (hscr.congr ktu.wr) (by omega_arith) ((ku.gpr _ (by decide)).trans t23)
    (by rw [ktu.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm) hk'
    (by rw [w5, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm) hp1
    (by show (s₀.gpr .r10).toNat < 2 ^ 60; omega_arith))
    fun v ⟨⟨v10, v21, v29, v11, v27, v28, vBP, vBQ, Ov⟩, kv⟩ => ?_
  obtain k := ktu.trans kv
  obtain hw : ∀ d, d + 8 ≤ 96 → word v.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd =>
    Ov.word (Or.inl hd) (by omega_arith)
  obtain z : ∀ x : Addr, x = off x 0 := fun x => (BitVec.add_zero x).symm
  refine ⟨⟨hscr.congr k.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vBP, vBQ, (kv.gpr _ (by decide)).trans
    ((ku.gpr _ (by decide)).trans t23), v10, v21, v29, v11, v27, v28, k.mono, fun i hi => ?_, ?_⟩,
    fun hp => by rw [hw _ (by decide), w12 hp, kt.gpr _ (by decide)]⟩
  · rw [hw _ (by decide), w0, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w1, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w2, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w3, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w4, kt.gpr _ (by decide)]; exact z _
  · rw [hw _ (by decide), w5, kt.gpr _ (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w6, tst 0 (by decide)]; exact z _
  · rw [hw _ (by decide), w7, tst 1 (by decide)]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · rw [hw _ (by decide), w8, tst 2 (by decide)]; exact z _
  · rw [hw _ (by decide), w9, tst 4 (by decide)]; exact z _
  · rw [hw _ (by decide), w10, tst 6 (by decide)]; exact z _
  · have hs1 := hSv.saved i hi
    rw [a11, k1.gpr _ (fun h => saved_ne11 i hi (List.mem_singleton.mp h))] at hs1
    change t.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _ at hs1
    change v.mem.readW (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [Offset.add_add] at hs1 ⊢
    obtain h1 := Ov.word (d := 112 + 8 * i) (Or.inr (by omega_arith)) (by omega_arith)
    obtain h2 := Ou.word (d := 112 + 8 * i) (Or.inr (by omega_arith)) (by omega_arith)
    simp only [word] at h1 h2
    rw [h1, h2]; exact hs1
  · exact (((frame_sub (o := 112) fr (by omega_arith) (by decide)).mono (by omega_arith) (by omega_arith)).trans
      (Ou.mono (by omega_arith) (by omega_arith))).trans (Ov.mono (by omega_arith) (by omega_arith))

theorem front_ok (s₀ : State) (h : fnContract.pre s₀) :
    WP isa (.block (Crt.save ++ Crt.args ++ setupX)) s₀ (Front s₀) :=
  WP.mono (front_okG false s₀ (preCore_nil h)) fun _ h => h.1

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: what the precondition gives

`pre_facts`: from `fnContract.pre`, the lengths, the layout of the three
working spaces in the scratch, and that each buffer is readable and apart
from the scratch (`PF`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24 + slot (wsWords (cqL s₀)) 24 ≤ cZ s₀
  pq : wsWords (cpL s₀) + wsWords (cqL s₀) ≤ cwX s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  out : Scr s₀ (s₀.gpr .r3) (ck s₀)
  sepO : ∀ x, ofs (s₀.gpr .r3) x < ck s₀ → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r5) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r5) i ≠ x
  rI : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r7) i) 1
  sI : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r7) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r9) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .r9) i ≠ x
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

theorem pre_factsG {X : List Region} {s₀ : State} (h : preCore (baseRd s₀ ++ X) s₀) : PF s₀ := by
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, ?_, nwS, Scr.of_mem (by rw [hwr, hOL]; simp)
    (by show (s₀.gpr .r3).toNat + (s₀.gpr .r6).toNat ≤ 2 ^ 64; rw [← hOL]; exact nwO),
    fun x hx => Pub.sep_of_disjoint dOS x (by rw [hOL]; exact hx),
    rd_of_mem (by rw [hrd]; simp [baseRd]) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dNS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (s₀.gpr .r8).toNat) (by rw [hrd]; simp [baseRd]) (Nat.le_of_eq hIL.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r6).toNat at hi; omega_arith),
    rd_of_mem (by rw [hrd]; simp [baseRd]) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dPS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (by rw [hrd]; simp [baseRd]) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dQS (Nat.le_of_lt (BitVec.isLt _)),
    rd_of_mem (L := (stackArg s₀ 3).toNat) (by rw [hrd]; simp [baseRd]) (Nat.le_of_eq hdpl.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDPS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r10).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 5).toNat) (by rw [hrd]; simp [baseRd]) (Nat.le_of_eq hdql.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dDQS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (stackArg s₀ 1).toNat at hi; omega_arith),
    rd_of_mem (L := (stackArg s₀ 7).toNat) (by rw [hrd]; simp [baseRd]) (Nat.le_of_eq hqil.symm) (BitVec.isLt _),
    fun i hi => Pub.ne_of_disjoint dQIS (Nat.le_of_lt (BitVec.isLt _)) i (by
      change i < (s₀.gpr .r10).toNat at hi; omega_arith)⟩
  · show slot (2 * (((s₀.gpr .r6).toNat + 7) / 8)) 8 + slot (wsWords (s₀.gpr .r10).toNat) 24 +
      slot (wsWords (stackArg s₀ 1).toNat) 24 ≤ (stackArg s₀ 9).toNat * 8
    unfold slot wsWords hdrBytes; omega_arith
  · show wsWords (s₀.gpr .r10).toNat + wsWords (stackArg s₀ 1).toNat ≤ 2 * (((s₀.gpr .r6).toNat + 7) / 8)
    unfold wsWords; omega_arith

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := pre_factsG (preCore_nil h)

end VG.Proof.Bignum.PPC64LE.Crt
