module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PrivPre
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtArgs
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Framework.Offset

/-!
# An RSA private key's precomputed values on PPC64LE: the front

`fnContract`: `vg_rsa_private_precompute(pre = r3, pre_len = r4, n = r5,
n_len = r6, p = r7, p_len = r8, q = r9, q_len = r10, scratch, scratch_len)`,
the last two on the stack, on the registers and the stack. `front_ok`: the
nonvolatile registers saved in the working space's header, the arguments in
it, and `Precompute.core`'s registers (`Front`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE


/-- `pre`, `pre_len` words at `r3`. -/
abbrev preR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
/-- `n`, `n_len` bytes at `r5`. -/
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
/-- `p`, `p_len` bytes at `r7`. -/
abbrev pR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
/-- `q`, `q_len` bytes at `r9`. -/
abbrev qR (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
/-- The working space, `scratch_len` words. -/
abbrev scrR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
/-- The arguments on the stack. -/
abbrev argsR (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The bytes of `n`, `p` and `q`. -/
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
abbrev pB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
abbrev qB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat

/-- `vg_rsa_private_precompute`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧
      s.rd = [nR s, pR s, qR s, argsR s] ∧ s.wr = [preR s, scrR s] ∧
      (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (pR s) ∧ (preR s).Disjoint (qR s) ∧
      (preR s).Disjoint (scrR s) ∧ (preR s).Disjoint (argsR s) ∧
      (nR s).Disjoint (scrR s) ∧ (pR s).Disjoint (scrR s) ∧ (qR s).Disjoint (scrR s) ∧
      (scrR s).Disjoint (argsR s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r6).toNat ∧ 1 ≤ (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat < (s.gpr .r6).toNat ∧
      1 ≤ (s.gpr .r10).toNat ∧ (s.gpr .r10).toNat < (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .r6).toNat (s.gpr .r8).toNat
        (s.gpr .r10).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r6).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    match Spec.Rsa.privatePrecompute (nB s) (pB s) (qB s) with
    | some ws => (s'.gpr .r3).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .r3) (s.gpr .r4).toNat = ws
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .r3) (s.gpr .r4).toNat = List.replicate (s.gpr .r4).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 2).map (stackArg s₁) = (List.range 2).map (stackArg s₂) ∧ nB s₁ = nB s₂

/-- The working space. -/
abbrev cS (s : State) : Addr := stackArg s 0
/-- Its size in bytes. -/
abbrev cZ (s : State) : Nat := (stackArg s 1).toNat * 8
/-- `k`. -/
abbrev ck (s : State) : Nat := (s.gpr .r6).toNat
/-- `n`'s words. -/
abbrev cw (s : State) : Nat := (ck s + 7) / 8

/-- The first argument on the stack into `r11`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r11 .r11 0]) s fun t =>
      (t.gpr .r11 = stackArg s 0 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- `save`: the working space from the stack, the registers saved there. -/
theorem save_ok (s₀ : State) (h : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8)
    (hin : ∀ i < 18, InRegions s₀.wr (off (Crt.savW (stackArg s₀ 0)) (8 * i)) 8) :
    WP isa (.block PrivPre.save) s₀ fun t => ∃ s₁ : State, s₁.gpr .r11 = stackArg s₀ 0 ∧ s₁.mem = s₀.mem ∧
      Keep [.r11] s₀ s₁ ∧ Crt.Saved s₁ t := by
  rw [PrivPre.save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadS_ok s₀ h) fun s₁ ⟨⟨a11, m1, _⟩, k1⟩ => ?_
  refine WP.mono (Crt.saveRegs_ok s₁ (fun i hi => by rw [k1.wr, a11]; exact hin i hi)) fun t ht =>
    ⟨s₁, a11, m1, k1, ht⟩

/-- `args`, after `save` (the working space at `S` in `r23`): the arguments
into the header. -/
theorem args_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 256 ≤ Z) (h23 : s.gpr .r23 = S) :
    WP isa (.block PrivPre.args) s fun t =>
      (word t.mem S oOut = s.gpr .r3 ∧ word t.mem S oN = s.gpr .r5 ∧ word t.mem S oNLen = s.gpr .r6 ∧
        word t.mem S oIn = s.gpr .r3 ∧ word t.mem S oP = s.gpr .r7 ∧ word t.mem S oPLen = s.gpr .r8 ∧
        word t.mem S oQ = s.gpr .r9 ∧ word t.mem S oQLen = s.gpr .r10 ∧ word t.mem S oQInv = s.gpr .r3 ∧
        Outside S 0 88 s.mem t.mem) ∧ Keep [] s t := by
  have hn := hs.nowrap
  have step : ∀ {t : State} {o : Nat} {r : Reg}, Scr t S Z → t.gpr .r23 = S → o + 8 ≤ 88 → o % 8 = 0 →
      WP isa (.block [.store .d r .r23 o]) t fun u =>
        (word u.mem S o = t.gpr r ∧ Outside S o 8 t.mem u.mem) ∧ Keep [] t u :=
    fun ht h23 ho ho' => Crt.st1_ok ht h23 (by omega_arith) (by omega_arith)
  have kw : ∀ {m m' : Mem} {o d : Nat}, Outside S o 8 m m' → d + 8 ≤ o ∨ o + 8 ≤ d → d + 8 ≤ 88 →
      word m' S d = word m S d := fun h hd hd' => h.word hd (by omega_arith)
  rw [show PrivPre.args = [.store .d .r3 .r23 0] ++ ([.store .d .r5 .r23 8] ++ ([.store .d .r6 .r23 16] ++ ([.store .d .r3 .r23 24] ++ ([.store .d .r7 .r23 32] ++ ([.store .d .r8 .r23 40] ++ ([.store .d .r9 .r23 48] ++ ([.store .d .r10 .r23 56] ++ [.store .d .r3 .r23 80]))))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s) (o := 0) (r := .r3) hs h23 (by decide) (by decide))
    fun s1 ⟨⟨w1, F1⟩, j1⟩ => ?_
  have k1 := j1
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s1) (o := 8) (r := .r5) (hs.congr k1.wr) ((k1.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s2 ⟨⟨w2, F2⟩, j2⟩ => ?_
  have k2 := k1.trans j2
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s2) (o := 16) (r := .r6) (hs.congr k2.wr) ((k2.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s3 ⟨⟨w3, F3⟩, j3⟩ => ?_
  have k3 := k2.trans j3
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s3) (o := 24) (r := .r3) (hs.congr k3.wr) ((k3.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s4 ⟨⟨w4, F4⟩, j4⟩ => ?_
  have k4 := k3.trans j4
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s4) (o := 32) (r := .r7) (hs.congr k4.wr) ((k4.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s5 ⟨⟨w5, F5⟩, j5⟩ => ?_
  have k5 := k4.trans j5
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s5) (o := 40) (r := .r8) (hs.congr k5.wr) ((k5.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s6 ⟨⟨w6, F6⟩, j6⟩ => ?_
  have k6 := k5.trans j6
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s6) (o := 48) (r := .r9) (hs.congr k6.wr) ((k6.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s7 ⟨⟨w7, F7⟩, j7⟩ => ?_
  have k7 := k6.trans j7
  rw [WP.block_append_iff]
  refine WP.mono (step (t := s7) (o := 56) (r := .r10) (hs.congr k7.wr) ((k7.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s8 ⟨⟨w8, F8⟩, j8⟩ => ?_
  have k8 := k7.trans j8
  refine WP.mono (step (t := s8) (o := 80) (r := .r3) (hs.congr k8.wr) ((k8.gpr _ (by simp)).trans h23) (by decide) (by decide))
    fun s9 ⟨⟨w9, F9⟩, j9⟩ => ?_
  have k9 := k8.trans j9
  simp only [oOut, oN, oNLen, oIn, oP, oPLen, oQ, oQLen, oQInv]
  refine ⟨⟨by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), kw F6 (by decide) (by decide), kw F5 (by decide) (by decide), kw F4 (by decide) (by decide), kw F3 (by decide) (by decide), kw F2 (by decide) (by decide), w1], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), kw F6 (by decide) (by decide), kw F5 (by decide) (by decide), kw F4 (by decide) (by decide), kw F3 (by decide) (by decide), w2, k1.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), kw F6 (by decide) (by decide), kw F5 (by decide) (by decide), kw F4 (by decide) (by decide), w3, k2.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), kw F6 (by decide) (by decide), kw F5 (by decide) (by decide), w4, k3.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), kw F6 (by decide) (by decide), w5, k4.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), kw F7 (by decide) (by decide), w6, k5.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), kw F8 (by decide) (by decide), w7, k6.gpr _ (by simp)], by rw [kw F9 (by decide) (by decide), w8, k7.gpr _ (by simp)], by rw [ w9, k8.gpr _ (by simp)], ?_⟩, k9.mono⟩
  exact ((((((((F1.mono (by decide) (by decide)).trans (F2.mono (by decide) (by decide))).trans (F3.mono (by decide) (by decide))).trans (F4.mono (by decide) (by decide))).trans (F5.mono (by decide) (by decide))).trans (F6.mono (by decide) (by decide))).trans (F7.mono (by decide) (by decide))).trans (F8.mono (by decide) (by decide))).trans (F9.mono (by decide) (by decide))

end VG.Proof.Bignum.PPC64LE.PrivPre
