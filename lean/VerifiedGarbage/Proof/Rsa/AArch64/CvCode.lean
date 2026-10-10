import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Bignum.AArch64.HdrPairs
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-!
# `vg_rsa_crt_values` on AArch64: correctness

`CrtValues.code`, from a state its contract allows, writes `crtKey` of its
inputs (`cvCode_correct`), against `cvA`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_crt_values(dp = x0, dp_len = x1, dq = x2, dq_len = x3,
qinv = x4, qinv_len = x5, n = x6, n_len = x7, p = [sp], p_len = [sp + 8],
q = [sp + 16], q_len = [sp + 24], d = [sp + 32], d_len = [sp + 40],
scratch = [sp + 48], scratch_len = [sp + 56])`. -/
def cvA : Contract isa where
  pre s :=
    let dp : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let dq : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let qi : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let n : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let d : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let scr : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 64⟩
    s.sp.toNat + 64 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, d, args] ∧ s.wr = [dp, dq, qi, scr] ∧
      dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint n ∧ dp.Disjoint p ∧ dp.Disjoint q ∧ dp.Disjoint d ∧
      dp.Disjoint scr ∧ dp.Disjoint args ∧
      dq.Disjoint qi ∧ dq.Disjoint n ∧ dq.Disjoint p ∧ dq.Disjoint q ∧ dq.Disjoint d ∧ dq.Disjoint scr ∧
      dq.Disjoint args ∧
      qi.Disjoint n ∧ qi.Disjoint p ∧ qi.Disjoint q ∧ qi.Disjoint d ∧ qi.Disjoint scr ∧ qi.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x7).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .x7).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .x7).toNat ∧ (s.gpr .x1).toNat = (stackArg s 1).toNat ∧
      (s.gpr .x5).toNat = (stackArg s 1).toNat ∧ (s.gpr .x3).toNat = (stackArg s 3).toNat ∧
      1 ≤ (stackArg s 5).toNat ∧ (stackArg s 5).toNat ≤ (s.gpr .x7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x7).toNat ≤ (stackArg s 7).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .x0, (stackArg s 1).toNat), (s.gpr .x2, (stackArg s 3).toNat),
        (s.gpr .x4, (stackArg s 1).toNat)] ((s'.gpr .x0).setWidth 32)
      ((Spec.Rsa.crtKey (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)).map fun v => [v.1, v.2.1, v.2.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 8).map (stackArg s₁) = (List.range 8).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x6) (s₁.gpr .x7).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x6) (s₂.gpr .x7).toNat

/-! ## The entry -/

theorem cvEntry_eq : entry = ([.ldrSp .x8 48, .str .x .x0 .x8 (8 * sDp), .str .x .x1 .x8 (8 * sPl),
    .str .x .x2 .x8 (8 * sDq), .str .x .x3 .x8 (8 * sQl), .str .x .x4 .x8 (8 * sQi), .str .x .x6 .x8 (8 * Public.sN),
    .str .x .x7 .x8 (8 * Public.sK)] : List Instr) ++
    (hdrPairs [(0, sP), (2, sQ), (4, sD), (5, sDl)] ++ ([mov .x0 .x8, mov .x2 .x6, mov .x3 .x7] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def cvEntryMemA (m : Mem) (B : Addr) (vdp vpl vdq vql vqi vn vk : BitVec 64) : Mem :=
  ((((((m.writeW (off B (8 * sDp)) vdp).writeW (off B (8 * sPl)) vpl).writeW (off B (8 * sDq)) vdq).writeW
    (off B (8 * sQl)) vql).writeW (off B (8 * sQi)) vqi).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk

/-- The header after the entry's stores. -/
def cvEntryMem (m : Mem) (B : Addr) (vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) : Mem :=
  ((((cvEntryMemA m B vdp vpl vdq vql vqi vn vk).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sQ)) vq).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem cvEntryMemA_outside (m : Mem) (B : Addr) (vdp vpl vdq vql vqi vn vk : BitVec 64) :
    Outside B 0 (8 * 32) m (cvEntryMemA m B vdp vpl vdq vql vqi vn vk) := by
  unfold cvEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem cvEntryMem_facts (m : Mem) (B : Addr) (vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) :
    let m' := cvEntryMem m B vdp vpl vdq vql vqi vn vk vp vq vd vdl
    word m' B (8 * sDp) = vdp ∧ word m' B (8 * sPl) = vpl ∧ word m' B (8 * sDq) = vdq ∧
    word m' B (8 * sQl) = vql ∧ word m' B (8 * sQi) = vqi ∧ word m' B (8 * Public.sN) = vn ∧
    word m' B (8 * Public.sK) = vk ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧
    word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' cvEntryMem cvEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, the working space's base
(stack argument 6) in `x0`, and `n` and `n_len` in `x2` and `x3`. -/
theorem cvEntry_ok {s : State} {B : Addr} (hB : stackArg s 6 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 8, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 8, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x6 ∧ t.gpr .x3 = s.gpr .x7 ∧
      word t.mem B (8 * sDp) = s.gpr .x0 ∧ word t.mem B (8 * sPl) = s.gpr .x1 ∧
      word t.mem B (8 * sDq) = s.gpr .x2 ∧ word t.mem B (8 * sQl) = s.gpr .x3 ∧
      word t.mem B (8 * sQi) = s.gpr .x4 ∧ word t.mem B (8 * Public.sN) = s.gpr .x6 ∧
      word t.mem B (8 * Public.sK) = s.gpr .x7 ∧
      word t.mem B (8 * sP) = stackArg s 0 ∧ word t.mem B (8 * sQ) = stackArg s 2 ∧
      word t.mem B (8 * sD) = stackArg s 4 ∧ word t.mem B (8 * sDl) = stackArg s 5 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x2, .x3, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 48) 64 = B := hB
  have ha6 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 48) 8 := ha 6 (by decide)
  have ho : 48 % 8 = 0 ∧ 48 < 32768 := ⟨rfl, by decide⟩
  rw [cvEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = cvEntryMemA s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6)
        (s.gpr .x7)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha6, hB', hdr_enc (show sDp < 32 by decide), hdr_enc (show sPl < 32 by decide),
      hdr_enc (show sDq < 32 by decide), hdr_enc (show sQl < 32 by decide), hdr_enc (show sQi < 32 by decide),
      hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hw sDp (by decide), hw sPl (by decide), hw sDq (by decide), hw sQl (by decide), hw sQi (by decide),
      hw Public.sN (by decide), hw Public.sK (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact cvEntryMemA_outside _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0, .x2, .x3] (Q := fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x6 ∧
      t.gpr .x3 = s.gpr .x7 ∧ t.mem = t₂.mem)
    (by brun [h8₂, k12.gpr .x6 (by decide), k12.gpr .x7 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, h2, h3, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = cvEntryMem s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6)
      (s.gpr .x7) (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 5) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho'⟩ :=
    cvEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x6) (s.gpr .x7)
      (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 5)
  exact ⟨h0, h2, h3, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho', (k12.trans k₃).mono (by decide)⟩

/-! ## The result -/

/-- What `CrtValues.code` leaves, from a valid modulus. -/
theorem cvWritten_of {m : Mem} {dp dq qi : Addr} {x0 : BitVec 64} {nb pb qb db : List Byte} {X : Nat} {c : Bool}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hc : c = decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      Nat.gcd (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = 1))
    (hX : c = true → Spec.Rsa.inverse (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = some X)
    (b1 : Spec.Rsa.bytesAt m qi pb.length = Spec.Rsa.i2osp (if c then X else 0) pb.length)
    (b2 : Spec.Rsa.bytesAt m dp pb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip pb - 1) else 0) pb.length)
    (b3 : Spec.Rsa.bytesAt m dq qb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip qb - 1) else 0) qb.length)
    (hr : x0 = BitVec.ofNat 64 c.toNat) :
    Spec.Rsa.writtenAll m [(dp, pb.length), (dq, qb.length), (qi, pb.length)] (x0.setWidth 32)
      ((Spec.Rsa.crtKey nb pb qb db).map fun v => [v.1, v.2.1, v.2.2]) := by
  simp only [Spec.Rsa.crtKey, hv, true_and]
  rw [hr, setWidth_flag]
  cases c
  · simp only [Bool.false_eq_true, ite_false] at b1 b2 b3
    have hnone : (if Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb then
        (Spec.Rsa.crtValues (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip db)).map
          (fun x => (Spec.Rsa.i2osp x.1 pb.length, Spec.Rsa.i2osp x.2.1 qb.length,
            Spec.Rsa.i2osp x.2.2 pb.length)) else none) = none := by
      split
      · rename_i hpq
        have hg : Nat.gcd (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) ≠ 1 := fun hg =>
          absurd hc (by simp [hpq, hg])
        simp [Spec.Rsa.crtValues, VG.Proof.Rsa.inverse_none hg]
      · rfl
    rw [hnone]
    simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨rfl, by rw [b2, i2osp_zero'], by rw [b3, i2osp_zero'], by rw [b1, i2osp_zero']⟩
  · simp only [ite_true] at b1 b2 b3
    have hpq := (of_decide_eq_true hc.symm).1
    simp only [hpq, ite_true]
    simp only [Spec.Rsa.crtValues, hX rfl, Option.map_some, Spec.Rsa.writtenAll, List.map_cons, List.map_nil]
    exact ⟨trivial, by rw [b2, b3, b1]⟩

theorem bytesAt_zero {m : Mem} {p : Addr} {n : Nat} (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

/-! ## The precondition, as the code uses it -/

theorem stkAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.zero_add]

theorem stkAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stkAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem apart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

/-- The inputs of `main`, from the entry state. -/
def cvIn (s : State) : CvIn where
  B := stackArg s 6
  Z := (stackArg s 7).toNat * 8
  k := (s.gpr .x7).toNat
  pl := (stackArg s 1).toNat
  ql := (stackArg s 3).toNat
  dl := (stackArg s 5).toNat
  pDp := s.gpr .x0
  pDq := s.gpr .x2
  pQi := s.gpr .x4
  pN := s.gpr .x6
  pP := stackArg s 0
  pQ := stackArg s 2
  pD := stackArg s 4
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  pb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  qb := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat
  W := s.wr

/-- What `CrtValues.code` uses of its contract's precondition. -/
structure CvCtx (s : State) : Prop where
  L : CvLens (cvIn s)
  x1 : (s.gpr .x1).toNat = (stackArg s 1).toNat
  x3 : (s.gpr .x3).toNat = (stackArg s 3).toNat
  hs : Scr s (stackArg s 6) ((stackArg s 7).toNat * 8)
  ha : ∀ j < 8, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 8, ∀ m', Outside (stackArg s 6) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x6) (cvIn s).nb
  p : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 0) (cvIn s).pb
  q : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 2) (cvIn s).qb
  d : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 4) (cvIn s).db
  oQi : OutOk s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x4) (stackArg s 1).toNat
  oDp : OutOk s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x0) (stackArg s 1).toNat
  oDq : OutOk s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x2) (stackArg s 3).toNat
  a1 : Apart (s.gpr .x4) (stackArg s 1).toNat (s.gpr .x0) (stackArg s 1).toNat
  a2 : Apart (s.gpr .x4) (stackArg s 1).toNat (s.gpr .x2) (stackArg s 3).toNat
  a3 : Apart (s.gpr .x0) (stackArg s 1).toNat (s.gpr .x2) (stackArg s 3).toNat

theorem cvCtx_of {s : State} (h : cvA.pre s) : CvCtx s := by
  simp only [cvA] at h
  sig_split h
  rename_i hsp hrd hwr d12 d13 d1n d1p d1q d1d d1s d1a d23 d2n d2p d2q d2d d2s d2a d3n d3p d3q d3d
    d3s d3a dns dps dqs dds dsa w1 w2 w3 wN wP wQ wD wS hk hpl1 hpl2 hql1 hql2 hx1 hx5 hx3 hdl1 hdl2
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 6) ((stackArg s 7).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 64⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hx1] at d12 d13 d1n d1p d1q d1d d1s d1a w1
  rw [hx3] at d12 d23 d2n d2p d2q d2d d2s d2a w2
  rw [hx5] at d13 d23 d3n d3p d3q d3d d3s d3a w3
  refine ⟨⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hdl1, hdl2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, bytesAt_length _ _ _, by simp only [cvIn]; omega⟩, hx1, hx3, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 64) (by omega) (by omega))
      rw [← stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hx1, hx3, hx5]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d3s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hx1, hx3, hx5]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d1s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hx1, hx3, hx5]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d2s (contains_byte _ hj (by omega))⟩,
    apart_of (fun a h₁ h₂ => d13 a h₂ h₁) (by omega) (by omega), apart_of (fun a h₁ h₂ => d23 a h₂ h₁) (by omega) (by omega),
    apart_of d12 (by omega) (by omega)⟩

/-- After `entry`, from `s`. -/
structure CvHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 6) ((stackArg s 7).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 6
  x2 : t.gpr .x2 = s.gpr .x6
  x3 : t.gpr .x3 = BitVec.ofNat 64 (s.gpr .x7).toNat
  args : CvArgs t.mem (cvIn s).B (cvIn s).k (cvIn s).pl (cvIn s).ql (cvIn s).dl (cvIn s).pDp (cvIn s).pDq
    (cvIn s).pQi (cvIn s).pN (cvIn s).pP (cvIn s).pQ (cvIn s).pD
  inScr : InScr (stackArg s 6) ((stackArg s 7).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x2, .x3, .x8, .x9] s t

/-- `entry`. -/
theorem cvHead_ok' {s : State} (c : CvCtx s) : WP isa (.block entry) s (CvHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .x7).toNat ≤ (stackArg s 7).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .x7).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 6) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.mono (cvEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, h2, h3, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD,
    hDl, ho, k⟩ => ?_
  refine ⟨c.hs.congr k.wr, h0, h2, by rw [h3, ofNat_toNat64],
    ⟨hDp, hDq, hQi, hN,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x7).toNat by rw [hK, ofNat_toNat64], hP,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (stackArg s 1).toNat by
        rw [hPl, ← c.x1, ofNat_toNat64], hQ,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (stackArg s 3).toNat by
        rw [hQl, ← c.x3, ofNat_toNat64], hD,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (stackArg s 5).toNat by rw [hDl, ofNat_toNat64]⟩,
    InScr.of_outside ho (by omega), k⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cvPre_of {s t₁ t : State} (c : CvCtx s) (h : CvHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t) : CvPre (cvIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 6) ((stackArg s 7).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.wr, x0 := (k.gpr .x0 (by decide)).trans h.x0, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, p := c.p.congrK hi kk, q := c.q.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oQi := ⟨fun i hi => by rw [kk.wr]; exact c.oQi.wr i hi, c.oQi.sep⟩,
      oDp := ⟨fun i hi => by rw [kk.wr]; exact c.oDp.wr i hi, c.oDp.sep⟩,
      oDq := ⟨fun i hi => by rw [kk.wr]; exact c.oDq.wr i hi, c.oDq.sep⟩,
      a1 := c.a1, a2 := c.a2, a3 := c.a3, wr := kk.wr }

/-- `vg_rsa_crt_values`. -/
theorem cvCode_correct (s : State) (h : cvA.pre s) :
    ∃ t s', Exec isa CrtValues.code s t s' ∧ abiPreserved s s' ∧ cvA.post s s' := by
  have c := cvCtx_of h
  clear h
  have hk1 := c.L.k1
  have hk2 := c.L.k2
  suffices hwp : WP isa CrtValues.code s fun s' => abiPreserved s s' ∧ cvA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold CrtValues.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cvHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (cvIn s).nb.length = (s.gpr .x7).toNat := bytesAt_length _ _ _
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h₁.x2 h₁.x3 hk1 hk2 hnl
    (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := cvPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  have hpl : (cvIn s).pb.length = (stackArg s 1).toNat := bytesAt_length _ _ _
  have hql : (cvIn s).qb.length = (stackArg s 3).toNat := bytesAt_length _ _ _
  refine WP.ite (!Spec.Rsa.modulusValid (cvIn s).N (s.gpr .x7).toNat)
    (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (cvIn s).N (s.gpr .x7).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .x7).toNat ≤ (stackArg s 7).toNat * 8 := c.L.z
    have pl2 : (stackArg s 1).toNat < (s.gpr .x7).toNat := c.L.pl2
    have ql2 : (stackArg s 3).toNat < (s.gpr .x7).toNat := c.L.ql2
    have k2' : (s.gpr .x7).toNat ≤ 1024 := c.L.k2
    have k1' : 64 ≤ (s.gpr .x7).toNat := c.L.k1
    exact WP.mono (cvFail_ok hpre.scr hpre.x0 (show 8 * 32 ≤ (stackArg s 7).toNat * 8 by omega) hpre.args c.L.pl1
      (show (stackArg s 1).toNat < 2 ^ 31 by omega) c.L.ql1 (show (stackArg s 3).toNat < 2 ^ 31 by omega)
      hpre.oQi hpre.oDp hpre.oDq hpre.a1 hpre.a2 hpre.a3)
      fun t ⟨z1, z2, z3, hax, _, kt⟩ => ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.crtKey (cvIn s).nb (cvIn s).pb (cvIn s).qb (cvIn s).db = none := by
          simp only [Spec.Rsa.crtKey]
          rw [hnl, hv]; simp
        simp only [cvIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z2, bytesAt_zero z3, bytesAt_zero z1⟩⟩
  · have hv : Spec.Rsa.modulusValid (cvIn s).N (s.gpr .x7).toNat = true := by simpa using hb
    refine WP.mono (WP.keep (.x0 :: mmRegs) (cvMain_ok hpre hv) (by decide +kernel)
      (by decide) (by decide +kernel)) fun t ⟨⟨X, hX, b1, b2, b3, hax, _⟩, kt⟩ =>
      ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), ?_⟩
    have := cvWritten_of (m := t.mem) (dp := s.gpr .x0) (dq := s.gpr .x2) (qi := s.gpr .x4)
      (by rw [hnl]; exact hv) rfl hX (by rw [hpl]; exact b1) (by rw [hpl]; exact b2) (by rw [hql]; exact b3) hax
    rw [hpl, hql] at this
    exact this

end VG.Proof.Rsa.AArch64
