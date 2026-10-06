import VerifiedGarbage.Proof.Rsa.AArch64.RpMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode

/-!
# `vg_rsa_recover_primes` on AArch64: correctness

`Recover.code mul`, from a state its contract allows, writes `primesKey` of
its inputs (`rpCode_correct`), against `rpA`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_recover_primes(p = x0, p_len = x1, q = x2, q_len = x3, n = x4,
n_len = x5, e = x6, e_len = x7, d = [sp], d_len = [sp + 8],
scratch = [sp + 16], scratch_len = [sp + 24])`. -/
def rpA : Contract isa where
  pre s :=
    let p : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let q : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let n : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let e : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let d : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    s.sp.toNat + 32 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
      p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
      q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x5).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x5).toNat ∧
      (s.gpr .x3).toNat = (s.gpr .x5).toNat ∧ 1 ≤ (s.gpr .x7).toNat ∧
      (s.gpr .x7).toNat ≤ (s.gpr .x5).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat ≤ (s.gpr .x5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x5).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .x0, (s.gpr .x5).toNat), (s.gpr .x2, (s.gpr .x5).toNat)]
      ((s'.gpr .x0).setWidth 32)
      ((Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).1.map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x6) (s₁.gpr .x7).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x6) (s₂.gpr .x7).toNat ∧
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x6) (s₁.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat)).2 =
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x6) (s₂.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat)).2

/-! ## The entry -/

theorem rpEntry_eq : entry = ([.ldrSp .x8 16, .str .x .x0 .x8 (8 * sP), .str .x .x2 .x8 (8 * sQ),
    .str .x .x4 .x8 (8 * Public.sN), .str .x .x5 .x8 (8 * Public.sK), .str .x .x6 .x8 (8 * Public.sE),
    .str .x .x7 .x8 (8 * Public.sElen)] : List Instr) ++
    (hdrPairs [(0, sD), (1, sDl)] ++ ([mov .x0 .x8, mov .x2 .x4, mov .x3 .x5] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def rpEntryMemA (m : Mem) (B : Addr) (vp vq vn vk ve vel : BitVec 64) : Mem :=
  (((((m.writeW (off B (8 * sP)) vp).writeW (off B (8 * sQ)) vq).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk).writeW (off B (8 * Public.sE)) ve).writeW (off B (8 * Public.sElen)) vel

/-- The header after the entry's stores. -/
def rpEntryMem (m : Mem) (B : Addr) (vp vq vn vk ve vel vd vdl : BitVec 64) : Mem :=
  ((rpEntryMemA m B vp vq vn vk ve vel).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem rpEntryMemA_outside (m : Mem) (B : Addr) (vp vq vn vk ve vel : BitVec 64) :
    Outside B 0 (8 * 32) m (rpEntryMemA m B vp vq vn vk ve vel) := by
  unfold rpEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem rpEntryMem_facts (m : Mem) (B : Addr) (vp vq vn vk ve vel vd vdl : BitVec 64) :
    let m' := rpEntryMem m B vp vq vn vk ve vel vd vdl
    word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧ word m' B (8 * Public.sN) = vn ∧
    word m' B (8 * Public.sK) = vk ∧ word m' B (8 * Public.sE) = ve ∧ word m' B (8 * Public.sElen) = vel ∧
    word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' rpEntryMem rpEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, the working space's base
(stack argument 2) in `x0`, and `n` and `n_len` in `x2` and `x3`. -/
theorem rpEntry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 4, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x4 ∧ t.gpr .x3 = s.gpr .x5 ∧
      word t.mem B (8 * sP) = s.gpr .x0 ∧ word t.mem B (8 * sQ) = s.gpr .x2 ∧
      word t.mem B (8 * Public.sN) = s.gpr .x4 ∧ word t.mem B (8 * Public.sK) = s.gpr .x5 ∧
      word t.mem B (8 * Public.sE) = s.gpr .x6 ∧ word t.mem B (8 * Public.sElen) = s.gpr .x7 ∧
      word t.mem B (8 * sD) = stackArg s 0 ∧ word t.mem B (8 * sDl) = stackArg s 1 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.x0, .x2, .x3, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = B := hB
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := ha 2 (by decide)
  have ho : 16 % 8 = 0 ∧ 16 < 32768 := ⟨rfl, by decide⟩
  rw [rpEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = rpEntryMemA s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ?_
      (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha2, hB', hdr_enc (show sP < 32 by decide), hdr_enc (show sQ < 32 by decide),
      hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show Public.sE < 32 by decide), hdr_enc (show Public.sElen < 32 by decide),
      hw sP (by decide), hw sQ (by decide), hw Public.sN (by decide), hw Public.sK (by decide),
      hw Public.sE (by decide), hw Public.sElen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact rpEntryMemA_outside _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0, .x2, .x3] (Q := fun t => t.gpr .x0 = B ∧ t.gpr .x2 = s.gpr .x4 ∧
      t.gpr .x3 = s.gpr .x5 ∧ t.mem = t₂.mem)
    (by brun [h8₂, k12.gpr .x4 (by decide), k12.gpr .x5 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, h2, h3, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = rpEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
      (s.gpr .x7) (stackArg s 0) (stackArg s 1) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨hP, hQ, hN, hK, hE, hEl, hD, hDl, ho'⟩ :=
    rpEntryMem_facts s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (stackArg s 0) (stackArg s 1)
  exact ⟨h0, h2, h3, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho', (k12.trans k₃).mono (by decide)⟩

/-! ## The result -/

/-- What `Recover.code` leaves, from a valid modulus. -/
theorem rpWritten_of {m : Mem} {pp pq : Addr} {x0 : BitVec 64} {nb eb db : List Byte}
    {res : Option (Nat × Nat)}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hres : (Spec.Rsa.recoverPrimes (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db)).1 = res)
    (b1 : Spec.Rsa.bytesAt m pp nb.length = Spec.Rsa.i2osp (fstOr res) nb.length)
    (b2 : Spec.Rsa.bytesAt m pq nb.length = Spec.Rsa.i2osp (sndOr res) nb.length)
    (hr : x0 = BitVec.ofNat 64 res.isSome.toNat) :
    Spec.Rsa.writtenAll m [(pp, nb.length), (pq, nb.length)] (x0.setWidth 32)
      ((Spec.Rsa.primesKey nb eb db).1.map fun v => [v.1, v.2]) := by
  simp only [Spec.Rsa.primesKey, hv, ite_true]
  rw [hr, setWidth_flag]
  subst hres
  generalize Spec.Rsa.recoverPrimes (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = rp at b1 b2 ⊢
  obtain ⟨r1, r2⟩ := rp
  dsimp only at b1 b2 ⊢
  cases r1 with
  | none =>
    simp only [fstOr, sndOr, Option.isSome_none, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.writtenAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, i2osp_zero'], by rw [b2, i2osp_zero']⟩
  | some v =>
    obtain ⟨p, q⟩ := v
    simp only [fstOr, sndOr, Option.isSome_some, ite_true, Option.map_some, Spec.Rsa.writtenAll, List.map_cons,
      List.map_nil] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, b2]⟩

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state. -/
def rpIn (s : State) : RpIn where
  B := stackArg s 2
  Z := (stackArg s 3).toNat * 8
  k := (s.gpr .x5).toNat
  el := (s.gpr .x7).toNat
  dl := (stackArg s 1).toNat
  pP := s.gpr .x0
  pQ := s.gpr .x2
  pN := s.gpr .x4
  pE := s.gpr .x6
  pD := stackArg s 0
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  eb := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  W := s.wr

/-- What `Recover.code` uses of its contract's precondition. -/
structure RpCtx (s : State) : Prop where
  L : RpLens (rpIn s)
  x1 : (s.gpr .x1).toNat = (s.gpr .x5).toNat
  x3 : (s.gpr .x3).toNat = (s.gpr .x5).toNat
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 4, ∀ m', Outside (stackArg s 2) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x4) (rpIn s).nb
  e : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x6) (rpIn s).eb
  d : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0) (rpIn s).db
  oP : OutOk s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x0) (s.gpr .x5).toNat
  oQ : OutOk s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .x2) (s.gpr .x5).toNat
  a : Apart (s.gpr .x0) (s.gpr .x5).toNat (s.gpr .x2) (s.gpr .x5).toNat

theorem rpCtx_of {s : State} (h : rpA.pre s) : RpCtx s := by
  simp only [rpA] at h
  obtain ⟨hsp, hrd, hwr, dpq, dpn, dpe, dpd, dps, dpa, dqn, dqe, dqd, dqs, dqa, dns, des, dds, dsa,
    wP, wQ, wN, wE, wD, wS, hk, hx1, hx3, hel1, hel2, hdl1, hdl2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hx1] at dpq dpn dpe dpd dps dpa wP
  rw [hx3] at dpq dqn dqe dqd dqs dqa wQ
  refine ⟨⟨hk1, hk2, hel1, hel2, hdl1, hdl2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, by simp only [rpIn]; omega⟩, hx1, hx3, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 32) (by omega) (by omega))
      rw [← stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hx1]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr dps (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hx3]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr dqs (contains_byte _ hj (by omega))⟩,
    apart_of dpq (by omega) (by omega)⟩

/-- After `entry`, from `s`. -/
structure RpHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 2
  x2 : t.gpr .x2 = s.gpr .x4
  x3 : t.gpr .x3 = BitVec.ofNat 64 (s.gpr .x5).toNat
  args : RpArgs t.mem (rpIn s).B (rpIn s).k (rpIn s).el (rpIn s).dl (rpIn s).pP (rpIn s).pQ (rpIn s).pN
    (rpIn s).pE (rpIn s).pD
  inScr : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x2, .x3, .x8, .x9] s t

/-- `entry`. -/
theorem rpHead_ok' {s : State} (c : RpCtx s) : WP isa (.block entry) s (RpHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .x5).toNat ≤ (stackArg s 3).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .x5).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.mono (rpEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, h2, h3, hP, hQ, hN, hK, hE, hEl, hD, hDl, ho, k⟩ => ?_
  refine ⟨c.hs.congr k.wr, h0, h2, by rw [h3, ofNat_toNat64],
    ⟨hP, hQ, hN,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (s.gpr .x5).toNat by rw [hK, ofNat_toNat64], hE,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (s.gpr .x7).toNat by rw [hEl, ofNat_toNat64], hD,
      show word _ (stackArg s 2) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hDl, ofNat_toNat64]⟩,
    InScr.of_outside ho (by omega), k⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem rpPre_of {s t₁ t : State} (c : RpCtx s) (h : RpHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t) : RpPre (rpIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.wr, x0 := (k.gpr .x0 (by decide)).trans h.x0, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oP := ⟨fun i hi => by rw [kk.wr]; exact c.oP.wr i hi, c.oP.sep⟩,
      oQ := ⟨fun i hi => by rw [kk.wr]; exact c.oQ.wr i hi, c.oQ.sep⟩,
      a := c.a, wr := kk.wr }

/-- `vg_rsa_recover_primes` with the Montgomery multiplication `M`. -/
theorem rpCode_correct (M : Mont) (s : State) (h : rpA.pre s) :
    ∃ t s', Exec isa (code M.mm) s t s' ∧ abiPreserved s s' ∧ rpA.post s s' := by
  have c := rpCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .x5).toNat := c.L.k1
  have hk2 : (s.gpr .x5).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa (code M.mm) s fun s' => abiPreserved s s' ∧ rpA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h₁.x2 h₁.x3 hk1 hk2 hnl
    (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := rpPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  refine WP.ite (!Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat)
    (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .x5).toNat ≤ (stackArg s 3).toNat * 8 := c.L.z
    exact WP.mono (rpFail_ok hpre.scr hpre.x0 (show 8 * 32 ≤ (stackArg s 3).toNat * 8 by omega) hpre.args
      (show 1 ≤ (s.gpr .x5).toNat by omega) (show (s.gpr .x5).toNat < 2 ^ 31 by omega) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, _, kt⟩ => ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : (Spec.Rsa.primesKey (rpIn s).nb (rpIn s).eb (rpIn s).db).1 = none := by
          simp only [Spec.Rsa.primesKey]
          rw [hnl, hv]; simp
        simp only [rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = true := by simpa using hb
    refine WP.mono (rpMain_ok M hpre hv) fun t ⟨res, hres, b1, b2, hax, _, kt⟩ =>
      ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), ?_⟩
    have := rpWritten_of (m := t.mem) (pp := s.gpr .x0) (pq := s.gpr .x2) (by rw [hnl]; exact hv) hres
      (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
    rw [hnl] at this
    exact this

end VG.Proof.Rsa.AArch64
