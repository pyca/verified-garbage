import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-!
# `vg_rsa_crt_values` on x86-64: correctness

`CrtValues.code`, from a state its contract allows, writes `crtKey` of its
inputs (`cvCode_correct`), against `cvContract`, which states the shared
contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_crt_values(dp = rdi, dp_len = rsi, dq = rdx, dq_len = rcx,
qinv = r8, qinv_len = r9, n = [rsp + 8], n_len = [rsp + 16],
p = [rsp + 24], p_len = [rsp + 32], q = [rsp + 40], q_len = [rsp + 48],
d = [rsp + 56], d_len = [rsp + 64], scratch = [rsp + 72],
scratch_len = [rsp + 80])`. -/
def cvContract : Contract isa where
  pre s :=
    let dp : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let dq : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let qi : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let n : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let p : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let q : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let d : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, d, args] ∧ s.wr = [dp, dq, qi, scr] ∧
      dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint n ∧ dp.Disjoint p ∧ dp.Disjoint q ∧ dp.Disjoint d ∧
      dp.Disjoint scr ∧ dp.Disjoint args ∧
      dq.Disjoint qi ∧ dq.Disjoint n ∧ dq.Disjoint p ∧ dq.Disjoint q ∧ dq.Disjoint d ∧ dq.Disjoint scr ∧
      dq.Disjoint args ∧
      qi.Disjoint n ∧ qi.Disjoint p ∧ qi.Disjoint q ∧ qi.Disjoint d ∧ qi.Disjoint scr ∧ qi.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint n ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint d ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (stackArg s 1).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (stackArg s 1).toNat ∧ 1 ≤ (stackArg s 5).toNat ∧
      (stackArg s 5).toNat < (stackArg s 1).toNat ∧ (s.gpr .rsi).toNat = (stackArg s 3).toNat ∧
      (s.gpr .r9).toNat = (stackArg s 3).toNat ∧ (s.gpr .rcx).toNat = (stackArg s 5).toNat ∧
      1 ≤ (stackArg s 7).toNat ∧ (stackArg s 7).toNat ≤ (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (stackArg s 1).toNat ≤ (stackArg s 9).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .rdi, (stackArg s 3).toNat), (s.gpr .rdx, (stackArg s 5).toNat),
        (s.gpr .r8, (stackArg s 3).toNat)] ((s'.gpr .rax).setWidth 32)
      ((Spec.Rsa.crtKey (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat)).map fun v => [v.1, v.2.1, v.2.2])
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧ stackArg s₁ 8 = stackArg s₂ 8 ∧
      stackArg s₁ 9 = stackArg s₂ 9 ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat

/-! ## The entry -/

theorem cvEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 72 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sDp) .rdi, .store (hdr11 sPl) .rsi, .store (hdr11 sDq) .rdx, .store (hdr11 sQl) .rcx,
    .store (hdr11 sQi) .r8] : List Instr) ++
    (crtPairs [(0, Impl.Bignum.X86_64.Public.sN), (1, Impl.Bignum.X86_64.Public.sK), (2, sP), (4, sQ), (6, sD),
      (7, sDl)] ++ ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def cvEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi : BitVec 64) : Mem :=
  ((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sDp)) vdp).writeW
    (off B (8 * sPl)) vpl).writeW (off B (8 * sDq)) vdq).writeW (off B (8 * sQl)) vql).writeW (off B (8 * sQi)) vqi

/-- The header after the entry's stores. -/
def cvEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) : Mem :=
  ((((((cvEntryMemA m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi).writeW (off B (8 * Impl.Bignum.X86_64.Public.sN))
    vn).writeW (off B (8 * Impl.Bignum.X86_64.Public.sK)) vk).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sQ)) vq).writeW (off B (8 * sD)) vd).writeW (off B (8 * sDl)) vdl

theorem cvEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi : BitVec 64) :
    Outside B 0 (8 * 32) m (cvEntryMemA m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi) := by
  unfold cvEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem cvEntryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl : BitVec 64) :
    let m' := cvEntryMem m B v0 v1 v2 v3 v4 v5 vdp vpl vdq vql vqi vn vk vp vq vd vdl
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sDp) = vdp ∧ word m' B (8 * sPl) = vpl ∧
    word m' B (8 * sDq) = vdq ∧ word m' B (8 * sQl) = vql ∧ word m' B (8 * sQi) = vqi ∧
    word m' B (8 * Impl.Bignum.X86_64.Public.sN) = vn ∧ word m' B (8 * Impl.Bignum.X86_64.Public.sK) = vk ∧
    word m' B (8 * sP) = vp ∧ word m' B (8 * sQ) = vq ∧ word m' B (8 * sD) = vd ∧ word m' B (8 * sDl) = vdl ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' cvEntryMem cvEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 8) in `rdi`. -/
theorem cvEntry_ok {s : State} {B : Addr} (hB : stackArg s 8 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 9, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem B (8 * sDp) = s.gpr .rdi ∧ word t.mem B (8 * sPl) = s.gpr .rsi ∧
      word t.mem B (8 * sDq) = s.gpr .rdx ∧ word t.mem B (8 * sQl) = s.gpr .rcx ∧
      word t.mem B (8 * sQi) = s.gpr .r8 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sN) = stackArg s 0 ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sK) = stackArg s 1 ∧
      word t.mem B (8 * sP) = stackArg s 2 ∧ word t.mem B (8 * sQ) = stackArg s 4 ∧
      word t.mem B (8 * sD) = stackArg s 6 ∧ word t.mem B (8 * sDl) = stackArg s 7 ∧
      Outside B 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e8 : s.gpr .rsp + BitVec.ofInt 64 72 = stackArgAddr s 8 := rfl
  have hB' : s.mem.readW (stackArgAddr s 8) 64 = B := hB
  have ha8 := ha 8 (by decide)
  rw [cvEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = cvEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e8, ha8, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sDp (by decide),
      hw sPl (by decide), hw sDq (by decide), hw sQl (by decide), hw sQi (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact cvEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = cvEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7) := by
    rw [hm, hm₂, hm₁]; rfl
  rw [hmem]
  obtain ⟨h0, h1, h2, h3, h4, h5, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho⟩ :=
    cvEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (stackArg s 0) (stackArg s 1)
      (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 7)
  refine ⟨hdi, fun i hi => ?_, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD, hDl, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-! ## The result -/

/-- What `CrtValues.code` leaves, from a valid modulus. -/
theorem cvWritten_of {m : Mem} {dp dq qi : Addr} {rax : BitVec 64} {nb pb qb db : List Byte} {X : Nat} {c : Bool}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hc : c = decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb ∧
      Nat.gcd (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = 1))
    (hX : c = true → Spec.Rsa.inverse (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip pb) = some X)
    (b1 : Spec.Rsa.bytesAt m qi pb.length = Spec.Rsa.i2osp (if c then X else 0) pb.length)
    (b2 : Spec.Rsa.bytesAt m dp pb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip pb - 1) else 0) pb.length)
    (b3 : Spec.Rsa.bytesAt m dq qb.length =
      Spec.Rsa.i2osp (if c then Spec.Rsa.os2ip db % (Spec.Rsa.os2ip qb - 1) else 0) qb.length)
    (hr : rax = BitVec.ofNat 64 c.toNat) :
    Spec.Rsa.writtenAll m [(dp, pb.length), (dq, qb.length), (qi, pb.length)] (rax.setWidth 32)
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
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

theorem stkAddr_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stkAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem apart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

/-- The inputs of `main`, from the entry state. -/
def cvIn (s : State) : CvIn where
  B := stackArg s 8
  Z := (stackArg s 9).toNat * 8
  k := (stackArg s 1).toNat
  pl := (stackArg s 3).toNat
  ql := (stackArg s 5).toNat
  dl := (stackArg s 7).toNat
  pDp := s.gpr .rdi
  pDq := s.gpr .rdx
  pQi := s.gpr .r8
  pN := stackArg s 0
  pP := stackArg s 2
  pQ := stackArg s 4
  pD := stackArg s 6
  sv i := s.gpr (saved.getD i .rax)
  nb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  pb := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
  qb := Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat
  db := Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat
  W := s.wr
  sp := s.gpr .rsp

/-- What `CrtValues.code` uses of its contract's precondition. -/
structure CvCtx (s : State) : Prop where
  L : CvLens (cvIn s)
  rsi : (s.gpr .rsi).toNat = (stackArg s 3).toNat
  rcx : (s.gpr .rcx).toNat = (stackArg s 5).toNat
  hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8)
  ha : ∀ j < 9, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 9, ∀ m', Outside (stackArg s 8) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 0) (cvIn s).nb
  p : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 2) (cvIn s).pb
  q : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 4) (cvIn s).qb
  d : Src s (stackArg s 8) ((stackArg s 9).toNat * 8) (stackArg s 6) (cvIn s).db
  oQi : OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .r8) (stackArg s 3).toNat
  oDp : OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdi) (stackArg s 3).toNat
  oDq : OutOk s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .rdx) (stackArg s 5).toNat
  a1 : Apart (s.gpr .r8) (stackArg s 3).toNat (s.gpr .rdi) (stackArg s 3).toNat
  a2 : Apart (s.gpr .r8) (stackArg s 3).toNat (s.gpr .rdx) (stackArg s 5).toNat
  a3 : Apart (s.gpr .rdi) (stackArg s 3).toNat (s.gpr .rdx) (stackArg s 5).toNat
  hret : ∀ b < 8, (stackArg s 9).toNat * 8 ≤ ofs (stackArg s 8) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ j < (stackArg s 3).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .r8 + BitVec.ofNat 64 j) ∧
    (∀ j < (stackArg s 3).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j) ∧
    (∀ j < (stackArg s 5).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 j)

theorem cvCtx_of {s : State} (h : cvContract.pre s) : CvCtx s := by
  simp only [cvContract] at h
  sig_split h
  rename_i hsp hrd hwr d12 d13 d1n d1p d1q d1d d1s d1a d23 d2n d2p d2q d2d d2s d2a d3n d3p d3q d3d
    d3s d3a dns dps dqs dds dsa dR1 dR2 dR3 dRn dRp dRq dRd dRs dRa w1 w2 w3 wN wP wQ wD wS hk hpl1
    hpl2 hql1 hql2 hsi hr9 hcx hdl1 hdl2
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 8) ((stackArg s 9).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 80⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hsi] at d12 d13 d1n d1p d1q d1d d1s d1a dR1 w1
  rw [hcx] at d12 d23 d2n d2p d2q d2d d2s d2a dR2 w2
  rw [hr9] at d13 d23 d3n d3p d3q d3d d3s d3a dR3 w3
  refine ⟨⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hdl1, hdl2, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, bytesAt_length _ _ _, by simp only [cvIn]; omega⟩, hsi, hcx, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 80) (by omega) (by omega))
      rw [← stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d3s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d1s (contains_byte _ hj (by omega))⟩,
    ⟨fun j hj => ⟨_, by rw [hwr, hsi, hcx, hr9]; simp, contains_byte _ hj (by omega)⟩,
      fun j hj => out_scr d2s (contains_byte _ hj (by omega))⟩,
    apart_of (fun a h₁ h₂ => d13 a h₂ h₁) (by omega) (by omega), apart_of (fun a h₁ h₂ => d23 a h₂ h₁) (by omega) (by omega),
    apart_of d12 (by omega) (by omega), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dR3 _ hc (by rw [he]; exact contains_byte _ hj (by omega)),
    fun j hj he => dR1 _ hc (by rw [he]; exact contains_byte _ hj (by omega)),
    fun j hj he => dR2 _ hc (by rw [he]; exact contains_byte _ hj (by omega))⟩

/-- After `entry` and the reloads of `n` and `k`, from `s`. -/
structure CvHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 8) ((stackArg s 9).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 8
  rdx : t.gpr .rdx = stackArg s 0
  rcx : t.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat
  args : CvArgs t.mem (cvIn s).B (cvIn s).k (cvIn s).pl (cvIn s).ql (cvIn s).dl (cvIn s).pDp (cvIn s).pDq
    (cvIn s).pQi (cvIn s).pN (cvIn s).pP (cvIn s).pQ (cvIn s).pD (cvIn s).sv
  inScr : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

/-- `entry`, and `n` and `k` into `rdx` and `rcx`. -/
theorem cvHead_ok' {s : State} (c : CvCtx s) :
    WP isa (.block (entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr))) s (CvHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (stackArg s 1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (stackArg s 1).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 8) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (cvEntry_ok rfl hw c.ha c.hsep) fun t₀ ⟨hdi, hsv, hDp, hPl, hDq, hQl, hQi, hN, hK, hP, hQ, hD,
    hDl, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  have eN : Impl.Bignum.X86_64.Public.sN = 17 := rfl
  have eK : Impl.Bignum.X86_64.Public.sK = 18 := rfl
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = stackArg s 0 ∧
      t.gpr .rcx = stackArg s 1 ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sN) (by omega),
      hs₀.ld (d := 8 * Impl.Bignum.X86_64.Public.sK) (by omega), hN, hK]) rfl)
    fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  rw [← hm] at hsv hDp hPl hDq hQl hQi hN hK hP hQ hD hDl
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, ofNat_toNat64],
    ⟨hDp, hDq, hQi, hN,
      show Bignum.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 1).toNat by rw [hK, ofNat_toNat64], hP,
      show Bignum.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 3).toNat by
        rw [hPl, ← c.rsi, ofNat_toNat64], hQ,
      show Bignum.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 5).toNat by
        rw [hQl, ← c.rcx, ofNat_toNat64], hD,
      show Bignum.word _ (stackArg s 8) _ = BitVec.ofNat 64 (stackArg s 7).toNat by rw [hDl, ofNat_toNat64],
      hsv⟩,
    by rw [hm]; exact InScr.of_outside ho₀ (by omega), (k₀.trans k₁).mono (by decide)⟩

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem cvPre_of {s t₁ t : State} (c : CvCtx s) (h : CvHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) : CvPre (cvIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 8) ((stackArg s 9).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.2.2, rdi := (k.gpr (by decide)).trans h.rdi, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, p := c.p.congrK hi kk, q := c.q.congrK hi kk, d := c.d.congrK hi kk, L := c.L,
      oQi := ⟨fun i hi => by rw [kk.2.2]; exact c.oQi.wr i hi, c.oQi.sep⟩,
      oDp := ⟨fun i hi => by rw [kk.2.2]; exact c.oDp.wr i hi, c.oDp.sep⟩,
      oDq := ⟨fun i hi => by rw [kk.2.2]; exact c.oDq.wr i hi, c.oDq.sep⟩,
      a1 := c.a1, a2 := c.a2, a3 := c.a3, wr := kk.2.2, rsp := kk.gpr (by decide) }

/-- The saved registers and the return address, from what `fail` or `main`
leaves. -/
theorem cvGpr_of {s t₂ t : State} (c : CvCtx s) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (cvIn s).sv i)
    (hsp : t.gpr .rsp = t₂.gpr .rsp) (hsp₂ : t₂.gpr .rsp = s.gpr .rsp)
    (hfr : ∀ x, (stackArg s 9).toNat * 8 ≤ ofs (stackArg s 8) x →
      (∀ i < (stackArg s 3).toNat, x ≠ s.gpr .r8 + BitVec.ofNat 64 i) →
      (∀ i < (stackArg s 3).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 i) →
      (∀ i < (stackArg s 5).toNat, x ≠ s.gpr .rdx + BitVec.ofNat 64 i) → t.mem x = s.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp.trans hsp₂
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZx, n1, n2, n3⟩ := c.hret b hb
    exact hfr _ hZx n1 n2 n3

/-- `vg_rsa_crt_values`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem cvCode_correct (hmx : CrtValues.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : cvContract.pre s) :
    ∃ t s', Exec isa CrtValues.code s t s' ∧ abiPreserved s s' ∧ cvContract.post s s' := by
  have c := cvCtx_of h
  clear h
  have hk1 := c.L.k1
  have hk2 := c.L.k2
  suffices hwp : WP isa CrtValues.code s fun s' => gprPreserved s s' ∧ cvContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold CrtValues.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cvHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (cvIn s).nb.length = (stackArg s 1).toNat := bytesAt_length _ _ _
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 hnl (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := cvPre_of c h₁ hm₂ k₂
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := hpre.rsp
  have hpl : (cvIn s).pb.length = (stackArg s 3).toNat := bytesAt_length _ _ _
  have hql : (cvIn s).qb.length = (stackArg s 5).toNat := bytesAt_length _ _ _
  refine WP.ite (!Spec.Rsa.modulusValid (cvIn s).N (stackArg s 1).toNat) (by simp [eval, hz₂]) (fun hb => ?_)
    (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (cvIn s).N (stackArg s 1).toNat = false := by simpa using hb
    have z : 128 * (stackArg s 1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
    have pl2 : (stackArg s 3).toNat < (stackArg s 1).toNat := c.L.pl2
    have ql2 : (stackArg s 5).toNat < (stackArg s 1).toNat := c.L.ql2
    have k2 : (stackArg s 1).toNat ≤ 1024 := c.L.k2
    have k1 : 64 ≤ (stackArg s 1).toNat := c.L.k1
    exact WP.mono (cvFail_ok hpre.scr hpre.rdi (show 8 * 32 ≤ (stackArg s 9).toNat * 8 by omega) hpre.args c.L.pl1
      (show (stackArg s 3).toNat < 2 ^ 31 by omega) c.L.ql1 (show (stackArg s 5).toNat < 2 ^ 31 by omega)
      hpre.oQi hpre.oDp hpre.oDq hpre.a1 hpre.a2 hpre.a3)
      fun t ⟨z1, z2, z3, hax, hsv, hfr, hsp⟩ => ⟨cvGpr_of c hsv hsp hsp₂ fun x hx n1 n2 n3 => by
        rw [hfr x n1 n2 n3, hm₂]; exact h₁.inScr x hx, by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.crtKey (cvIn s).nb (cvIn s).pb (cvIn s).qb (cvIn s).db = none := by
          simp only [Spec.Rsa.crtKey]
          rw [hnl, hv]; simp
        simp only [cvIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z2, bytesAt_zero z3, bytesAt_zero z1⟩⟩
  · have hv : Spec.Rsa.modulusValid (cvIn s).N (stackArg s 1).toNat = true := by simpa using hb
    exact WP.mono (cvMain_ok hpre hv) fun t ⟨X, hX, b1, b2, b3, hax, hsv, hfr, hsp⟩ =>
      ⟨cvGpr_of c hsv hsp hsp₂ fun x hx n1 n2 n3 => by
        rw [hfr x hx n1 n2 n3, hm₂]; exact h₁.inScr x hx, by
        have := cvWritten_of (m := t.mem) (dp := s.gpr .rdi) (dq := s.gpr .rdx) (qi := s.gpr .r8)
          (by rw [hnl]; exact hv) rfl hX (by rw [hpl]; exact b1) (by rw [hpl]; exact b2) (by rw [hql]; exact b3) hax
        rw [hpl, hql] at this
        exact this⟩

end VG.Proof.Rsa.X86_64
