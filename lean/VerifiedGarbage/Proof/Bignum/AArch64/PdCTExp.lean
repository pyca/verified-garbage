import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-!
# `vg_rsa_public_precomputed` on AArch64: the exponentiation is constant time but for `e`

The exponentiation branches on the bits of `e` and on whether it has
started, which is whether the prefix of `e` so far is nonzero: the runs agree
on both because they agree on `e` (`pExpBit_ct`, `pExpLoop_ct`, `finish_ct`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

variable {M : Mont}

/-- The condition on `r` after a count that leaves it nonzero iff `j + 1 ≠ n`. -/
theorem eval_count_r {t : State} {r : Reg} {j n : Nat} (hj : j < n) (h : (t.gpr r).toNat ≠ 0 ↔ j + 1 ≠ n) :
    isa.eval (.nonzero .x r) t = some (decide (j + 1 < n)) := by
  rw [eval_nonzero, ne_zero_iff]
  exact congrArg some (decide_eq_decide.mpr (by rw [h]; omega))

/-! ## A bit -/

/-- The public data of a bit: the working space, `m`, the prefix `E` of `e`
so far and the bit's byte (shifted) `V`. -/
structure PBitPub where
  L : Lay
  N : Nat
  E : Nat
  V : Nat

/-- What every step needs of the working space and `X ≡ x R`. -/
def PFacts (L : Lay) (N X x : Nat) : Prop :=
  slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * L.w)) N ∧ X < N ∧
    X % N = x * 2 ^ (64 * L.w) % N

/-- Before a step of a bit, after the prefix `E`. -/
def PQ (p : PBitPub) (t : State) : Prop :=
  ∃ X x, ExpCtx t p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt t.mem p.L.B p.L.w p.N x p.E ∧ PFacts p.L p.N X x ∧
    word t.mem p.L.B (8 * sV) = BitVec.ofNat 64 p.V ∧ p.V < 2 ^ 62

theorem pins_PQ : Pins PQ [.x0] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.x0, h₂.good.x0]

theorem PQ.goodL {p : PBitPub} {t : State} (h : PQ p t) : GoodL p.L t :=
  let ⟨_, _, hc, _, hf, _⟩ := h; ⟨hc.good, hf.1⟩

/-- The started test keeps `PQ`. -/
theorem startedTest_pq {p : PBitPub} {t : State} (h : PQ p t) :
    WP isa (.block startedTest) t fun t' => PQ p t' ∧ isa.eval (.nonzero .x .x3) t' = some (!decide (p.E = 0)) := by
  obtain ⟨X, x, hc, hy, hf, hV, hV'⟩ := h
  exact WP.mono (startedTest_ok hc.good hf.1 hy) fun t' ⟨hz, hm, k⟩ =>
    ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩, hz⟩

/-- `start` leaks the same in runs with the same working space. -/
theorem start_ct : RelCT isa (Two GoodL) start fun _ _ => True := by
  unfold start
  refine RelCT.seq (two_piece (Ψ := fun (L : Lay) t => t.gpr .x12 = BitVec.ofNat 64 L.w ∧
      t.gpr .x16 = off L.B (slot L.w aXm) ∧ t.gpr .x17 = off L.B (slot L.w aY) ∧ t.gpr .x0 = L.B) [.x0]
    pins_good (by taint_decide) ?_)
    (two_taint [.x16, .x17, .x12, .x0] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  rintro L t ⟨hg, hZ⟩
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t₁ => t₁.gpr .x12 = BitVec.ofNat 64 L.w ∧
      t₁.gpr .x16 = off L.B (slot L.w aXm) ∧ t₁.gpr .x17 = off L.B (slot L.w aY)) (by
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aXm < 32 by decide),
      hdr_enc (show sArr aY < 32 by decide), hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aXm (by decide), hg.hdr.harr aY (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h12, h16, h17⟩, k⟩ => ⟨h12, h16, h17, (k.gpr .x0 (by decide)).trans hg.x0⟩

/-- `bitTest`: the bit, into `x3`. -/
theorem bitTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) {V : Nat} (hV : word t.mem B (8 * sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (.block bitTest) t fun t' => t'.gpr .x3 = BitVec.ofNat 64 (V / 128 % 2) ∧ t'.mem = t.mem ∧
      Keep [.x3, .x4] t t' :=
  WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.gpr .x3 = BitVec.ofNat 64 (V / 128 % 2) ∧ t'.mem = t.mem) (by
    unfold bitTest
    brun [hg.x0, hdr_enc (show sV < 32 by decide), hg.scr.ld (d := 8 * sV)
      (by have := hdr_lt_slot w 8 (show sV < 32 by decide); have := hg.scr.nowrap; omega), hV,
      show BitVec.setWidth 64 (1#16) = (1 : BitVec 64) from rfl, bit7 V hV'])
    (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

/-- A bit leaks the same in runs that agree on `e`. -/
theorem pExpBit_ct : RelCT isa (Two PQ) (Precomputed.expBit M.mm) fun _ _ => True := by
  unfold Precomputed.expBit
  -- Whether started.
  refine RelCT.seq (two_piece (Ψ := fun p t => PQ p t ∧ isa.eval (.nonzero .x .x3) t = some (!decide (p.E = 0)))
    _ pins_PQ (by taint_decide) fun p t h => startedTest_pq h) ?_
  -- `Y := Y²` if started.
  refine RelCT.seq (R := Two fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_map (·.L) (fun _ _ h => h.1.1.goodL) (M.ctL (by unfold MmUse; decide)))
      (RelCT.block_nil fun _ _ _ => trivial)) ?_) ?_
  · rintro p t ⟨⟨X, x, hc, hy, hf, hV, hV'⟩, hz⟩
    exact WP.mono (pSq_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hy hz) fun t' ⟨hc', hy', ha, _⟩ =>
      ⟨X, x, hc', hy', hf, by rw [ha.hslot (by decide)]; exact hV, hV'⟩
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
      isa.eval (.nonzero .x .x3) t = some (decide (p.V / 128 % 2 ≠ 0))) [.x0]
    (fun p s₁ s₂ h₁ h₂ => pins_PQ _ s₁ s₂ h₁ h₂) (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hf, hV, hV'⟩
    exact WP.mono (bitTest_ok hc.good hf.1 hV (by omega)) fun t' ⟨h3, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩,
        eval_nz_ofNat h3 (by omega)⟩
  -- If the bit is set: `Y := Y X` once started, `Y := X` and started if not; then the next bit.
  refine RelCT.seq (R := Two fun (p : PBitPub) t => t.gpr .x0 = p.L.B)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (RelCT.block_nil fun _ _ _ => trivial)) ?_)
    (two_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))
  · refine RelCT.seq (two_piece (Ψ := fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
        isa.eval (.nonzero .x .x3) t = some (!decide (2 * p.E = 0))) [.x0]
      (fun p s₁ s₂ h₁ h₂ => pins_PQ _ s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p t h => startedTest_pq h.1.1) ?_
    refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · exact two_map (fun (p : PBitPub) => p.L) (fun _ _ h => h.1.1.goodL)
        (M.ctL (by unfold MmUse; decide))
    · exact two_map (fun (p : PBitPub) => p.L) (fun _ _ h => h.1.1.goodL) start_ct
  · rintro p t ⟨⟨X, x, hc, hy, hf, -, -⟩, hz⟩
    exact WP.mono (pMul_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hy hz)
      fun t' ⟨hc', _⟩ => hc'.good.x0

/-! ## The bits of a byte -/

/-- The public data of the bits of a byte: the working space, `m`, the
exponent so far `E` and the byte `v`. -/
structure BitsPub where
  L : Lay
  N : Nat
  E : Nat
  v : Nat

/-- After `j` bits of a byte. -/
def PBitsInv (p : BitsPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PBitInv t₀ p.L.B p.L.Z p.L.w p.L.minv p.N X x p.E p.v j s ∧
    PFacts p.L p.N X x ∧ p.v < 256

theorem pBitsInv_pq {p : BitsPub} {j : Nat} {s : State} (hj : j < 8) (h : PBitsInv p j s) :
    PQ ⟨p.L, p.N, p.E * 2 ^ j + p.v / 2 ^ (8 - j), p.v * 2 ^ j⟩ s := by
  obtain ⟨t₀, X, x, hI, hf, hv⟩ := h
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨X, x, hI.ctx, hI.y, hf, hI.v, by have := Nat.mul_le_mul_left p.v hp; dsimp only; omega⟩

/-- The eight bits of a byte leak the same in runs that agree on `e`. -/
theorem pBits_ct : RelCT isa (Two fun p s => 0 < 8 ∧ PBitsInv p 0 s)
    (.loop (Precomputed.expBit M.mm) (.nonzero .x .x3)) (Two fun p s => PBitsInv p 8 s) :=
  two_loop (Φ := PBitsInv) (fun _ => 8)
    (two_map (fun q : BitsPub × Nat =>
      (⟨q.1.L, q.1.N, q.1.E * 2 ^ q.2 + q.1.v / 2 ^ (8 - q.2), q.1.v * 2 ^ q.2⟩ : PBitPub))
      (fun _ _ h => pBitsInv_pq h.1 h.2) pExpBit_ct)
    fun _ _ _ hj ⟨t₀, X, x, hI, hf, hv⟩ =>
      WP.mono (pBitStep_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hv hj hI) fun _ ⟨hI', hz⟩ =>
        ⟨eval_count_r hj hz, fun _ => ⟨t₀, X, x, hI', hf, hv⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hv⟩⟩

/-! ## The bytes of `e` -/

/-- The public data of the exponentiation: the working space, `m`, and the
`len` bytes `eb` of `e` at `ep`. -/
structure EPub where
  L : Lay
  N : Nat
  ep : Addr
  len : Nat
  eb : List Byte

/-- What the exponentiation's steps need of the bytes of `e`, from `t₀`. -/
def ESrc (a : EPub) (t₀ : State) : Prop :=
  a.eb.length = a.len ∧ a.len < 2 ^ 31 ∧
    (∀ i < a.len, InRegions (t₀.rd ++ t₀.wr) (a.ep + BitVec.ofNat 64 i) 1) ∧
    (∀ i (_ : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb.getD i 0) ∧
    (∀ i < a.len, a.L.Z ≤ ofs a.L.B (a.ep + BitVec.ofNat 64 i))

/-- The working space's and `m`'s facts every step needs. -/
def EFacts (a : EPub) (X x : Nat) : Prop :=
  slot a.L.w 8 ≤ a.L.Z ∧ 2 ≤ a.L.w ∧ a.L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * a.L.w)) a.N ∧ X < a.N ∧
    X % a.N = x * 2 ^ (64 * a.L.w) % a.N

theorem ESrc.bytes {a : EPub} {t₀ : State} (h : ESrc a t₀) :
    ∀ i (hi : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb[i]'(by have := h.1; omega) :=
  fun i hi => by rw [h.2.2.2.1 i hi]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by have := h.1; omega]

/-- The bits of byte `i`. -/
def bitsPub (q : EPub × Nat) : BitsPub := ⟨q.1.L, q.1.N, pre q.1.eb q.2, (q.1.eb.getD q.2 0).toNat⟩

/-- After `i` bytes of `e`. -/
def PBytesInv (a : EPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PByteInv t₀ a.L.B a.L.Z a.L.w a.L.minv a.N X x a.ep a.len a.eb i s ∧
    EFacts a X x ∧ ESrc a t₀

/-- After `byteHead`'s loads. -/
def PHeadMid (q : EPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ PBytesInv q.1 q.2 s ∧ s.gpr .x3 = q.1.ep ∧ s.gpr .x4 = BitVec.ofNat 64 q.2

theorem pins_pBytes : Pins (fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s) [.x0] :=
  fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.x0, h₂.ctx.good.x0]

theorem pins_pHeadMid : Pins PHeadMid [.x0, .x3, .x4] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, ⟨_, _, _, i₁, _⟩, a₁, c₁⟩ := h₁
  obtain ⟨-, ⟨_, _, _, i₂, _⟩, a₂, c₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.x0, i₂.ctx.good.x0]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of `e` leaks the same in runs that agree on `e`. -/
theorem pByteBody_ct : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s)
    (.seq (.block byteHead) (.seq (.loop (Precomputed.expBit M.mm) (.nonzero .x .x3)) (.block byteNext)))
      fun _ _ => True := by
  rw [byteHead_eq]
  have w₁ : ∀ (q : EPub × Nat) s, q.2 < q.1.len ∧ PBytesInv q.1 q.2 s →
      WP isa (.block [ldh .x3 sE, ldh .x4 sI]) s (PHeadMid q) := by
    rintro q s ⟨hi, t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByteHead1_ok hf.1 hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, X, x, h3, hf, hsrc⟩, h1, h2⟩
  have w₂ : ∀ (q : EPub × Nat) s, PHeadMid q s →
      WP isa (.block [.add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 8, sth .x3 sBit]) s
        fun t => 0 < 8 ∧ PBitsInv (bitsPub q) 0 t := by
    rintro q s ⟨hi, ⟨t₀, X, x, hI, hf, hsrc⟩, h3, h4⟩
    refine WP.mono (pByteHead2_ok hf.1 hsrc.1 hi hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI h3 h4)
      fun t ⟨_, _, hB⟩ => ⟨by decide, t, X, x, ?_, hf, ?_⟩
    · simp only [bitsPub, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show q.2 < q.1.eb.length by have := hsrc.1; omega), Option.getD_some]
      exact hB
    · simp only [bitsPub]; exact (List.getD q.1.eb q.2 0).isLt
  have h₁ : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s)
      (.block [ldh .x3 sE, ldh .x4 sI]) (Two PHeadMid) :=
    two_piece _ pins_pBytes (by taint_decide) w₁
  have h₂ : RelCT isa (Two PHeadMid)
      (.block [.add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 sV, movi .x3 8, sth .x3 sBit])
      (Two fun q s => 0 < 8 ∧ PBitsInv (bitsPub q) 0 s) :=
    two_piece _ pins_pHeadMid (by taint_decide) w₂
  have h₃ : RelCT isa (Two fun (p : BitsPub) s => PBitsInv p 8 s) (.block byteNext) fun _ _ => True :=
    two_taint [.x0] (fun (_ : BitsPub) s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.x0, h₂.ctx.good.x0]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq h₁ h₂))
    (RelCT.seq (two_map bitsPub (fun _ _ h => h) pBits_ct) h₃)

/-- Before `expLoop`. -/
def PExpPre (a : EPub) (s : State) : Prop :=
  ∃ X x : Nat, ExpCtx s a.L.B a.L.Z a.L.w a.L.minv a.N X ∧ EFacts a X x ∧
    word s.mem a.L.B (8 * sE) = a.ep ∧ word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    1 ≤ a.len ∧ ESrc a s

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pExpLoop_ct : RelCT isa (Two PExpPre) (Precomputed.expLoop M.mm) (Two fun a s => PBytesInv a a.len s) := by
  unfold Precomputed.expLoop
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < a.len ∧ PBytesInv a 0 s) [.x0]
    (fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.x0, h₂.good.x0]) (by taint_decide) ?_) ?_
  · rintro a s ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩
    exact WP.mono (pExpInit_ok (x := x) (eb := a.eb) hc hf.1 he hlen) fun t h => ⟨hL1, s, X, x, h, hf, hsrc⟩
  · refine two_loop (Φ := PBytesInv) (fun a => a.len) pByteBody_ct ?_
    rintro a i s hi ⟨t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByte_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hsrc.1 hsrc.2.1 hi
      hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_count_r hi hz, fun _ => ⟨t₀, X, x, hI', hf, hsrc⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hsrc⟩⟩

/-! ## The result -/

/-- The public data of `finish`: the working space, `m` and `e`. -/
structure FPub where
  L : Lay
  N : Nat
  E : Nat

/-- Before `finish`. -/
def FPre (p : FPub) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt s.mem p.L.B p.L.w p.N x p.E ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31

theorem pins_FPre : Pins FPre [.x0] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.x0, h₂.good.x0]

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem finish_ct : RelCT isa (Two FPre) (Precomputed.finish M.mm) fun _ _ => True := by
  unfold Precomputed.finish
  refine RelCT.seq (two_piece (Ψ := fun p t => FPre p t ∧ isa.eval (.nonzero .x .x3) t = some (!decide (p.E = 0)))
    _ pins_FPre (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hZ, hw, hw'⟩
    exact WP.mono (startedTest_ok hc.good hZ hy) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hZ, hw, hw'⟩, hz⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun (p : FPub) => p.L) (fun _ _ ⟨⟨⟨_, _, hc, _, hZ, _⟩, _⟩, _⟩ => ⟨hc.good, hZ⟩)
      (M.ctL (by unfold MmUse; decide))
  -- `Y := 1`.
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : FPub) t => GoodL p.L t ∧ t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧
      t.gpr .x13 = BitVec.ofNat 64 0) [.x0] (fun p s₁ s₂ h₁ h₂ => pins_FPre p s₁ s₂ h₁.1.1 h₂.1.1)
    (by taint_decide) ?_) ?_
  · rintro p t ⟨⟨⟨X, x, hc, hy, hZ, hw, hw'⟩, _⟩, _⟩
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hc.good.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hc.good.scr.nowrap; omega)
    refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t₂ => t₂.gpr .x12 = BitVec.ofNat 64 p.L.w ∧
        t₂.gpr .x13 = BitVec.ofNat 64 0 ∧ t₂.mem = t.mem) (by
      brun [hc.good.x0, hdr_enc (show sW < 32 by decide), hl sW (by decide), hc.good.hdr.hw])
      (by decide) (by decide) (by decide +kernel))
      fun t₂ ⟨⟨h12, h13, hm⟩, k⟩ => ⟨⟨(hc.mem hm k (by decide)).good, hZ⟩, h12, h13⟩
  refine RelCT.seq (two_piece (Ψ := fun (p : FPub) t => t.gpr .x8 = off p.L.B (slot p.L.w aY) ∧
      t.gpr .x12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  rintro p t ⟨⟨hg, hZ⟩, h12, h13⟩
  have hl : InRegions (t.rd ++ t.wr) (off p.L.B (8 * sArr aY)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aY < 32 by decide); have := hg.scr.nowrap; omega)
  refine WP.mono (WP.keep [.x7, .x8] (Q := fun t' => t'.gpr .x8 = off p.L.B (slot p.L.w aY) ∧ t'.gpr .x7 = 0) (by
    brun [hg.x0, hdr_enc (show sArr aY < 32 by decide), hl, hg.hdr.harr aY (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨h8, h7⟩, k⟩ => ⟨h8, (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13, h7⟩

end VG.Proof.Bignum.AArch64
