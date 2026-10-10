import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Tail
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp

/-! ## Ctx -/
section

/-!
# An RSA key from its primes on x86-64: the precondition, as the code uses it

`keyIn s`: the inputs, from the state on entry; `KCtx s`: what the code
uses of `keyPre` (`keyCtx_of`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

/-- The inputs, from the state on entry. -/
def keyIn (s : State) : KIn where
  B := arg s 10
  Z := (arg s 11).toNat * 8
  pl := (s.gpr .r9).toNat
  pN := s.gpr .rdi
  pD := s.gpr .rdx
  pP := s.gpr .r8
  pQ := arg s 0
  pDp := arg s 2
  pDq := arg s 4
  pQi := arg s 6
  pE := arg s 8
  el := (arg s 9).toNat
  sv i := s.gpr (saved.getD i .rax)
  pb := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  qb := bytesAt s.mem (arg s 0) (s.gpr .r9).toNat
  eb := bytesAt s.mem (arg s 8) (arg s 9).toNat
  Wr := s.wr
  sp := s.gpr .rsp

/-- What the code uses of `keyPre`. -/
structure KCtx (s : State) : Prop where
  L : KLens (keyIn s)
  rsi : (s.gpr .rsi).toNat = 2 * (s.gpr .r9).toNat
  hs : Scr s (arg s 10) ((arg s 11).toNat * 8)
  hZ : slot (keyIn s).W 16 ≤ (arg s 11).toNat * 8
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', Outside (arg s 10) 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j
  p : Src s (arg s 10) ((arg s 11).toNat * 8) (s.gpr .r8) (keyIn s).pb
  q : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 0) (keyIn s).qb
  e : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 8) (keyIn s).eb
  O : KOuts (keyIn s)
  hret : ∀ b < 8, (arg s 11).toNat * 8 ≤ ofs (arg s 10) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ o ∈ outsL (keyIn s), ∀ i < o.2, s.gpr .rsp + BitVec.ofNat 64 b ≠ o.1 + BitVec.ofNat 64 i

theorem kStk_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

theorem kStk_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [kStk_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kApart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

theorem keyCtx_of {s : State} (h : keyPre s) : KCtx s := by
  simp only [keyPre] at h
  sig_split h
  rename_i hsp hrd hwr dnd dnp dnq dndp dndq dnqi dne dns dna ddp ddq dddp dddq ddqi dde dds dda dpq
    dpdp dpdq dpqi dpe dps dpa dqdp dqdq dqqi dqe dqs dqa dpdq' dpqi' dpe' dps' dpa' dqqi' dqe' dqs'
    dqa' dqie dqis dqia des dsa dRn dRd dRp dRq dRdp dRdq dRqi dRe dRs dRa wn wd wp wq wdp wdq wqi
    we ws hpl hsi hcx hql hdpl hdql hqil hel1 hel8
  have hsl := h
  obtain ⟨hpl1, hpl2, hpl8⟩ := hpl
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (arg s 10) ((arg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) ws
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  simp only [hcx, hsi] at dnd ddp ddq dddp dddq ddqi dde dds dda dRd wd
  simp only [hsi] at dnp dnq dndp dndq dnqi dne dns dna dRn wn
  simp only [hql] at dnq ddq dpq dqdp dqdq dqqi dqe dqs dqa dRq wq
  simp only [hdpl] at dndp dddp dpdp dqdp dpdq' dpqi' dpe' dps' dpa' dRdp wdp
  simp only [hdql] at dndq dddq dpdq dqdq dpdq' dqqi' dqe' dqs' dqa' dRdq wdq
  simp only [hqil] at dnqi ddqi dpqi dqqi dpqi' dqqi' dqie dqis dqia dRqi wqi
  have hwr' : ∀ (o : Addr) (l : Nat), (⟨o, l⟩ : Region) ∈ s.wr → l ≤ 2 ^ 64 → ∀ i < l,
      InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun o l hm hl i hi => ⟨_, hm, contains_byte o hi hl⟩
  have hpw : (s.gpr .r9).toNat ≤ 2 ^ 64 := by omega
  refine ⟨⟨hpl1, hpl2, hpl8, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, hel1, hel8⟩, hsi, hs,
    by simp only [keyIn, KIn.W, slot, hdrBytes]; omega,
    fun j hj => ⟨_, hargs, by rw [kStk_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega) (by omega))
      rw [← kStk_add s j b] at this; omega)),
    src_of_region (by rw [hwr]; simp) (by omega) dps,
    src_of_region (by rw [hwr]; simp [hql]) (by omega) dqs,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    ⟨fun o ho => ?_, fun o ho => ?_, ?_⟩, fun b hb => ?_⟩
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact hwr' _ _ (by rw [hwr, hsi]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr, hcx, hsi]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr, hql]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr, hdpl]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr, hdql]; simp) (by omega)
    · exact hwr' _ _ (by rw [hwr, hqil]; simp) (by omega)
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> intro i hi
    · exact out_scr dns (contains_byte _ hi (by omega))
    · exact out_scr dds (contains_byte _ hi (by omega))
    · exact out_scr dps (contains_byte _ hi (by omega))
    · exact out_scr dqs (contains_byte _ hi (by omega))
    · exact out_scr dps' (contains_byte _ hi (by omega))
    · exact out_scr dqs' (contains_byte _ hi (by omega))
    · exact out_scr dqis (contains_byte _ hi (by omega))
  · simp only [outsL, keyIn, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    exact ⟨⟨kApart_of dnd (by omega) (by omega), kApart_of dnp (by omega) (by omega),
        kApart_of dnq (by omega) (by omega), kApart_of dndp (by omega) (by omega),
        kApart_of dndq (by omega) (by omega), kApart_of dnqi (by omega) (by omega)⟩,
      ⟨kApart_of ddp (by omega) (by omega), kApart_of ddq (by omega) (by omega),
        kApart_of dddp (by omega) (by omega), kApart_of dddq (by omega) (by omega),
        kApart_of ddqi (by omega) (by omega)⟩,
      ⟨kApart_of dpq (by omega) (by omega), kApart_of dpdp (by omega) (by omega),
        kApart_of dpdq (by omega) (by omega), kApart_of dpqi (by omega) (by omega)⟩,
      ⟨kApart_of dqdp (by omega) (by omega), kApart_of dqdq (by omega) (by omega),
        kApart_of dqqi (by omega) (by omega)⟩,
      ⟨kApart_of dpdq' (by omega) (by omega), kApart_of dpqi' (by omega) (by omega)⟩,
      kApart_of dqqi' (by omega) (by omega)⟩
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
    refine ⟨out_scr dRs hc, fun o ho i hi he => ?_⟩
    simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hi he
    · exact dRn _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRd _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRp _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRq _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRdp _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRdq _ hc (by rw [he]; exact contains_byte _ hi (by omega))
    · exact dRqi _ hc (by rw [he]; exact contains_byte _ hi (by omega))

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Res -/
section

/-!
# An RSA key from its primes on x86-64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyOp keyStatus keyFromPrimes)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (rax : BitVec 64) : Prop :=
  (rax.setWidth 32).toNat = keyStatus (keyOp I.pl I.eb I.pb I.qb) ∧
    match keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32 (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .rax) := by
  have hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

theorem i2osp_ite (c : Bool) (x k : Nat) :
    Spec.Rsa.i2osp (if c then x else 0) k = if c then Spec.Rsa.i2osp x k else List.replicate k 0 := by
  cases c <;> simp [i2osp_zero]

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  have he : I.E < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  have hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) he hx hxl
  have hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  have hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32 _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    have hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    have hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega)
      omega
    have hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    have hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega
    have hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.X86_64.Key

end
