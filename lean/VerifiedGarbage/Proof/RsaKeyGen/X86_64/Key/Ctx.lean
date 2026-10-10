import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Tail
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

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
