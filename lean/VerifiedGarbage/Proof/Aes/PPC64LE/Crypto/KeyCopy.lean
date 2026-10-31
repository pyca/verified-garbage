module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyGroups
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the key-copy loop establishes the word loop's initial schedule prefix.
/-! # POWER8 AES key copy -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE

structure KeyConfig (base : State) (P S : Addr) (K : Nat) : Prop where
  length : K = 16 ∨ K = 24 ∨ K = 32
  key : (⟨P, K⟩ : Region) ∈ base.rd ++ base.wr
  schedule : (⟨S, 240⟩ : Region) ∈ base.wr
  sep : (⟨P, K⟩ : Region).Disjoint ⟨S, 240⟩

structure CopyInv (base : State) (P S : Addr) (K c : Nat) (s : State) : Prop where
  bound : 8*c ≤ K
  keep : Keep [.r3, .r4, .r5, .r8] base s
  ptr : s.gpr .r3 = P + BitVec.ofNat 64 (8*c)
  out : s.gpr .r5 = S + BitVec.ofNat 64 (8*c)
  left : s.gpr .r4 = BitVec.ofNat 64 (K-8*c)
  copied : ∀ k < 8*c, s.mem (S + BitVec.ofNat 64 k) = base.mem (P + BitVec.ofNat 64 k)
  frame : Frame [⟨S, 240⟩] base.mem s.mem

theorem store64_byte (m : Mem) (a : Addr) (v : BitVec 64) {t : Nat} (ht : t < 8) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8*t) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show t < 2^64 by omega),
    show t < 64/8 by omega, ite_true, BitVec.setWidth_eq]

theorem load64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8*t) 8 = m (a + BitVec.ofNat 64 t) := by
  rw [← Mem.extractLsb'_read m a (n := 8) ht]
  rfl

theorem copy_step {base s : State} {P S : Addr} {K c : Nat} (hc : KeyConfig base P S K)
    (h : CopyInv base P S K c s) (hmore : 8*c < K) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.copyBody) s (CopyInv base P S K (c+1)) := by
  have hK : K ≤ 32 := by rcases hc.length with he | he | he <;> omega
  have hnext : 8*c+8 ≤ K := by rcases hc.length with he | he | he <;> omega
  have hin : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (8*c)) 8 := by
    rw [h.keep.2.1, h.keep.2.2]
    exact ⟨⟨P, K⟩, hc.key, Offset.contains_base _ (d := 8*c) (n := 8) (k := K) (by omega) (by omega)⟩
  have hout : InRegions s.wr (S + BitVec.ofNat 64 (8*c)) 8 := by
    rw [h.keep.2.2]
    exact ⟨⟨S, 240⟩, hc.schedule, Offset.contains_base _ (d := 8*c) (n := 8) (k := 240) (by omega) (by omega)⟩
  rw [Impl.Aes.PPC64LE.Crypto.copyBody]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [h.ptr, BitVec.add_zero]) hin fun s₁ u₁ => ?_
  refine wp_std (by decide) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.out, BitVec.add_zero]) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => ?_
  refine wp_subi (by decide) (by decide) fun s₅ u₅ => wp_nil ?_
  have hm : s₅.mem = s.mem.writeW (S + BitVec.ofNat 64 (8*c)) (s.mem.readW (P + BitVec.ofNat 64 (8*c)) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  have hk : Keep [.r3, .r4, .r5, .r8] s s₅ := by
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₅.other _ hr.2.1, u₄.other _ hr.2.2.1, u₃.other _ hr.1, congrFun u₂.gpr r, u₁.other _ hr.2.2.2]
    · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨by omega, (h.keep.trans hk).mono (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, congrFun u₂.gpr .r3,
      u₁.other _ (by decide), h.ptr, Offset.add_add]
    exact congrArg (fun i => P + BitVec.ofNat 64 i) (by omega)
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), congrFun u₂.gpr .r5,
      u₁.other _ (by decide), h.out, Offset.add_add]
    exact congrArg (fun i => S + BitVec.ofNat 64 i) (by omega)
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), congrFun u₂.gpr .r4,
      u₁.other _ (by decide), h.left, Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · intro j hj
    rw [hm]
    by_cases hjc : j < 8*c
    · have hf : Frame [⟨S + BitVec.ofNat 64 (8*c), 8⟩] s.mem
          (s.mem.writeW (S + BitVec.ofNat 64 (8*c)) (s.mem.readW (P + BitVec.ofNat 64 (8*c)) 64)) :=
        (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      rw [hf.bytes (R := ⟨S, 8*c⟩) (by
        simpa only [List.mem_singleton, forall_eq, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          Offset.disjoint S (d := 0) (n := 8*c) (e := 8*c) (k := 8) (Or.inl (by omega)) (by omega) (by omega))
        (by change 8*c ≤ 2^64; omega) hjc]
      exact h.copied j hjc
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 8 ∧ j = 8*c+t := ⟨j-8*c, by omega, by omega⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, store64_byte _ _ _ ht, load64_byte _ _ ht,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h.frame.bytes (R := ⟨P, K⟩) (by simpa only [List.mem_singleton, forall_eq] using hc.sep)
        (by change K ≤ 2^64; omega) (by change 8*c+t < K; omega)
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 8*c) (n := 8) (k := 240) (by omega) (by omega))

theorem copy_loop_ok {base s : State} {P S : Addr} {K : Nat} (hc : KeyConfig base P S K)
    (h : CopyInv base P S K 0 s) :
    WP isa (.loop (.block Impl.Aes.PPC64LE.Crypto.copyBody) (.nonzero .d .r4)) s (CopyInv base P S K (K/8)) := by
  have hK : K ≤ 32 := by rcases hc.length with he | he | he <;> omega
  have hdiv : 8*(K/8) = K := by rcases hc.length with he | he | he <;> omega
  have hpos : 0 < K/8 := by rcases hc.length with he | he | he <;> omega
  have step : ∀ c t, c+1 ≤ K/8 → CopyInv base P S K c t →
      WP isa (.block Impl.Aes.PPC64LE.Crypto.copyBody) t (CopyInv base P S K (c+1)) := by
    intro c t hc' ht
    exact copy_step hc ht (by omega)
  have test : ∀ c t, c ≤ K/8 → CopyInv base P S K c t →
      (K/8-c < 1 → eval (.nonzero .d .r4) t = some false) ∧
      (1 ≤ K/8-c → eval (.nonzero .d .r4) t = some true) := by
    intro c t hc' ht
    have he := eval_nonzero_ofNat' t .r4 (by omega) ht.left
    change eval (.nonzero .d .r4) t = some (decide (K-8*c ≠ 0)) at he
    constructor
    · intro hl
      rw [he, show K-8*c = 0 by omega]
      rfl
    · intro hl
      rw [he]
      simp only [ne_eq, show ¬K-8*c = 0 by omega, not_false_eq_true, decide_true]
  refine WP.mono (WP.chunk_loop (by decide) hpos h step test) ?_
  rintro t ⟨j, hj, he, ht⟩
  have hje : j = K/8 := by omega
  exact hje ▸ ht

end VG.Proof.Aes.PPC64LE.Crypto
