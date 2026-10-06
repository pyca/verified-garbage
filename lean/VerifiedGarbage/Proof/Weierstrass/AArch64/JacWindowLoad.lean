import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombPublic
import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! Public Jacobian table loads within the scratch allocation. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

/-- Copy consecutive words from a public table pointer, with disjoint source
and destination intervals. The table may live inside the scratch allocation. -/
theorem jacWords_ok {s : State} {base : Addr} {size src dst n : Nat}
    (hs : Scr s base size) (hp : s.gpr .x16 = off base src)
    (hd : dst + 8 * n ≤ size) (hd8 : dst % 8 = 0)
    (hsrc : src + 8 * n ≤ size)
    (hap : dst + 8 * n ≤ src ∨ src + 8 * n ≤ dst) :
    ∀ k ≤ n, WP isa (.block ((List.range k).flatMap fun i =>
      [.ldr .x .x4 .x16 (8*i), st .x4 (dst+8*i)])) s fun t =>
      (∀ i < k, word t.mem base (dst+8*i) = word s.mem base (src+8*i)) ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | k+1,hk => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (jacWords_ok hs hp hd hd8 hsrc hap k (by omega)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [← List.singleton_append,WP.block_append_iff]
    have ha : off base src + BitVec.ofNat 64 (8*k) = off base (src+8*k) := by
      simp [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    have hr : InRegions (s₁.rd ++ s₁.wr) (off base src + BitVec.ofNat 64 (8*k)) 8 := by
      rw [ha]
      exact ⟨_,List.mem_append_right _ hs₁.wr,hs₁.contains (by omega) (by decide)⟩
    refine WP.mono (direct_load (by rw [k₁.gpr _ (by decide),hp])
      (o := 8*k) (by have := hs.enc; omega) hr) fun s₂ ⟨e₂,k₂,_⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_ok hs₂ (d := dst+8*k) (by omega) (by omega) .x4) fun t et => ?_
    have mt : t.mem = s₂.mem.writeW (off base (dst+8*k)) (s₂.gpr .x4) := by rw [et]
    have kt : KeepRegs [] s₂ t := by subst et; exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
    have O₂ : Outside base (dst+8*k) 8 s₂.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega)
    have old : word s₁.mem (off base src) (8*k) = word s.mem base (src+8*k) := by
      simp only [word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      change word s₁.mem base (src+8*k) = _
      exact O₁.word (by omega) (by omega)
    refine ⟨fun i hi => ?_,k₁.trans ((Keeps.regs k₂).trans (kt.mono (by simp))),?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega) (by omega),k₂.mem,e₁ i h]
      · obtain rfl : i = k := by omega
        rw [mt,word_writeW_self,e₂,old]
    · refine (O₁.mono (Nat.le_refl _) (by omega)).trans ?_
      rw [← k₂.mem]
      exact O₂.mono (by omega) (by omega)

/-- Address calculation for magnitudes 1 through 16. -/
theorem jacAddress_ok (K : WinCfg) {s : State} {base : Addr} {a : Nat}
    (h0 : s.gpr .x0 = base) (h2 : s.gpr .x2 = BitVec.ofNat 64 a)
    (ha : 1 ≤ a) (ht : K.tbl < 4096) :
    WP isa (.block [.subImm .x .x2 .x2 1, .movz .x .x17 96 0,
      .mul .x .x2 .x2 .x17, .addImm .x .x16 .x0 K.tbl,
      .add .x .x16 .x16 .x2]) s fun t =>
      t.gpr .x16 = off base (K.tbl+96*(a-1)) ∧ Keeps [.x2,.x16,.x17] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,show 16*0<64 from by decide,show 1<4096 from by decide,ht,ite_true,ite_false,
    reduceCtorEq,h0,h2,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simp only [Nat.mul_zero,BitVec.shiftLeft_zero]
    change base + BitVec.ofNat 64 K.tbl + (BitVec.ofNat 64 a - BitVec.ofNat 64 1) * 96 = _
    rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) ha]
    simp only [off,BitVec.ofNat_mul,BitVec.ofNat_add,BitVec.add_assoc]
    rw [BitVec.mul_comm]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

/-- A complete public lookup returns all twelve words of the selected
Jacobian point and writes only the destination point. -/
theorem jacPublicEntry_ok (K : WinCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (h2 : s.gpr .x2 = BitVec.ofNat 64 a)
    (ha : 1 ≤ a) (ht : K.tbl < 4096)
    (hd : K.E.x+96 ≤ size) (hd8 : K.E.x%8=0)
    (htbl : K.tbl+96*(a-1)+96 ≤ size)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x) :
    WP isa (.block (Jacobian.publicEntry K)) s fun t =>
      (∀ i < 12, word t.mem base (K.E.x+8*i) =
        word s.mem base (K.tbl+96*(a-1)+8*i)) ∧
      KeepRegs [.x2,.x4,.x16,.x17] s t ∧ Outside base K.E.x 96 s.mem t.mem := by
  rw [Jacobian.publicEntry,WP.block_append_iff]
  refine WP.mono (jacAddress_ok K hs.x0 h2 ha ht) fun s₁ ⟨h16,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (jacWords_ok (n := 12) hs₁ h16 hd hd8 htbl hap 12 (Nat.le_refl _))
    fun t ⟨hv,hk,ho⟩ => ⟨?_,?_,?_⟩
  · simpa only [k₁.mem] using hv
  · exact ((Keeps.regs k₁).mono (by sub_regs)).trans (hk.mono (by sub_regs))
  · simpa only [k₁.mem] using ho

/-- The twelve-word copy preserves each four-word field element. -/
theorem jacWords_coord {m m' : Mem} {base : Addr} {dst src c : Nat}
    (hc : c < 3)
    (h : ∀ i < 12, word m' base (dst+8*i) = word m base (src+8*i)) :
    wordsVal m' base (dst+32*c) 4 = wordsVal m base (src+32*c) 4 := by
  apply wordsVal_of_words₂
  intro i hi
  have he := h (4*c+i) (by omega)
  simpa only [show dst+8*(4*c+i) = dst+32*c+8*i by omega,
    show src+8*(4*c+i) = src+32*c+8*i by omega] using he

end VG.Proof.Weierstrass.AArch64
