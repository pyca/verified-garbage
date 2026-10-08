import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad

/-! Stores for the Jacobian window's table construction. -/
namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- One table store through the public construction pointer. -/
theorem tableStoreWord_ok {s : State} {base : Addr} {size dst i : Nat}
    (hs : Scr s base size) (hp : s.gpr .x16 = off base dst)
    (hd : dst+8*i+8 ≤ size) :
    WP isa (.block [.str .x .x1 .x16 (8*i)]) s fun t =>
      t = {s with mem := s.mem.writeW (off base (dst+8*i)) (s.gpr .x1)} := by
  have ha : s.gpr .x16 + BitVec.ofNat 64 (8*i) = off base (dst+8*i) := by
    rw [hp]; simp [off,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  have hr : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (8*i)) 8 := by
    rw [ha]; exact ⟨_,hs.wr,hs.contains hd (by decide)⟩
  have he : 8*i%8=0 ∧ 8*i<32768 := by have := hs.enc; omega
  apply WP.of_runBlock
  simp only [runBlock_cons,exec_str_x he hr,ha,runStep_some,runBlock_nil,
    Option.some.injEq,exists_eq_left']

/-- Copy consecutive source words into the public table construction pointer. -/
theorem tableStoreWords_ok {s : State} {base : Addr} {size dst n : Nat} {src : Nat → Nat}
    (hs : Scr s base size) (hp : s.gpr .x16 = off base dst)
    (hd : dst+8*n ≤ size) (hsrc : ∀i<n,src i+8 ≤ size) (hs8 : ∀i<n,src i%8=0)
    (hap : ∀i<n,dst+8*n ≤ src i ∨ src i+8 ≤ dst) :
    ∀ k ≤ n, WP isa (.block ((List.range k).flatMap fun i =>
      [ld .x1 (src i), .str .x .x1 .x16 (8*i)])) s fun t =>
      (∀ i < k, word t.mem base (dst+8*i) = word s.mem base (src i)) ∧
      KeepRegs [.x1] s t ∧ Outside base dst (8*k) s.mem t.mem
  | 0,_ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | k+1,hk => by
    have hn := hs.nowrap
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,WP.block_append_iff]
    refine WP.mono (tableStoreWords_ok hs hp hd hsrc hs8 hap k (by omega)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [← List.singleton_append,WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := src k) (hsrc k (by omega)) (hs8 k (by omega)) .x1) fun s₂ ⟨e₂,k₂,_⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    have h20 : s₂.gpr .x16 = off base dst := by rw [k₂.gpr _ (by decide),k₁.gpr _ (by decide),hp]
    refine WP.mono (tableStoreWord_ok hs₂ h20 (i := k) (by omega)) fun t et => ?_
    have mt : t.mem = s₂.mem.writeW (off base (dst+8*k)) (s₂.gpr .x1) := by rw [et]
    have kt : KeepRegs [] s₂ t := by subst et; exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
    have O₂ : Outside base (dst+8*k) 8 s₂.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega)
    have old : word s₁.mem base (src k) = word s.mem base (src k) :=
      O₁.word (by have := hap k (by omega); omega) (by have := hsrc k (by omega); omega)
    refine ⟨fun i hi => ?_,k₁.trans ((Keeps.regs k₂).trans (kt.mono (by simp))),?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega) (by omega),k₂.mem,e₁ i h]
      · obtain rfl : i = k := by omega
        rw [mt,word_writeW_self,e₂,old]
    · refine (O₁.mono (Nat.le_refl _) (by omega)).trans ?_
      rw [← k₂.mem]
      exact O₂.mono (by omega) (by omega)

end VG.Proof.P256.EcdhJac
