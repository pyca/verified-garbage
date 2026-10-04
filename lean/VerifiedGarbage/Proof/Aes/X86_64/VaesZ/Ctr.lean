import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

/-!
# AVX-512 VAES counter mode: the counter blocks and the data

`ctrsZ_ok`: `ctrsZ c m i regs` puts the counter blocks `CB`, `inc₃₂(CB)`, …
into the lanes of the registers `regs` (lane `l` of register `k` gets block
`4k + l`), as bytes; `xorDataZ_ok`: `xorDataZ t base regs j` XORs the lanes
of the registers into the data blocks `4j`, `4j + 1`, …; both for any list
of registers, by induction, as `Vaes.ctrs_ok` and `Vaes.xorData_ok` do with
two lanes.
-/

namespace VG.Proof.Aes.X86_64.VaesZ

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ xorDataZ)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (paddd_one ea_at ofInt_natCast inRegions_wr off_toNat eval_pxor blockAt_frame)
open VG.Proof.Aes.X86_64.Vaes (blockAt_writeW_sep)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- 4 in doubleword 0 of each lane. -/
abbrev four : BitVec 128 := (0 : BitVec 64) ++ (4 : BitVec 64)

theorem paddd_four (c : Block) : XBinOp.eval .paddd c four = inc32 (inc32 (inc32 (inc32 c))) := by
  rw [← paddd_one, ← paddd_one, ← paddd_one, ← paddd_one]
  apply ext_dword <;>
  rw [dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), dword_paddd _ _ (by decide),
    dword_paddd _ _ (by decide), dword_paddd _ _ (by decide), BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc] <;>
  exact congrArg (_ + ·) (by decide)

/-- One register's four counter blocks into `b`. -/
theorem ctr1Z_ok (c m i : XReg) (b : XReg) (s : State) (X : Block) (j : Nat) (h9 : b ≠ c) (h12 : b ≠ i)
    (hc : ∀ l < 4, s.zlane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 4, s.zlane m l = revMask) (ht : ∀ l < 4, s.zlane i l = four) :
    WP isa (.block [.zop (.zbin .vpshufb b c m), .zop (.zbin .vpaddd c c i)])
      s fun s' =>
      (∀ l < 4, s'.zlane b l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + l) X) revMask) ∧
      (∀ l < 4, s'.zlane c l = Nat.repeat inc32 (j + 4 + l) X) ∧ ZFrame [b, c] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
  · simp only [zlane_zbin _ _ _ _ _ _ hl, h9, ite_true, ite_false, hc l hl, hr l hl, ZBinOp.sse]
  · simp only [zlane_zbin _ _ _ _ _ _ hl, ite_true, Ne.symm h9, Ne.symm h12, ite_false, hc l hl, ht l hl,
      ZBinOp.sse]
    rw [paddd_four, show j + 4 + l = (j + l) + 1 + 1 + 1 + 1 by omega]
    rfl
  · refine ⟨by simp, by simp, by simp, by simp, fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [zlane_zbin _ _ _ _ _ _ hl, hr.1, hr.2]

theorem ctrsZ_ok (c m i : XReg) (hci : c ≠ i) (hcm : c ≠ m) (regs : List XReg) (s : State) (X : Block) (j : Nat)
    (hnd : regs.Nodup) (hx : ∀ r ∈ regs, r ≠ c ∧ r ≠ m ∧ r ≠ i)
    (hc : ∀ l < 4, s.zlane c l = Nat.repeat inc32 (j + l) X)
    (hr : ∀ l < 4, s.zlane m l = revMask) (ht : ∀ l < 4, s.zlane i l = four) :
    WP isa (.block (ctrsZ c m i regs)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        s'.zlane regs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (j + 4 * k + l) X) revMask) ∧
      (∀ l < 4, s'.zlane c l = Nat.repeat inc32 (j + 4 * regs.length + l) X) ∧
      ZFrame (c :: regs) s s' := by
  induction regs generalizing s j with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun l hl => by simpa using hc l hl,
      ZFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h12⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrsZ, WP.block_append_iff]
    refine WP.mono (ctr1Z_ok c m i b s X j h9 h12 hc hr ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (j + 4) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (fun l hl => by rw [f₁.zlane _ (by simp [Ne.symm h10, Ne.symm hcm]) l hl]; exact hr l hl)
      (fun l hl => by rw [f₁.zlane _ (by simp [Ne.symm h12, hci.symm]) l hl]; exact ht l hl))
      fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk l hl
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        rw [f.zlane _ (by simp [h9, hbs]) l hl, e₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 4 + 4 * k + l = j + 4 * (k + 1) + l by omega]
    · intro l hl
      rw [c l hl, List.length_cons, show j + 4 + 4 * bs.length + l = j + 4 * (bs.length + 1) + l by omega]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

/-- Lane `l` of a 64-byte load. -/
theorem load512_lane (m : Mem) (a : Addr) {l : Nat} (hl : l < 4) :
    (m.readW a 512).extractLsb' (128 * l) 128 = m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  have e := readW_extract m a (w := 512) (k := 16 * l) (n := 16) (by omega)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  exact e

/-- Lane `l` of a register, as a stored value. -/
theorem zmm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 4) :
    (s.zmm r).extractLsb' (128 * l) 128 = s.zlane r l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.zmm, State.ymm, State.zlane, State.lane, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, decide_eq_true hj, Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · simp only [show 128 * 0 + j < 256 by omega, show 128 * 0 + j < 128 by omega, ite_true,
      show (0 : Nat) < 2 by decide]
    exact congrArg _ (by omega)
  · simp only [show 128 * 1 + j < 256 by omega, show ¬ 128 * 1 + j < 128 by omega,
      ite_true, ite_false, show (1 : Nat) < 2 by decide, show (1 : Nat) ≠ 0 by decide]
    exact congrArg _ (by omega)
  · simp only [show ¬ 128 * 2 + j < 256 by omega, ite_false, show ¬ (2 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega)
  · simp only [show ¬ 128 * 3 + j < 256 by omega, ite_false, show ¬ (3 : Nat) < 2 by decide,
      BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
    exact congrArg _ (by omega)

/-- The block at `a + 16 l` of a 64-byte write at `a`. -/
theorem blockAt_writeW_lane (m : Mem) (a : Addr) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    blockAt (m.writeW a v) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (v.extractLsb' (128 * l) 128) revMask := by
  have e := readW_writeW_inside m a v (k := 16 * l) (n := 16) (by omega) (by decide)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  rw [blockAt_eq, e]

/-- XOR the four lanes of `b` into the blocks at `base + d` … `base + d + 48`. -/
theorem xor1Z_ok (t : XReg) (base : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hin : InRegions s.wr (s.gpr base + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load t (at_ base d), .zop (.zbin .vpxord b b t),
        .vmovdqu32Store (at_ base d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr base + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 4, blockAt s'.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hin' := inRegions_wr hin
  let a := s.gpr base + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW a 512
  let s₁ := s.setZ t (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpxord b b t).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane t l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ base d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, ea_at, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr, ZOp.exec_wr,
      State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb8, ite_false, eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

theorem xorDataZ_ok (t : XReg) (base : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hw : (s.gpr base).toNat + 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataZ t base regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        blockAt s'.mem (s.gpr base + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) =
          blockAt s.mem (s.gpr base + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorDataZ, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (xor1Z_ok t base b (64 * j) s hb8 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrcx : s₁.gpr base = s.gpr base := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrcx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrcx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrcx] at hb hf
    rw [ofInt_natCast] at m₁ b₁
    have adr : ∀ l < 4, s.gpr base + BitVec.ofNat 64 (16 * (4 * j + l)) =
        s.gpr base + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * l) := fun l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨s.gpr base + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + BitVec.ofNat 64 (16 * (4 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr base).isLt
      omega
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr l hl, b₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁, blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr base).isLt
            simp only [Nat.reduceDiv] at h₂
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr base).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

end VG.Proof.Aes.X86_64.VaesZ
