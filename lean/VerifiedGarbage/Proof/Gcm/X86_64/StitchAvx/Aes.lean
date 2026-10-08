import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes

/-!
# Interleaved counter mode and GHASH in AVX: a batch of four blocks

The loops of `Impl.Gcm.X86_64.StitchAvx` keep their state in the lower lanes
of the vector registers (lane 0), as `Impl.Gcm.X86_64.Stitch`'s keep theirs in
both. `batch_ok`: `batch j g` encrypts the four data blocks at `rdx + 16 j`
(blocks `c … c + 3`, `AInv`): the counter blocks into `xmm3`–`xmm6`
(`ctrs_ok`), AES of each (`Vaes.aesGL_ok` for `VEX.128`), and the XOR into
the data (`xorData_ok`). The blocks `g i` between the rounds do what `Q`
says, which neither the counter blocks, the rounds nor the XOR (which writes
only those four blocks) undo.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.StitchAvx (aregs ctrs xorData batch)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Gcm.X86_64.Stitch (SPre kp nr cp dp nb pp dR pR sch ciph cb bAddr blk ctb in_sub in_sub_int
  sch_frame addr_eq)
open VG.Proof.Aes.X86_64.Vaes (aesGL_ok lanes YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame one paddd_one ea_at ofInt_natCast inRegions_wr
  off_toNat blockAt_writeW_sep blockAt_writeW_xor run_in run_sep)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-! ## The counter blocks -/

/-- One counter block into `b`. -/
theorem ctr1_ok (b : XReg) (s : State) (X : Block) (j : Nat) (h14 : b ≠ .xmm14) (h15 : b ≠ .xmm15)
    (hc : s.lane .xmm14 0 = Nat.repeat inc32 j X) (hr : s.lane .xmm0 0 = revMask)
    (ht : s.lane .xmm15 0 = one) :
    WP isa (.block [.vop (.vbin .vpshufb .l128 b .xmm14 .xmm0), .vop (.vbin .vpaddd .l128 .xmm14 .xmm14 .xmm15)])
      s fun s' =>
      s'.lane b 0 = XBinOp.eval .pshufb (Nat.repeat inc32 j X) revMask ∧
      s'.lane .xmm14 0 = Nat.repeat inc32 (j + 1) X ∧ YFrame [b, .xmm14] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [lane_vbin128, h14, ite_true, ite_false, hc, hr, VBinOp.sse]
  · simp only [lane_vbin128, ite_true, Ne.symm h14, Ne.symm h15, ite_false, hc, ht, VBinOp.sse]
    rw [paddd_one]; rfl
  · refine ⟨by simp, by simp, by simp, by simp, fun r hr l _ => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]

theorem ctrs_ok : ∀ (regs : List XReg) (s : State) (X : Block) (j : Nat), regs.Nodup →
    (∀ r ∈ regs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15) →
    s.lane .xmm14 0 = Nat.repeat inc32 j X → s.lane .xmm0 0 = revMask → s.lane .xmm15 0 = one →
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.lane regs[k] 0 = XBinOp.eval .pshufb (Nat.repeat inc32 (j + k) X) revMask) ∧
      s'.lane .xmm14 0 = Nat.repeat inc32 (j + regs.length) X ∧ YFrame (.xmm14 :: regs) s s'
  | [], s, _, _, _, _, hc, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), by simpa using hc, YFrame.refl _ _⟩
  | b :: bs, s, X, j, hnd, hx, hc, hr, ht => by
    obtain ⟨h14, h0, h15⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (ctr1_ok b s X j h14 h15 hc hr ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ctrs_ok bs s₁ X (j + 1) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (by rw [f₁.lane _ (by simp [Ne.symm h0]) 0 (by decide)]; exact hr)
      (by rw [f₁.lane _ (by simp [Ne.symm h15]) 0 (by decide)]; exact ht))
      fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f.lane _ (by simp [h14, hbs]) 0 (by decide), e₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · rw [c, List.length_cons, show j + 1 + bs.length = j + (bs.length + 1) by omega]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

/-- XOR `b` into the block at `rdx + d` with a memory operand. -/
theorem xor1_ok (b : XReg) (d : Nat) (s : State) (_hb : b ≠ .xmm13)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.vbinLoad .vpxor .l128 b b (at_ .rdx d),
        .vmovdquStore .l128 (at_ .rdx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int))
        (XBinOp.eval .pxor (s.lane b 0) (s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm13 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  have hin' := inRegions_wr hin
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128,
    ea_at, hin', ite_true, Option.map_some, VBinOp.sse, XBinOp.eval,
    State.store128_eq, State.setV_gpr, State.setV_wr, hin,
    VG.X86_64.RegUpd.xmm_setV, ite_true, State.setV_mem,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, ?_, fun r hr _ l _ => ?_⟩
  · simp only [State.setMem_gpr, State.setV_gpr]
  · simp only [State.setMem_rd, State.setV_rd]
  · simp only [State.setMem_wr, State.setV_wr]
  · simp only [State.lane, State.setMem_xmm, State.setMem_ymmHi,
      VG.X86_64.RegUpd.xmm_setV, VG.X86_64.RegUpd.ymmHi_setV_128, hr, ite_false]

theorem xorData_ok : ∀ (regs : List XReg) (j : Nat) (s : State), regs.Nodup → .xmm13 ∉ regs →
    (∀ k < regs.length, InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) →
    (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64 →
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.lane regs[k] 0) revMask) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm13 → r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l)
  | [], _, s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h8, hin, hw => by
    have hb8 : b ≠ .xmm13 := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : .xmm13 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (xor1_ok b (16 * j) s hb8 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (xorData_ok bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    have ofs : ∀ a : Nat, (s.gpr .rdx + BitVec.ofInt 64 (a : Int)) = s.gpr .rdx + BitVec.ofNat 64 a :=
      fun a => by rw [ofInt_natCast]
    rw [ofs] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .rdx).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf hdj, m₁, blockAt_writeW_xor]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rdx).isLt
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) 0 (by decide)]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

/-! ## A batch -/

/-- The encryption after `c` blocks: the counter, the mask, the increment,
the key schedule and its last round key, and the data (blocks below `c`
encrypted, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : s.lane .xmm14 0 = Nat.repeat inc32 c (cb s₀)
  msk : s.lane .xmm0 0 = revMask
  inc : s.lane .xmm15 0 = one
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀, blockAt s.mem (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInv s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInv s₀ c s' :=
  ⟨h.le, by rw [f.lane _ h14 0 (by decide)]; exact h.ctr, by rw [f.lane _ h0 0 (by decide)]; exact h.msk,
    by rw [f.lane _ h15 0 (by decide)]; exact h.inc, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨bAddr s₀ c, 64⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 4 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 16 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 4) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 64⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (ctrs_ok aregs s (cb s₀) c hnd hx hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesGL_ok .l128 .xmm13 aregs hnd h13 hp.rounds g G
    (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), XBinOp.eval .pshufb (s₂.lane aregs[k] 0) revMask =
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := fun k h =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) 0 (by decide), e₁ k h])).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (16 * (j + i)) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  refine WP.mono (xorData_ok aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, BitVec.ofInt_natCast, addr]
      exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 16 * j = 16 * (j + 0) by omega, addr, Nat.add_zero] at fr₃
  have fr' : Frame [⟨bAddr s₀ c, 64⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega, ?_, ?_, ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
    by rw [g₃, f₂.gpr, f₁.gpr, hI.rsi], by rw [g₃, f₂.gpr, f₁.gpr, hI.r10], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, f₁.gpr], kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) 0 (by decide), f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) 0 (by decide), c₁]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) 0 (by decide), hI.msk]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) 0 (by decide), hI.inc]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact run_in hw hc (n := 4) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 4) → blockAt s₃.mem (bAddr s₀ k) = blockAt s.mem (bAddr s₀ k) :=
      fun hn => blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 4 by omega, ite_true]
    · by_cases hhi : k < c + 4
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
        have hj : i < aregs.length := by simp [aregs]; omega
        rw [← addr, b₃ i hj, addr, hI.blocks _ hk, ks i hj]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Gcm.X86_64.StitchAvx
