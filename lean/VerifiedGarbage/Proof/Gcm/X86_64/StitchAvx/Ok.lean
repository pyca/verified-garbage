import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Aes`. -/
section

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
theorem ctr1_ok (b : XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat) (h14 : b ≠ .xmm14) (h15 : b ≠ .xmm15)
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

theorem ctrs_ok : ∀ (regs : List XReg) (s : State) (X : VG.Spec.Gcm.Block) (j : Nat), regs.Nodup →
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
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ctr1_ok b s X j h14 h15 hc hr ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ctrs_ok bs s₁ X (j + 1) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
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

/-- XOR `b` into the block at `rdx + d`. -/
theorem xor1_ok (b : XReg) (d : Nat) (s : State) (hb : b ≠ .xmm13)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.vmovdquLoad .l128 .xmm13 (at_ .rdx d), .vop (.vbin .vpxor .l128 b b .xmm13),
        .vmovdquStore .l128 (at_ .rdx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int))
        (XBinOp.eval .pxor (s.lane b 0) (s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm13 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  have hin' := inRegions_wr hin
  let a := s.gpr .rdx + BitVec.ofInt 64 (d : Int)
  let s₁ := s.setV .l128 .xmm13 (s.mem.readW a 128) 0
  let s₂ := (VOp.vbin .vpxor .l128 b b .xmm13).exec s₁
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load128, ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l128 (at_ .rdx d) b) s₂ =
      some (s₂.setMem (s.mem.writeW a (s₂.lane b 0))) := by
    simp only [isa, exec, State.store128_eq, ea_at, s₂, s₁, VOp.exec_gpr, State.setV_gpr, VOp.exec_wr,
      State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a, State.lane, ite_true]
  refine ⟨_, hst, WP.block_nil ⟨?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁],
    fun r h1 h2 l hl => ?_⟩⟩
  · simp only [State.setMem_mem]
    refine congrArg _ ?_
    simp only [s₂, s₁, lane_vbin128, ite_true, State.lane_setV128, hb, ite_false, VBinOp.sse, a]
  · simp [s₂, s₁, lane_vbin128, State.lane_setV128, h1, h2]

theorem xorData_ok : ∀ (regs : List XReg) (j : Nat) (s : State), regs.Nodup → .xmm13 ∉ regs →
    (∀ k < regs.length, InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) →
    (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64 →
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), VG.Spec.Gcm.blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
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
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.xor1_ok b (16 * j) s hb8 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.xorData_ok bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    have ofs : ∀ a : Nat, (s.gpr .rdx + BitVec.ofInt 64 (a : Int)) = s.gpr .rdx + BitVec.ofNat 64 a :=
      fun a => by rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast]
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
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp)).trans
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
  le : c ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀
  ctr : s.lane .xmm14 0 = Nat.repeat inc32 c (cb s₀)
  msk : s.lane .xmm0 0 = revMask
  inc : s.lane .xmm15 0 = one
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [VG.Proof.Gcm.X86_64.Stitch.dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s.mem (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s' :=
  ⟨h.le, by rw [f.lane _ h14 0 (by decide)]; exact h.ctr, by rw [f.lane _ h0 0 (by decide)]; exact h.msk,
    by rw [f.lane _ h15 0 (by decide)]; exact h.inc, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s) :
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
    (hc : c + 4 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 16 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (c + 4) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 64⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := VG.Proof.Gcm.X86_64.StitchAvx.aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ctrs_ok aregs s (cb s₀) c hnd hx hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
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
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.xorData_ok aregs j s₂ hnd h13 (fun k hk => by
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
    refine hI.frame.trans (fr'.sub fun r hr => ⟨VG.Proof.Gcm.X86_64.Stitch.dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact run_in hw hc (n := 4) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 4) → VG.Spec.Gcm.blockAt s₃.mem (bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (bAddr s₀ k) :=
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Gh`. -/
section

/-!
# Interleaved counter mode and GHASH in AVX: the GHASH work

`ghLoad_ok`: `ghLoad k` loads the power at `scratch + 16 k` into `xmm12` and
block `k` at `rdx + 16 k` into `xmm7`, and adds their product to the
product's lower lanes, as the SSE instructions it stands for do
(`WP.lane0`, `Pclmul.ldrev_ok`, `acc_ok`). `accN` is the product after the
first `n` loads of an order, `GEnv` what the loads need, `ghStep` one load
and `ghFin` the reduction into `Y`. The GHASH work between the rounds of a
batch is `gq ord base fin`; `QG` is what holds before the blocks after round
`j`, and `gq_ok` is the obligation of `batch_ok` for it.

Nothing here computes in the field: what the products add up to is
`Proof/Gcm/X86_64/StitchAvx/Ok.lean`'s.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod Only ldrev_ok pxor72_ok acc_ok reduce_ok)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (ghLoad aregs gq)
open VG.Proof.Gcm.X86_64.Stitch (SPre pp dp nb pR bAddr in_sub in_sub_int in_rdwr addr_eq)
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame run_sep)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt)

/-! ## A load -/

/-- The SSE instructions of `ghLoad k`. -/
def ghSse (k : Nat) : List Instr :=
  .movdquLoad .xmm12 (at_ .r11 (16 * k)) ::
    ([.movdquLoad .xmm7 (at_ .rdx (16 * k)), .xop (.bin .pshufb .xmm7 .xmm0)] ++
      ((if k = 0 then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12))

theorem lane0_ghLoad (k : Nat) : lane0Block (ghLoad k) = some (VG.Proof.Gcm.X86_64.StitchAvx.ghSse k) := by
  unfold ghLoad VG.Proof.Gcm.X86_64.StitchAvx.ghSse; split <;> rfl

/-- The registers a load writes. -/
abbrev gl : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11]

theorem ghLoad_dst (k : Nat) : ∀ r, r ∉ VG.Proof.Gcm.X86_64.StitchAvx.gl → r ∉ (ghLoad k).filterMap vdst := by
  intro r hr
  simp only [VG.Proof.Gcm.X86_64.StitchAvx.gl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  unfold ghLoad
  split <;> simp [Impl.Gcm.X86_64.StitchAvx.acc, vdst, h1, h2, h3, h4, h5, h6]

theorem ghLoad_noGpr (k : Nat) : (ghLoad k).all noGpr = true := by
  unfold ghLoad; split <;> rfl

theorem ghSse_ok (k : Nat) (t : State) (h0 : t.xmm .xmm0 = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (VG.Proof.Gcm.X86_64.StitchAvx.ghSse k)) t fun t' =>
      prod t' = (prod t).acc
        ((if k = 0 then t.xmm .xmm2 else 0) ^^^ VG.Spec.Gcm.blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧
      Only VG.Proof.Gcm.X86_64.StitchAvx.gl t t' := by
  let t₁ := t.setXmm .xmm12 (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128)
  have o₁ : Only [.xmm12] t t₁ := ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [t₁, State.setXmm, hr]⟩
  rw [VG.Proof.Gcm.X86_64.StitchAvx.ghSse, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load128, Pclmul.ea_at, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdx (16 * k) t₁ (by decide) (by rw [o₁.xmm _ (by decide)]; exact h0)
    (by rw [o₁.gpr _ (by decide), o₁.rd, o₁.wr]; exact hin)) fun t₂ ⟨e₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [o₁.gpr _ (by decide), o₁.mem] at e₂
  have fin : ∀ t₃, Only [.xmm7] t₂ t₃ → t₃.xmm .xmm7 =
      (if k = 0 then t.xmm .xmm2 else 0) ^^^ VG.Spec.Gcm.blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) →
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12)) t₃ fun t' =>
        prod t' = (prod t).acc
          ((if k = 0 then t.xmm .xmm2 else 0) ^^^ VG.Spec.Gcm.blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
          (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧ Only VG.Proof.Gcm.X86_64.StitchAvx.gl t t' := by
    intro t₃ o₃ e₃
    refine WP.mono (acc_ok .xmm7 .xmm12 t₃ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩
    · rw [p', e₃, o₃.xmm _ (by decide), o₂.xmm _ (by decide), o₃.prod (by decide) (by decide) (by decide),
        o₂.prod (by decide) (by decide) (by decide), o₁.prod (by decide) (by decide) (by decide)]
      simp [t₁, State.setXmm]
    · exact ((o₁₂.trans o₃).trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with ((h | h) | h) | (h | h | h | h) <;> simp [h]
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true] at fin ⊢
    rw [WP.block_append_iff]
    refine WP.mono (pxor72_ok t₂) fun t₃ ⟨e₃, o₃⟩ => fin t₃ o₃ ?_
    have h2 : t₂.xmm .xmm2 = t.xmm .xmm2 := by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide)]
    rw [e₃, e₂, h2]
  · simp only [hk, ite_false, List.nil_append] at fin ⊢
    exact fin t₂ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by rw [e₂]; simp)

/-- The power at `scratch + 16 k` into `xmm12`, and block `k` at `rdx + 16 k`
(with `Y` added to block 0) added to the product with it. -/
theorem ghLoad_ok (k : Nat) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hpin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block (ghLoad k)) s fun s' =>
      prod (s'.proj 0) = (prod (s.proj 0)).acc
        ((if k = 0 then s.lane .xmm2 0 else 0) ^^^ VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx + BitVec.ofInt 64 ((16 * k : Nat) : Int)))
        (s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 128) ∧
      YFrame VG.Proof.Gcm.X86_64.StitchAvx.gl s s' := by
  refine WP.mono (WP.lane0 (VG.Proof.Gcm.X86_64.StitchAvx.lane0_ghLoad k) (VG.Proof.Gcm.X86_64.StitchAvx.ghSse_ok k (s.proj 0) (by simpa using h0) hin hpin))
    fun s' ⟨⟨p, o⟩, hi, hg⟩ => ⟨p, ?_⟩
  have hg := hg (VG.Proof.Gcm.X86_64.StitchAvx.ghLoad_noGpr k)
  refine ⟨hg, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · exact hi r (VG.Proof.Gcm.X86_64.StitchAvx.ghLoad_dst k r hr)

/-! ## The products of a group -/

/-- The input of the `k`-th load: block `k`, with `Y` added to block 0. -/
def inp (X : Nat → VG.Spec.Gcm.Block) (y : VG.Spec.Gcm.Block) (k : Nat) : VG.Spec.Gcm.Block := (if k = 0 then y else 0) ^^^ X k

/-- The product after the first `n` loads, in the order `ord`. -/
def accN (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block) (y : VG.Spec.Gcm.Block) (n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (VG.Proof.Gcm.X86_64.StitchAvx.inp X y (ord i)) (P (ord i))) Prod.zero

theorem accN_succ (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block) (y : VG.Spec.Gcm.Block) (n : Nat) :
    VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y (n + 1) = (VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y n).acc (VG.Proof.Gcm.X86_64.StitchAvx.inp X y (ord n)) (P (ord n)) := by
  simp only [VG.Proof.Gcm.X86_64.StitchAvx.accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after the sixteen blocks of a group. -/
abbrev yNew (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block) (y : VG.Spec.Gcm.Block) : VG.Spec.Gcm.Block :=
  reduce (VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y 16)

/-- What the loads of a group need: its blocks at `rdx` (those from `lo` on,
which the loads to come read), the powers in the working space, and the
mask. -/
structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → VG.Spec.Gcm.blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  ina : ∀ k < 16, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16
  inp : ∀ k < 16, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16
  m0 : s.lane .xmm0 0 = revMask

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block}
    {s : State} (h : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s) (hl : lo ≤ lo') : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.yframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block}
    {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s) (f : YFrame rs s s') (h0 : .xmm0 ∉ rs) :
    VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk => by rw [f.mem]; exact h.pv k hk, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk, by rw [f.lane _ h0 0 (by decide)]; exact h.m0⟩

theorem ofInt_add (a : Addr) (k : Nat) : a + BitVec.ofInt 64 ((16 * k : Nat) : Int) = a + BitVec.ofNat 64 (16 * k) := by
  rw [BitVec.ofInt_natCast]

/-- The product of the lower lanes, kept by a frame without `xmm8`–`xmm10`. -/
theorem prod_yframe {s s' : State} {rs : List XReg} (f : YFrame rs s s') (h8 : .xmm8 ∉ rs) (h9 : .xmm9 ∉ rs)
    (h10 : .xmm10 ∉ rs) : prod (s'.proj 0) = prod (s.proj 0) := by
  simp only [prod, State.proj_xmm, f.lane _ h8 0 (by decide), f.lane _ h9 0 (by decide),
    f.lane _ h10 0 (by decide)]

/-- One GHASH load, the `n`-th of the order `ord`. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block}
    {y : VG.Spec.Gcm.Block} {ord : Nat → Nat} {n : Nat} (hk : ord n < 16) (hlo : lo ≤ ord n) {s : State}
    (hE : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s) (hp : prod (s.proj 0) = VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y n) (hy : s.lane .xmm2 0 = y) :
    WP isa (.block (ghLoad (ord n))) s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s' ∧
      prod (s'.proj 0) = VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y (n + 1) ∧ s'.lane .xmm2 0 = y ∧ YFrame VG.Proof.Gcm.X86_64.StitchAvx.gl s s' := by
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghLoad_ok _ s hE.m0 (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.yframe f' (by decide), ?_, by rw [f'.lane _ (by decide) 0 (by decide), hy], f'⟩
  rw [p', hp, VG.Proof.Gcm.X86_64.StitchAvx.accN_succ, hE.rdx, hE.r11, VG.Proof.Gcm.X86_64.StitchAvx.ofInt_add, VG.Proof.Gcm.X86_64.StitchAvx.ofInt_add, hE.xs _ hlo hk, hE.pv _ hk, hy]
  rfl

/-- The reduction into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block} {s : State}
    (hE : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s) (h1 : s.lane .xmm1 0 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.StitchAvx.reduce .xmm2)) s fun s' =>
      VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ lo a X P s' ∧ s'.lane .xmm2 0 = reduce (prod (s.proj 0)) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.reduce .xmm2) rfl
    (reduce_ok .xmm2 (s.proj 0) (by decide) (by decide) (by decide) (by decide) (by simpa using h1)))
    fun s' ⟨⟨r, o⟩, hi, hg⟩ => ?_
  have f : YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s s' :=
    ⟨hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr, fun r hr l hl => by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · simpa using o.xmm r hr
      · refine hi r ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h8, h9, h10, h11, h2⟩ := hr
        simp [Impl.Gcm.X86_64.StitchAvx.reduce, Impl.Gcm.X86_64.StitchAvx.fold, vdst, h8, h9, h10, h11, h2]⟩
  exact ⟨hE.yframe f (by decide), by simpa using r, f⟩

theorem ite_t {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : ite c a b = a := by
  simp [h]

theorem ite_f {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : ite c a b = b := by
  simp [h]

/-! ## The GHASH work of a batch -/

/-- What holds before the blocks after round `j` of a batch. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block)
    (y : VG.Spec.Gcm.Block) (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) (s : State) : Prop :=
  VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ (lo j) a X P s ∧ s.lane .xmm1 0 = poly ∧
  (if fin ∧ 5 < j then s.lane .xmm2 0 = VG.Proof.Gcm.X86_64.StitchAvx.yNew ord X P y
   else prod (s.proj 0) = VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y (base + min (j - 1) 4) ∧ s.lane .xmm2 0 = y)

/-- The registers the GHASH work of a batch writes. -/
abbrev gRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

theorem gRegs_ok : ∀ r ∈ VG.Proof.Gcm.X86_64.StitchAvx.gRegs, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG.yframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block}
    {y : VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j : Nat} {s s' : State} {rs : List XReg}
    (h : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin j s) (f : YFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), s'.lane r 0 = s.lane r 0 :=
    fun r hr => f.lane r (fun h => hrs r h hr) 0 (by decide)
  have kp : prod (s'.proj 0) = prod (s.proj 0) := by
    simp only [prod, State.proj_xmm, k .xmm8 (by decide), k .xmm9 (by decide), k .xmm10 (by decide)]
  refine ⟨hE.yframe f (fun h => hrs _ h (by decide)), by rw [k .xmm1 (by decide)]; exact h1, ?_⟩
  split
  · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t (by assumption)] at h2
    rw [k .xmm2 (by decide)]; exact h2
  · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by assumption)] at h2
    exact ⟨by rw [kp]; exact h2.1, by rw [k .xmm2 (by decide)]; exact h2.2⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block}
    {y : VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool}
    (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → ord (base + j - 1) < 16 ∧ lo j ≤ ord (base + j - 1))
    (hfin : fin = true → base = 12) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (Stitch.nr s₀) (Stitch.sch s₀) s → VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin j s →
      WP isa (.block (gq ord base fin j)) s fun s' =>
        VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin (j + 1) s' ∧ YFrame VG.Proof.Gcm.X86_64.StitchAvx.gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    obtain ⟨hk, hlo⟩ := hrd j hj1 hl4
    rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega, show base + (j - 1) = base + j - 1 by omega] at h2
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), by rw [f'.lane _ (by decide) 0 (by decide)]; exact h1, ?_⟩,
        f'.mono (by decide)⟩
    rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by omega), show min (j + 1 - 1) 4 = j by omega, show base + j = base + j - 1 + 1 by omega]
    exact ⟨p', y'⟩
  · by_cases h5 : fin = true ∧ j = 5
    · -- The reduction.
      obtain ⟨hf, rfl⟩ := h5
      rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by omega)] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega, ite_false, hf, and_self, ite_true]
      have hb := hfin hf
      subst hb
      refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghFin hE h1) fun s' ⟨hE', y0, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), by rw [f'.lane _ (by decide) 0 (by decide)]; exact h1, ?_⟩,
          f'.mono (by decide)⟩
      rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t ⟨rfl, by omega⟩, y0, h2.1]; rfl
    · -- Nothing.
      have hg : gq ord base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false]
        rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t hf] at h2; rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t ⟨hf.1, by omega⟩]; exact h2
      · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega⟩ h5
        · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega]; exact h2

/-- The GHASH state, kept by the data a batch writes. -/
theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block}
    {P : Nat → VG.Spec.Gcm.Block} {y : VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 4 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 4))
    {t t' : State} (h : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 64⟩] t.mem t'.mem) : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : prod (t'.proj 0) = prod (t.proj 0) := by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) 0 (by decide),
      hlane .xmm9 (by decide) (by decide) 0 (by decide), hlane .xmm10 (by decide) (by decide) 0 (by decide)]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact hE.m0⟩,
    by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h1, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk
  · split
    · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t (by assumption)] at h2
      rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2
    · rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by assumption)] at h2
      exact ⟨by rw [kp]; exact h2.1, by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.2⟩

end VG.Proof.Gcm.X86_64.StitchAvx

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Loop`. -/
section

/-!
# Interleaved counter mode and GHASH in AVX: the loops

`group_ok`: a group of four batches (`batch_ok`), with the GHASH work of an
order between their rounds (`gq_ok`), which the data they write does not
undo (`QG.data`). The loops are proven for any powers `P` in the working
space whose products add up to `GHASH` over sixteen blocks (`FinOk`, which
`Proof/Gcm/X86_64/StitchAvx/Ok.lean` proves of the powers the setup
stores), from the state the setup leaves (`Ready`):

* encryption (`encTail_ok`): `EInv s₀ P e s`: `e` groups are encrypted
  (`AInv`), the first `e − 1` hashed into `Y`; `rdx` points to group `e − 1`,
  the next to hash, which a body hashes while it encrypts group `e`
  (`body_ok`); the last group is hashed alone (`final_ok`);
* decryption (`decTail_ok`): `DInv s₀ P e s`: `e` groups are decrypted and
  hashed (the blocks as they were); `rdx` points to group `e`, which a body
  hashes while it decrypts it, each batch reading its own blocks before
  overwriting them (`dbody_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs batch gq group ordE ordD first body dbody ghLoad lastG)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost kp nr cp yp dp nb pp kR cR yR dR pR sch ciph cb hk y₀ bAddr
  blk ctb in_sub in_sub_int in_rdwr addr_eq ghash_append16 nextE_ok nextD_ok store16_ok blocks_ctr32
  blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem toNat_ofNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## A group -/

/-- One batch of a group, the `b`-th of four. -/
theorem batchG_ok {s₀ : State} (hp : SPre s₀) {ord : Nat → Nat} {lo : Nat → Nat} {a : Addr}
    {X P : Nat → VG.Spec.Gcm.Block} {y : VG.Spec.Gcm.Block} {g c b j : Nat} {fin : Bool} (hfin : fin = true → b = 3)
    (hmono : ∀ j', lo j' ≤ lo (j' + 1))
    (hrd : ∀ j', 1 ≤ j' → j' ≤ 4 → ord (4 * b + j' - 1) < 16 ∧ lo j' ≤ ord (4 * b + j' - 1))
    (hsep : ∀ i, lo 10 ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 4))
    (hc : c + 4 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s) (hrdx : (s.gpr .rdx).toNat + 16 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c)
    (hQ : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord (4 * b) fin 1 s) :
    WP isa (batch j (gq ord (4 * b) fin)) s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (c + 4) s' ∧
      VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord (4 * b) fin 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ VG.Proof.Gcm.X86_64.StitchAvx.gRegs → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 64⟩] s.mem s'.mem :=
  VG.Proof.Gcm.X86_64.StitchAvx.batch_ok hp _ VG.Proof.Gcm.X86_64.StitchAvx.gRegs VG.Proof.Gcm.X86_64.StitchAvx.gRegs_ok (VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord (4 * b) fin)
    (VG.Proof.Gcm.X86_64.StitchAvx.gq_ok hmono hrd (fun h => by rw [hfin h]))
    (fun _ _ _ h f => h.yframe f (by decide))
    (fun _ _ h hg' hrd' hwr hl hf => QG.data hp hc hg ha hsep h hg' hrd' hwr hl hf) hc hI hrdx hQ

theorem QG.next {s₀ : State} {lo lo' : Nat → Nat} {a : Addr} {X P : Nat → VG.Spec.Gcm.Block} {y : VG.Spec.Gcm.Block}
    {ord : Nat → Nat} {base base' : Nat} {fin : Bool} {s : State}
    (h : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo a X P y ord base false 10 s) (hl : lo 10 ≤ lo' 1) (hb : base' = base + 4) :
    VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ lo' a X P y ord base' fin 1 s := by
  obtain ⟨hE, h1, h2⟩ := h
  rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by simp)] at h2
  refine ⟨hE.mono hl, h1, ?_⟩
  rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by omega), hb]
  exact h2

theorem frame_group {s₀ : State} {c b : Nat} {m m' : Mem} (h : Frame [⟨bAddr s₀ (c + 4 * b), 64⟩] m m')
    (hb : b < 4) : Frame [⟨bAddr s₀ c, 256⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_cons_self, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩

theorem group_ok {s₀ : State} (hp : SPre s₀) {ord : Nat → Nat} {lo : Nat → Nat → Nat} {a : Addr}
    {X P : Nat → VG.Spec.Gcm.Block} {y : VG.Spec.Gcm.Block} {g c j : Nat}
    (hmono : ∀ b j', lo b j' ≤ lo b (j' + 1)) (hnext : ∀ b, lo b 10 ≤ lo (b + 1) 1)
    (hrd : ∀ b < 4, ∀ j', 1 ≤ j' → j' ≤ 4 → ord (4 * b + j' - 1) < 16 ∧ lo b j' ≤ ord (4 * b + j' - 1))
    (hsep : ∀ b < 4, ∀ i, lo b 10 ≤ i → i < 16 → ¬ (c + 4 * b ≤ 16 * g + i ∧ 16 * g + i < c + 4 * b + 4))
    (hc : c + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s) (hrdx : (s.gpr .rdx).toNat + 16 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c)
    (hQ : VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ (lo 0) a X P y ord 0 false 1 s) :
    WP isa (group ord j) s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (c + 16) s' ∧ VG.Proof.Gcm.X86_64.StitchAvx.QG s₀ (lo 3) a X P y ord 12 true 10 s' ∧
      s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ VG.Proof.Gcm.X86_64.StitchAvx.gRegs → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem := by
  have hs : ∀ b < 4, ∀ i, lo b 10 ≤ i → i < 16 →
      ¬ (c + 4 * b ≤ 16 * g + i ∧ 16 * g + i < c + 4 * b + 4) := hsep
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.batchG_ok (b := 0) (fin := false) hp (fun h => absurd h (by decide)) (hmono 0)
    (hrd 0 (by decide)) (by simpa using hs 0 (by decide)) (by omega) hg ha hI (j := j) hrdx hQ)
    fun s₁ ⟨hA₁, hQ₁, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.batchG_ok (b := 1) (fin := false) hp (fun h => absurd h (by decide)) (hmono 1)
    (hrd 1 (by decide)) (hs 1 (by decide)) (by omega) hg ha hA₁ (j := j + 4) (by rw [hg₁]; omega)
    (QG.next hQ₁ (hnext 0) rfl)) fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.batchG_ok (b := 2) (fin := false) hp (fun h => absurd h (by decide)) (hmono 2)
    (hrd 2 (by decide)) (by simpa [Nat.add_assoc] using hs 2 (by decide)) (by omega) hg ha hA₂ (j := j + 8)
    (by rw [hg₂, hg₁]; omega) (QG.next hQ₂ (hnext 1) rfl)) fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.batchG_ok (b := 3) (fin := true) hp (fun _ => rfl) (hmono 3)
    (hrd 3 (by decide)) (by simpa [Nat.add_assoc] using hs 3 (by decide)) (by omega) hg ha hA₃ (j := j + 12)
    (by rw [hg₃, hg₂, hg₁]; omega) (QG.next hQ₃ (hnext 2) rfl)) fun s₄ ⟨hA₄, hQ₄, hg₄, hl₄, hm₄⟩ => ?_
  refine ⟨by simpa [Nat.add_assoc] using hA₄, hQ₄, by rw [hg₄, hg₃, hg₂, hg₁],
    fun r h13 h14 ha' hg' l hl => by
      rw [hl₄ r h13 h14 ha' hg' l hl, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        hl₁ r h13 h14 ha' hg' l hl], ?_⟩
  exact (VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 0) (by simpa using hm₁) (by decide)).trans
    ((VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 1) hm₂ (by decide)).trans
      ((VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 2) (by simpa [Nat.add_assoc] using hm₃) (by decide)).trans
        (VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 3) (by simpa [Nat.add_assoc] using hm₄) (by decide))))

/-- Clear the product. -/
theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' => prod (s'.proj 0) = Prod.zero ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl (Pclmul.zero_ok (s.proj 0)))
    fun s' ⟨⟨z, o⟩, hi, hg⟩ => ⟨z, hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr,
      fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · refine hi r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h9, h10⟩ := hr
    simp [Impl.Gcm.X86_64.StitchAvx.zero, vdst, h8, h9, h10]

/-- What the products of a group, in the order `ord`, add up to, for the
powers `P`. -/
def FinOk (ord : Nat → Nat) (H : VG.Spec.Gcm.Block) (P : Nat → VG.Spec.Gcm.Block) : Prop :=
  ∀ X y, reduce (VG.Proof.Gcm.X86_64.StitchAvx.accN ord X P y 16) = ghashFrom H y ((List.range 16).map X)

/-- What the setup leaves: nothing encrypted, the powers `P` in the working
space, `Y` in `xmm2`, `rdx` pointing to the data. -/
structure Ready (s₀ : State) (P : Nat → VG.Spec.Gcm.Block) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ 0 s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = y₀ s₀

/-- The powers are kept by the data written. -/
theorem keepP {s₀ : State} (hp : SPre s₀) {c : Nat} {m m' : Mem} (hc : c + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {k : Nat} (hk : k < 16) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 :=
  hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by have := hp.wrap_d; omega))) (by decide)

/-- `GEnv` of group `g`, at `a`, from the encryption after `c` blocks. -/
theorem genv_of {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} {c g : Nat} {a : Addr} {s : State}
    (hA : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c s) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    (hrdx : s.gpr .rdx = a) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k) :
    VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ 0 a (fun i => VG.Spec.Gcm.blockAt s.mem (bAddr s₀ (16 * g + i))) P s :=
  have hw := hp.wrap_d
  { rdx := hrdx
    r11 := hr11
    xs := fun i _ hi => by rw [show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) from addr_eq (by omega)]
    pv := hpw
    ina := fun k hk => by
      rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
        show a + BitVec.ofNat 64 (16 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * g + 16 * k) from addr_eq (by omega)]
      exact in_rdwr (in_sub hp.d_in (by omega))
    inp := fun k hk => by
      rw [hA.rd, hA.wr]
      exact in_rdwr (in_sub_int hp.p_in (by omega))
    m0 := hA.msk }

/-! ## Encryption -/

structure EInv (s₀ : State) (P : Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))

theorem ordE_lt (i : Nat) : ordE i < 16 := Nat.mod_lt _ (by decide)

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s) :
    WP isa body s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.zero_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ := VG.Proof.Gcm.X86_64.StitchAvx.genv_of (P := P) hp hA₁ (g := e - 1) (by omega) ha (by rw [f₁.gpr]) (by rw [f₁.gpr, hr11])
    (fun k hk => by rw [f₁.mem]; exact hI.pw k hk)
  let X : Nat → VG.Spec.Gcm.Block := fun i => VG.Spec.Gcm.blockAt s₁.mem (bAddr s₀ (16 * (e - 1) + i))
  have hX : ∀ i < 16, X i = ctb s₀ (16 * (e - 1) + i) := fun i hi => by
    simp only [X]; rw [hA₁.blocks _ (by omega)]; simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.group_ok (lo := fun _ _ => 0) (y := s.lane .xmm2 0) hp (fun _ _ => Nat.le_refl _)
    (fun _ => Nat.le_refl _) (fun b _ j' _ _ => ⟨VG.Proof.Gcm.X86_64.StitchAvx.ordE_lt _, Nat.zero_le _⟩)
    (fun b _ i _ hi => by omega) (by omega) (by omega) ha hA₁ (j := 16)
    (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, by rw [f₁.lane _ (by decide) 0 (by decide)]; exact hI.m1,
      by rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by decide)]; exact ⟨z₁, by rw [f₁.lane _ (by decide) 0 (by decide)]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1₂, h2⟩ := hQ₂
  rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, by rw [fl]; exact hA₂.ctr, by rw [fl]; exact hA₂.msk, by rw [fl]; exact hA₂.inc,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk => by rw [fm, VG.Proof.Gcm.X86_64.StitchAvx.keepP hp (by omega) hm₂ hk, f₁.mem]; exact hI.pw k hk,
    by rw [fl]; exact h1₂, ?_⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2]
    refine (hf _ _).trans ?_
    rw [show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
    exact congrArg _ (List.map_congr_left fun i hi => hX i (List.mem_range.mp hi))
  · rw [fcf, hr9, VG.Proof.Gcm.X86_64.StitchAvx.toNat_ofNat' (by omega), show e + 1 - 1 = e by omega]

/-- The first group: four batches, with nothing between their rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} {s : State} (hR : VG.Proof.Gcm.X86_64.StitchAvx.Ready s₀ P s) :
    WP isa first s (VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P 1) := by
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  have bt := fun (c j : Nat) (t : State) (hc : c + 4 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hA : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ c t)
      (hrdx : (t.gpr .rdx).toNat + 16 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c) =>
    VG.Proof.Gcm.X86_64.StitchAvx.batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none (fun _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ => trivial) (c := c) (j := j) hc hA hrdx trivial
  have hr : (s.gpr .rdx).toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat := by rw [hR.rdx]
  refine WP.seq (WP.mono (bt 0 0 s (by omega) hR.a (by omega)) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.seq (WP.mono (bt 4 4 s₁ (by omega) hA₁ (by rw [hg₁]; omega)) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.seq (WP.mono (bt 8 8 s₂ (by omega) hA₂ (by rw [hg₂, hg₁]; omega)) fun s₃ ⟨hA₃, _, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (bt 12 12 s₃ (by omega) hA₃ (by rw [hg₃, hg₂, hg₁]; omega)) fun s₄ ⟨hA₄, _, hg₄, hl₄, hm₄⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 2, s₄.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₄ r h13 h14 hr (by simp) l hl, hl₃ r h13 h14 hr (by simp) l hl, hl₂ r h13 h14 hr (by simp) l hl,
      hl₁ r h13 h14 hr (by simp) l hl]
  have gk : s₄.gpr = s.gpr := by rw [hg₄, hg₃, hg₂, hg₁]
  have hm : Frame [⟨bAddr s₀ 0, 256⟩] s.mem s₄.mem :=
    (VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 0) hm₁ (by decide)).trans ((VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 1) hm₂ (by decide)).trans
      ((VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 2) hm₃ (by decide)).trans (VG.Proof.Gcm.X86_64.StitchAvx.frame_group (b := 3) hm₄ (by decide))))
  refine ⟨hA₄, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk => ?_,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact hR.m1,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom]⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [VG.Proof.Gcm.X86_64.StitchAvx.keepP hp (by omega) hm hk]; exact hR.pw k hk

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → VG.Spec.Gcm.Block} {e : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [VG.Proof.Gcm.X86_64.StitchAvx.toNat_ofNat' (by omega)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordE (hk s₀) P) {s : State}
    (hI : VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P 1 s) (hcf : s.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s' := by
  have hm := hp.nbm
  have fin : ∀ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32 → ∀ t, VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e t → ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-- The loads `0 … n − 1` of the order of an encryption group. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block} {y : VG.Spec.Gcm.Block} :
    ∀ n, n ≤ 16 → ∀ s, VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ 0 a X P s → prod (s.proj 0) = Prod.zero → s.lane .xmm2 0 = y →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ordE i))) s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ 0 a X P s' ∧
        prod (s'.proj 0) = VG.Proof.Gcm.X86_64.StitchAvx.accN ordE X P y n ∧ s'.lane .xmm2 0 = y ∧ YFrame VG.Proof.Gcm.X86_64.StitchAvx.gl s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, hz, hy, YFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghRun_ok n (by omega) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghStep (VG.Proof.Gcm.X86_64.StitchAvx.ordE_lt n) (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordE (hk s₀) P) {e : Nat}
    (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 16, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (cR s₀) := fun k hk =>
    hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.zero_ok s₁) fun s₂ ⟨z₂, f₂⟩ => ?_
  let X : Nat → VG.Spec.Gcm.Block := fun i => ctb s₀ (16 * (e - 1) + i)
  have hE₂ : VG.Proof.Gcm.X86_64.StitchAvx.GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true, X]
      pv := fun k hk => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (16 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 16 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := by rw [f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0 }
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghRun_ok (y := s.lane .xmm2 0) 16 (Nat.le_refl _) s₂ hE₂ z₂
    (by rw [f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.ghFin hE₃ (by
      rw [f₃.lane _ (by decide) 0 (by decide), f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]
      exact hI.m1)) fun s₄ ⟨_, y4, f₄⟩ => ?_
  rw [p₃] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₅.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr, he]
  · show VG.Spec.Gcm.blockAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
    rw [show VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = (List.range (16 * e)).map (ctb s₀) from by
        rw [← he]; simp only [VG.Spec.Gcm.blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4, hf, show 16 * e = 16 * ((e - 1) + 1) by omega,
      ghash_append16, ← hI.y]
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordE (hk s₀) P) {s : State}
    (hR : VG.Proof.Gcm.X86_64.StitchAvx.Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (EPost s₀) := by
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.loopE_ok hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => VG.Proof.Gcm.X86_64.StitchAvx.final_ok hp hf he hI₄)

end VG.Proof.Gcm.X86_64.StitchAvx

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Dec`. -/
section

/-!
# Interleaved counter mode and GHASH in AVX: decryption

`DInv s₀ P e s`: `e` groups are decrypted (`AInv`) and hashed into `Y` (the
blocks as they were: the ciphertext); `rdx` points to group `e`. `dbody_ok`:
a body hashes group `e` while it decrypts it (`group_ok`), each batch
reading its own four blocks during its rounds, before it overwrites them.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs group ordD dbody dec)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre DPost nr cp yp dp nb pp cR yR dR pR hk y₀ bAddr blk ctb addr_eq
  ghash_append16 nextD_ok store16_ok blocks_ctr32 blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

structure DInv (s₀ : State) (P : Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 16, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  m1 : s.lane .xmm1 0 = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))

/-- Which blocks of the group the GHASH loads to come still read: before
round 5 of batch `b`, its own and those after; then those after. -/
abbrev loD (b j : Nat) : Nat := if j < 5 then 4 * b else 4 * b + 4

theorem ordD_ok : ∀ b < 4, ∀ j, 1 ≤ j → j ≤ 4 → ordD (4 * b + j - 1) < 16 ∧ VG.Proof.Gcm.X86_64.StitchAvx.loD b j ≤ ordD (4 * b + j - 1) := by
  intro b hb j h1 h4
  simp only [ordD, VG.Proof.Gcm.X86_64.StitchAvx.loD, show j < 5 by omega, ite_true]
  constructor <;> split <;> (try split) <;> omega

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordD (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P e s) :
    WP isa dbody s fun s' => VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, VG.Proof.Gcm.X86_64.StitchAvx.toNat_ofNat' (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.zero_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ := VG.Proof.Gcm.X86_64.StitchAvx.genv_of (P := P) hp hA₁ (g := e) (by omega) ha (by rw [f₁.gpr]) (by rw [f₁.gpr, hr11])
    (fun k hk => by rw [f₁.mem]; exact hI.pw k hk)
  let X : Nat → VG.Spec.Gcm.Block := fun i => VG.Spec.Gcm.blockAt s₁.mem (bAddr s₀ (16 * e + i))
  have hX : ∀ i < 16, X i = blk s₀ (16 * e + i) := fun i hi => by
    simp only [X]; rw [hA₁.blocks _ (by omega)]; simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.group_ok (lo := VG.Proof.Gcm.X86_64.StitchAvx.loD) (y := s.lane .xmm2 0) hp
    (fun b j => by simp only [VG.Proof.Gcm.X86_64.StitchAvx.loD]; split <;> split <;> omega)
    (fun b => by simp only [VG.Proof.Gcm.X86_64.StitchAvx.loD, show ¬ (10 < 5) by decide, show 1 < 5 by decide, ite_false, ite_true]; omega)
    VG.Proof.Gcm.X86_64.StitchAvx.ordD_ok
    (fun b _ i hi _ => by simp only [VG.Proof.Gcm.X86_64.StitchAvx.loD, show ¬ (10 < 5) by decide, ite_false] at hi; omega)
    (by omega) (by omega) ha hA₁ (j := 0)
    (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, by rw [f₁.lane _ (by decide) 0 (by decide)]; exact hI.m1,
      by rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_f (by decide)]; exact ⟨z₁, by rw [f₁.lane _ (by decide) 0 (by decide)]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1₂, h2⟩ := hQ₂
  rw [VG.Proof.Gcm.X86_64.StitchAvx.ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : VG.Proof.Gcm.X86_64.StitchAvx.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, by rw [fl]; exact hA₂.ctr, by rw [fl]; exact hA₂.msk, by rw [fl]; exact hA₂.inc,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk => by rw [fm, VG.Proof.Gcm.X86_64.StitchAvx.keepP hp (by omega) hm₂ hk, f₁.mem]; exact hI.pw k hk,
    by rw [fl]; exact h1₂, ?_⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2]
    refine (hf _ _).trans ?_
    rw [ghash_append16, ← hI.y]
    exact congrArg _ (List.map_congr_left fun i hi => hX i (List.mem_range.mp hi))
  · rw [fcf, hr9, VG.Proof.Gcm.X86_64.StitchAvx.toNat_ofNat' (by omega)]

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} {e : Nat} (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State}
    (hI : VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P e s) : WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₁ (by rw [l₁ _ (by decide) 0 (by decide)]; exact hm0)
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₁, hrcx, m₁, l₁ _ (by decide) 0 (by decide)] at m₂
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr, he]
  · show VG.Spec.Gcm.blockAt s₂.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

/-- The decryption after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordD (hk s₀) P) {s : State}
    (hR : VG.Proof.Gcm.X86_64.StitchAvx.Ready s₀ P s) :
    WP isa (.seq (.loop dbody .ae) (.block (storeCtr ++ storeY))) s (DPost s₀) := by
  have hm := hp.nbm
  have h16 := hp.nb16
  have hI₁ : VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P 0 s :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom]⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchAvx.DInv s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.dbody_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀) s ⟨0, by simp, by omega, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => VG.Proof.Gcm.X86_64.StitchAvx.dfinal_ok hp he hI₂)

end VG.Proof.Gcm.X86_64.StitchAvx

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Ok`. -/
section

/-!
# Interleaved counter mode and GHASH in AVX: the setup and the field

The only module of `Proof/Gcm/X86_64/StitchAvx/` that computes in the field
(`Proof/Gcm/Poly.lean`), so that few modules import its algebra:

* `setup_ok`: the setup stores `H'¹⁶⁻ᵏ` at `scratch + 16 k` (`x · H'ᵏ = Hᵏ`):
  `H'` from the hash subkey (`Pclmul.hInv_ok`), `H'²`–`H'⁸` in a tree
  (`tree_ok`, each step `Pclmul.mul_ok`), stored, and `H'⁹`–`H'¹⁶` as
  products with `H'⁸`, each stored as it is computed; all of it is the SSE
  code of the `VEX.128` instructions (`WP.lane0`). Then `Y`, the counter
  and the pointers (`Ready`).
* `finE`, `finD`: with those powers, the products of a group, in the order
  of an encryption or a decryption group, reduced, are `GHASH` over its
  sixteen blocks (`FinOk`).
* `stitch_ok`: both loops meet their contracts (`StitchOk`).
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod φ_reduce mul_ok const_ok ldrev_ok hInv_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (preg setupG lows highs setupC setup ordE ordD enc dec)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk kp nr cp yp dp nb pp kR cR yR dR pR hk y₀ bAddr blk
  in_sub in_sub_int in_rdwr ghash16)
open VG.Proof.Aes.X86_64.AesNi (one blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt ghashFrom mul)

/-! ## The powers -/

/-- A register of a power: none `mul` writes but its destination, nor the
mask, the reduction constant or `xmm2`. -/
theorem preg_ne (i : Nat) : preg i ≠ .xmm7 ∧ preg i ≠ .xmm8 ∧ preg i ≠ .xmm9 ∧ preg i ≠ .xmm10 ∧
    preg i ≠ .xmm11 ∧ preg i ≠ .xmm0 ∧ preg i ≠ .xmm1 ∧ preg i ≠ .xmm2 := by
  unfold preg; split <;> decide

theorem preg_inj : ∀ i < 8, ∀ j < 8, preg i = preg j → i = j := by decide

theorem pow_mul_pair {H a b d : Q} {m n : Nat} (hd : d = x * a * b) (ha : x * a = H ^ m) (hb : x * b = H ^ n) :
    x * d = H ^ (m + n) := by
  rw [hd, show x * (x * a * b) = (x * a) * (x * b) by ring, ha, hb, pow_add]

/-- One step of the tree: `H'ᵏ⁺¹ = mul(H'ᵃ⁺¹, H'ᵇ⁺¹)` into `preg k`. -/
theorem tree_ok {H : Q} (k a b : Nat) (hk8 : k < 8) (ha : a < k) (hb : b < k) (hab : a + b + 1 = k) (s : State)
    (h1 : s.xmm .xmm1 = poly) (hI : ∀ i < k, x * φ (s.xmm (preg i)) = H ^ (i + 1)) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul (preg k) (preg a) (preg b))) s fun s' =>
      s'.xmm .xmm1 = poly ∧ (∀ i < k + 1, i < 8 → x * φ (s'.xmm (preg i)) = H ^ (i + 1)) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11, preg k] s s' := by
  obtain ⟨-, a8, a9, a10, a11, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne a
  obtain ⟨-, b8, b9, b10, b11, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne b
  obtain ⟨-, k8, k9, k10, k11, -, k1, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne k
  refine WP.mono (mul_ok (preg k) (preg a) (preg b) s a8 a9 a10 a11 b8 b9 b10 b11 k8 k9 k10 k11 h1)
    fun s' ⟨m, o⟩ => ⟨by rw [o.xmm _ (by simp [Ne.symm k1])]; exact h1, fun i hi hi8 => ?_, o⟩
  by_cases hik : i = k
  · subst hik
    rw [VG.Proof.Gcm.X86_64.StitchAvx.pow_mul_pair m (hI a ha) (hI b hb), show a + 1 + (b + 1) = i + 1 by omega]
  · rw [o.xmm _ (by
      obtain ⟨-, i8, i9, i10, i11, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne i
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨i8, i9, i10, i11, fun h => hik (VG.Proof.Gcm.X86_64.StitchAvx.preg_inj i hi8 k hk8 h)⟩)]
    exact hI i (by omega)

/-- The SSE code of `setupG`. -/
def setupGS : List Instr :=
  Impl.Gcm.X86_64.Pclmul.const .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++
  Impl.Gcm.X86_64.Pclmul.const .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .rdi 240), .xop (.bin .pshufb .xmm7 .xmm0)] ++ Impl.Gcm.X86_64.Pclmul.hInv ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 1) (preg 0) (preg 0) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 2) (preg 1) (preg 0) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 3) (preg 1) (preg 1) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 4) (preg 3) (preg 0) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 5) (preg 3) (preg 1) ++ Impl.Gcm.X86_64.Pclmul.mul (preg 6) (preg 3) (preg 2) ++
  Impl.Gcm.X86_64.Pclmul.mul (preg 7) (preg 3) (preg 3)

/-- The SSE code of `lows n`. -/
def lowsS (n : Nat) : List Instr :=
  (List.range n).map fun i => .movdquStore (at_ .r11 (16 * (15 - i))) (preg i)

/-- The SSE code of `highs n`. -/
def highsS (n : Nat) : List Instr :=
  (List.range n).flatMap fun i =>
    Impl.Gcm.X86_64.Pclmul.mul .xmm7 .xmm15 (preg i) ++ [.movdquStore (at_ .r11 (16 * (7 - i))) .xmm7]

theorem lane0_setup : lane0Block (setupG ++ lows 8 ++ highs 8) = some (VG.Proof.Gcm.X86_64.StitchAvx.setupGS ++ VG.Proof.Gcm.X86_64.StitchAvx.lowsS 8 ++ VG.Proof.Gcm.X86_64.StitchAvx.highsS 8) := by
  decide +kernel

theorem only_trans' {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' := h.trans h'

theorem setupGS_ok (t : State) (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) 16) :
    WP isa (.block VG.Proof.Gcm.X86_64.StitchAvx.setupGS) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ i < 8, x * φ (t'.xmm (preg i)) =
        φ (VG.Spec.Gcm.blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int))) ^ (i + 1)) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [VG.Proof.Gcm.X86_64.StitchAvx.setupGS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
  have o₁₄ := (o₁₂.trans o₃).trans o₄
  rw [o₁₂.mem, o₁₂.gpr _ (by decide)] at l₃
  let H := φ (VG.Spec.Gcm.blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)))
  have hH : x * φ (t₄.xmm (preg 0)) = H := by rw [show preg 0 = .xmm3 from rfl, h₄, l₃]
  have p₄ : t₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  have m0 : t₄.xmm .xmm0 = revMask := by
    rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁, rev_eq]
  -- The tree.
  have step : ∀ {k a b : Nat} (hk8 : k < 8) (ha : a < k) (hb : b < k) (hab : a + b + 1 = k) {L : List Instr} {u : State}
      (h1 : u.xmm .xmm1 = poly) (h0 : u.xmm .xmm0 = revMask)
      (hI : ∀ i < k, x * φ (u.xmm (preg i)) = H ^ (i + 1))
      {Q : State → Prop}
      (hq : ∀ u', u'.xmm .xmm1 = poly → u'.xmm .xmm0 = revMask →
        (∀ i < k + 1, i < 8 → x * φ (u'.xmm (preg i)) = H ^ (i + 1)) →
        Only [.xmm8, .xmm9, .xmm10, .xmm11, preg k] u u' → WP isa (.block L) u' Q),
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul (preg k) (preg a) (preg b) ++ L)) u Q := by
    intro k a b hk8 ha hb hab L u h1 h0 hI Q hq
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.tree_ok k a b hk8 ha hb hab u h1 hI) fun u' ⟨h1', hI', o'⟩ => hq u' h1' ?_ hI' o'
    rw [o'.xmm _ (by obtain ⟨-, -, -, -, -, h, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne k; simp [Ne.symm h])]; exact h0
  have f₀ : ∀ i < 1, x * φ (t₄.xmm (preg i)) = H ^ (i + 1) := fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [hH, pow_one]
  refine step (k := 1) (a := 0) (b := 0) (by decide) (by decide) (by decide) rfl p₄ m0 f₀ fun t₅ p₅ m₅ f₅ o₅ => ?_
  refine step (k := 2) (a := 1) (b := 0) (by decide) (by decide) (by decide) rfl p₅ m₅ (fun i hi => f₅ i hi (by omega))
    fun t₆ p₆ m₆ f₆ o₆ => ?_
  refine step (k := 3) (a := 1) (b := 1) (by decide) (by decide) (by decide) rfl p₆ m₆ (fun i hi => f₆ i hi (by omega))
    fun t₇ p₇ m₇ f₇ o₇ => ?_
  refine step (k := 4) (a := 3) (b := 0) (by decide) (by decide) (by decide) rfl p₇ m₇ (fun i hi => f₇ i hi (by omega))
    fun t₈ p₈ m₈ f₈ o₈ => ?_
  refine step (k := 5) (a := 3) (b := 1) (by decide) (by decide) (by decide) rfl p₈ m₈ (fun i hi => f₈ i hi (by omega))
    fun t₉ p₉ m₉ f₉ o₉ => ?_
  refine step (k := 6) (a := 3) (b := 2) (by decide) (by decide) (by decide) rfl p₉ m₉ (fun i hi => f₉ i hi (by omega))
    fun t₁₀ p₁₀ m₁₀ f₁₀ o₁₀ => ?_
  rw [← List.append_nil (Impl.Gcm.X86_64.Pclmul.mul (preg 7) (preg 3) (preg 3))]
  refine step (k := 7) (a := 3) (b := 3) (by decide) (by decide) (by decide) rfl p₁₀ m₁₀ (fun i hi => f₁₀ i hi (by omega))
    fun t' p' m' f' o' => WP.block_nil ?_
  have o := o₁₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans o'))))))
  exact ⟨m', p', fun i hi => f' i (by omega) hi, o.gpr, o.mem, o.rd, o.wr⟩

/-- A 16-byte store to `[r11 + d]`. -/
theorem st_ok (r : XReg) (d : Nat) (t : State)
    (hin : InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .r11 d) r]) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) (t.xmm r) ∧ t'.gpr = t.gpr ∧
      t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (t.gpr .r11 + BitVec.ofInt 64 (d : Int)) (t.xmm r) },
    by simp only [isa, exec, State.store128, Pclmul.ea_at, hin, ite_true], WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The address of slot `k` of the working space. -/
theorem slot_eq (p : Addr) (k : Nat) : p + BitVec.ofInt 64 ((16 * k : Nat) : Int) = p + BitVec.ofNat 64 (16 * k) := by
  rw [BitVec.ofInt_natCast]

theorem readW_slot_self {m : Mem} {p : Addr} {k : Nat} {v : BitVec 128} :
    (m.writeW (p + BitVec.ofNat 64 (16 * k)) v).readW (p + BitVec.ofNat 64 (16 * k)) 128 = v :=
  Mem.readW_writeW_self m _ 16 _ (by decide)

theorem readW_slot_sep {m : Mem} {p : Addr} {k j : Nat} {v : BitVec 128} (hk : k < 16) (hj : j < 16)
    (h : k ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (16 * j)) v).readW (p + BitVec.ofNat 64 (16 * k)) 128 =
      m.readW (p + BitVec.ofNat 64 (16 * k)) 128 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The stores of `lowsS n`, with the working space at `r11`. -/
theorem lowsS_ok (t : State) (hr : ∀ k < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (t.gpr .r11).toNat + 256 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block (VG.Proof.Gcm.X86_64.StitchAvx.lowsS n)) t fun t' =>
      (∀ j < n, t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * (15 - j))) 128 = t.xmm (preg j)) ∧
      (∀ k < 16, k + n < 16 → t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
        t.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) ∧
      Frame [⟨t.gpr .r11, 256⟩] t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [VG.Proof.Gcm.X86_64.StitchAvx.lowsS, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.lowsS_ok t hr hp n (by omega)) fun t₁ ⟨v₁, k₁, f₁, g₁, x₁, rd₁, wr₁⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.st_ok (preg n) (16 * (15 - n)) t₁ (by rw [g₁, wr₁]; exact hr _ (by omega)))
      fun t' ⟨m', g', x', rd', wr'⟩ => ?_
    rw [g₁, x₁, VG.Proof.Gcm.X86_64.StitchAvx.slot_eq] at m'
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, g'.trans g₁, x'.trans x₁, rd'.trans rd₁, wr'.trans wr₁⟩
    · rw [m']
      by_cases hjn : j = n
      · subst hjn; exact VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_self
      · rw [VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_sep (by omega) (by omega) (by omega)]; exact v₁ j (by omega)
    · rw [m', VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_sep hk (by omega) (by omega)]; exact k₁ k hk (by omega)
    · rw [m']
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- The registers `highsS` writes. -/
abbrev hregs : List XReg := [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11]

/-- The products and stores of `highsS n`, with `H'⁸` in `xmm15`. -/
theorem highsS_ok {H : Q} (t : State) (hr : ∀ k < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (t.gpr .r11).toNat + 256 ≤ 2 ^ 64) (h1 : t.xmm .xmm1 = poly)
    (hI : ∀ i < 8, x * φ (t.xmm (preg i)) = H ^ (i + 1)) :
    ∀ n ≤ 8, WP isa (.block (VG.Proof.Gcm.X86_64.StitchAvx.highsS n)) t fun t' =>
      (∀ j < n, x * φ (t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * (7 - j))) 128) = H ^ (9 + j)) ∧
      (∀ k < 16, k + n < 8 ∨ 8 ≤ k → t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
        t.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) ∧
      Frame [⟨t.gpr .r11, 256⟩] t.mem t'.mem ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Gcm.X86_64.StitchAvx.hregs → t'.xmm r = t.xmm r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [VG.Proof.Gcm.X86_64.StitchAvx.highsS, List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.highsS_ok t hr hp h1 hI n (by omega)) fun t₁ ⟨v₁, k₁, f₁, g₁, x₁, rd₁, wr₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    obtain ⟨n7, n8, n9, n10, n11, -⟩ := VG.Proof.Gcm.X86_64.StitchAvx.preg_ne n
    have e15 : t₁.xmm .xmm15 = t.xmm (preg 7) := x₁ _ (by decide)
    have en : t₁.xmm (preg n) = t.xmm (preg n) := x₁ _ (by simp [n7, n8, n9, n10, n11])
    refine WP.mono (mul_ok .xmm7 .xmm15 (preg n) t₁ (by decide) (by decide) (by decide) (by decide) n8 n9 n10 n11
      (by decide) (by decide) (by decide) (by decide) (by rw [x₁ _ (by decide)]; exact h1))
      fun t₂ ⟨m₂, o₂⟩ => ?_
    have hr₂ : t₂.gpr .r11 = t.gpr .r11 := by rw [o₂.gpr _ (by decide), g₁ _ (by decide)]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.st_ok .xmm7 (16 * (7 - n)) t₂ (by rw [hr₂, o₂.wr, wr₁]; exact hr _ (by omega)))
      fun t' ⟨m', g', x', rd', wr'⟩ => ?_
    rw [hr₂, VG.Proof.Gcm.X86_64.StitchAvx.slot_eq, o₂.mem] at m'
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, fun r hr' => by rw [g', o₂.gpr r hr', g₁ r hr'],
      fun r hr' => ?_, by rw [rd', o₂.rd, rd₁], by rw [wr', o₂.wr, wr₁]⟩
    · rw [m']
      by_cases hjn : j = n
      · subst hjn
        rw [VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_self, VG.Proof.Gcm.X86_64.StitchAvx.pow_mul_pair m₂ (by rw [e15]; exact hI 7 (by decide)) (by rw [en]; exact hI j (by omega)),
          show 7 + 1 + (j + 1) = 9 + j by omega]
      · rw [VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_sep (by omega) (by omega) (by omega)]; exact v₁ j (by omega)
    · rw [m', VG.Proof.Gcm.X86_64.StitchAvx.readW_slot_sep hk (by omega) (by omega)]; exact k₁ k hk (by omega)
    · rw [m']
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · simp only [VG.Proof.Gcm.X86_64.StitchAvx.hregs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [x', o₂.xmm r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2]),
        x₁ r (by simp [VG.Proof.Gcm.X86_64.StitchAvx.hregs, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2])]

/-! ## `Y`, the counter, the increment and the pointers -/

theorem setupC_ok (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = VG.Spec.Gcm.blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm14 0 = VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx) ∧
      s'.lane .xmm15 0 = one ∧ s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, ?_, trivial, ?_, trivial, trivial, fun r h1 h2 h3 => ?_, fun r h2 h14 h15 l hl => ?_, trivial,
    trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h14, h15]

/-! ## The setup -/

theorem setupS_ok {s₀ : State} (hp : SPre s₀) (t : State) (hg : t.gpr = s₀.gpr) (hm : t.mem = s₀.mem)
    (hrd : t.rd = s₀.rd) (hwr : t.wr = s₀.wr) :
    WP isa (.block (VG.Proof.Gcm.X86_64.StitchAvx.setupGS ++ VG.Proof.Gcm.X86_64.StitchAvx.lowsS 8 ++ VG.Proof.Gcm.X86_64.StitchAvx.highsS 8)) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ k < 16, x * φ (t'.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) = φ (hk s₀) ^ (16 - k)) ∧
      (∀ r, r ≠ .rax → t'.gpr r = s₀.gpr r) ∧ Frame [pR s₀] s₀.mem t'.mem ∧ t'.rd = s₀.rd ∧ t'.wr = s₀.wr := by
  have hwp := hp.wrap_p
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.setupGS_ok t (by rw [hrd, hwr, hg]; exact in_sub_int hp.k_in (by decide)))
    fun t₁ ⟨m0, m1, pw₁, g₁, mm₁, rd₁, wr₁⟩ => ?_
  have hr11 : t₁.gpr .r11 = pp s₀ := by rw [g₁ _ (by decide), hg]
  have hin : ∀ k < 16, InRegions t₁.wr (t₁.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16 := fun k hk => by
    rw [wr₁, hwr, hr11]; exact in_sub_int hp.p_in (by omega)
  have hH : VG.Spec.Gcm.blockAt t.mem (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) = hk s₀ := by
    rw [hm, hg, BitVec.ofInt_natCast]; rfl
  rw [hH] at pw₁
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.lowsS_ok t₁ hin (by rw [hr11]; omega) 8 (Nat.le_refl _)) fun t₂ ⟨v₂, k₂, f₂, g₂, x₂, rd₂, wr₂⟩ => ?_
  have hin₂ : ∀ k < 16, InRegions t₂.wr (t₂.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16 := fun k hk => by
    rw [wr₂, g₂]; exact hin k hk
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.highsS_ok (H := φ (hk s₀)) t₂ hin₂ (by rw [g₂, hr11]; omega) (by rw [x₂]; exact m1)
    (fun i hi => by rw [x₂]; exact pw₁ i hi) 8 (Nat.le_refl _)) fun t₃ ⟨v₃, k₃, f₃, g₃, x₃, rd₃, wr₃⟩ => ?_
  rw [g₂, hr11] at v₃ k₃ f₃
  rw [hr11] at v₂ k₂ f₂
  refine ⟨by rw [x₃ _ (by decide), x₂]; exact m0, by rw [x₃ _ (by decide), x₂]; exact m1, fun k hk => ?_,
    fun r hr => by rw [g₃ r hr, g₂, g₁ r hr, hg], ?_, by rw [rd₃, rd₂, rd₁, hrd], by rw [wr₃, wr₂, wr₁, hwr]⟩
  · by_cases h8 : 8 ≤ k
    · rw [k₃ k hk (.inr h8), show k = 15 - (15 - k) by omega, v₂ _ (by omega)]
      rw [pw₁ _ (by omega), show 15 - k + 1 = 16 - (15 - (15 - k)) by omega]
    · rw [show k = 7 - (7 - k) by omega, v₃ _ (by omega), show 9 + (7 - k) = 16 - (7 - (7 - k)) by omega]
  · rw [← hm, ← mm₁]; exact f₂.trans f₃

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => VG.Proof.Gcm.X86_64.StitchAvx.Ready s₀ (fun k => s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) s ∧
      ∀ k < 16, x * φ (s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) = φ (hk s₀) ^ (16 - k) := by
  have hwd := hp.wrap_d
  rw [setup, WP.block_append_iff]
  refine WP.mono (WP.lane0 VG.Proof.Gcm.X86_64.StitchAvx.lane0_setup (VG.Proof.Gcm.X86_64.StitchAvx.setupS_ok hp (s₀.proj 0) rfl rfl rfl rfl))
    fun s₁ ⟨⟨m0, m1, pw, g₁, f₁, rd₁, wr₁⟩, _, _⟩ => ?_
  simp only [State.proj_xmm, State.proj_gpr, State.proj_mem, State.proj_rd, State.proj_wr] at m0 m1 pw g₁ f₁ rd₁ wr₁
  have hp₁ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → VG.Spec.Gcm.blockAt s₁.mem p = VG.Spec.Gcm.blockAt s₀.mem p :=
    fun hd => blockAt_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.setupC_ok s₁ m0 (by rw [wr₁, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₁, g₁ _ (by decide)]; exact hp.c_in))
    fun s₂ ⟨y0, c14, c15, r10, rax, rdx, gk, lk, m₂, rd₂, wr₂⟩ => ?_
  refine ⟨⟨⟨Nat.zero_le _, ?_, by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact m0, c15,
    by rw [gk _ (by decide) (by decide) (by decide), g₁ _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide), g₁ _ (by decide)],
    by rw [r10, g₁ _ (by decide), g₁ _ (by decide)], ?_, fun k hk => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩,
    by rw [rdx, g₁ _ (by decide)], by rw [rax, g₁ _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, g₁ r h1], fun k _ => by rw [m₂],
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide)]; exact m1,
    by rw [y0, g₁ _ (by decide), hp₁ hp.p_y.symm]⟩, fun k hk => by rw [m₂]; exact pw k hk⟩
  · rw [c14, g₁ _ (by decide), hp₁ hp.p_c.symm]; rfl
  · rw [m₂]; exact f₁.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₂, hp₁ (hp.d_p.sub_left (Offset.sub_base _ (by omega)))]
    simp only [Nat.not_lt_zero, ite_false]

/-! ## The products of a group, in the field -/

theorem zero_xor' (a : VG.Spec.Gcm.Block) : (0 : VG.Spec.Gcm.Block) ^^^ a = a := by simp

theorem finE {H : VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block} (hP : ∀ k < 16, x * φ (P k) = φ H ^ (16 - k)) : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordE H P := by
  intro X y
  apply φ_inj
  rw [ghash16]
  simp only [VG.Proof.Gcm.X86_64.StitchAvx.accN, ordE, VG.Proof.Gcm.X86_64.StitchAvx.inp, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Gcm.X86_64.StitchAvx.zero_xor']
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  have h0 := hP 0 (by decide)
  have h1 := hP 1 (by decide)
  have h2 := hP 2 (by decide)
  have h3 := hP 3 (by decide)
  have h4 := hP 4 (by decide)
  have h5 := hP 5 (by decide)
  have h6 := hP 6 (by decide)
  have h7 := hP 7 (by decide)
  have h8 := hP 8 (by decide)
  have h9 := hP 9 (by decide)
  have h10 := hP 10 (by decide)
  have h11 := hP 11 (by decide)
  have h12 := hP 12 (by decide)
  have h13 := hP 13 (by decide)
  have h14 := hP 14 (by decide)
  have h15 := hP 15 (by decide)
  simp only [Nat.reduceSub, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  linear_combination (φ y + φ (X 0)) * h0 + φ (X 1) * h1 + φ (X 2) * h2 + φ (X 3) * h3 + φ (X 4) * h4 + φ (X 5) * h5 + φ (X 6) * h6 + φ (X 7) * h7 + φ (X 8) * h8 + φ (X 9) * h9 + φ (X 10) * h10 + φ (X 11) * h11 + φ (X 12) * h12 + φ (X 13) * h13 + φ (X 14) * h14 + φ (X 15) * h15

theorem finD {H : VG.Spec.Gcm.Block} {P : Nat → VG.Spec.Gcm.Block} (hP : ∀ k < 16, x * φ (P k) = φ H ^ (16 - k)) : VG.Proof.Gcm.X86_64.StitchAvx.FinOk ordD H P := by
  intro X y
  apply φ_inj
  rw [ghash16]
  simp only [VG.Proof.Gcm.X86_64.StitchAvx.accN, ordD, VG.Proof.Gcm.X86_64.StitchAvx.inp, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Gcm.X86_64.StitchAvx.zero_xor']
  simp only [φ_xor, φ_reduce, Prod.val_acc, Prod.val_zero, φ_mul]
  have h0 := hP 0 (by decide)
  have h1 := hP 1 (by decide)
  have h2 := hP 2 (by decide)
  have h3 := hP 3 (by decide)
  have h4 := hP 4 (by decide)
  have h5 := hP 5 (by decide)
  have h6 := hP 6 (by decide)
  have h7 := hP 7 (by decide)
  have h8 := hP 8 (by decide)
  have h9 := hP 9 (by decide)
  have h10 := hP 10 (by decide)
  have h11 := hP 11 (by decide)
  have h12 := hP 12 (by decide)
  have h13 := hP 13 (by decide)
  have h14 := hP 14 (by decide)
  have h15 := hP 15 (by decide)
  simp only [Nat.reduceSub, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  linear_combination (φ y + φ (X 0)) * h0 + φ (X 1) * h1 + φ (X 2) * h2 + φ (X 3) * h3 + φ (X 4) * h4 + φ (X 5) * h5 + φ (X 6) * h6 + φ (X 7) * h7 + φ (X 8) * h8 + φ (X 9) * h9 + φ (X 10) * h10 + φ (X 11) * h11 + φ (X 12) * h12 + φ (X 13) * h13 + φ (X 14) * h14 + φ (X 15) * h15

/-! ## The loops -/

theorem enc_ok {s₀ : State} (hp : SPre s₀) : WP isa enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.setup_ok hp) fun _ ⟨hR, hpw⟩ => VG.Proof.Gcm.X86_64.StitchAvx.encTail_ok hp (VG.Proof.Gcm.X86_64.StitchAvx.finE hpw) hR)

theorem dec_ok {s₀ : State} (hp : SPre s₀) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchAvx.setup_ok hp) fun _ ⟨hR, hpw⟩ => VG.Proof.Gcm.X86_64.StitchAvx.decTail_ok hp (VG.Proof.Gcm.X86_64.StitchAvx.finD hpw) hR)

/-- Both loops meet their contracts. -/
theorem stitch_ok : StitchOk enc dec := ⟨fun _ hp => VG.Proof.Gcm.X86_64.StitchAvx.enc_ok hp, fun _ hp => VG.Proof.Gcm.X86_64.StitchAvx.dec_ok hp⟩

end VG.Proof.Gcm.X86_64.StitchAvx

end
