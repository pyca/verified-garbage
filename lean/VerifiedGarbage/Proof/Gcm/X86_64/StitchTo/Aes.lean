import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base

/-!
# The out-of-place VAES loop: a batch of eight blocks

`batchTo_ok`: `StitchTo.batchTo j g` encrypts the eight plaintext blocks at
`rdx + r8 + 32 j` (blocks `c … c + 7`, `r8` holding `src - dst`) into the
output blocks at `rdx + 32 j` (`AInvTo`): the counter blocks and the rounds
as in place (`Vaes.ctrs_ok`, `Vaes.aesG_ok`), then the XOR of the plaintext,
which nothing writes, into the output (`xorDataKTo_ok`), as
`Stitch.batch_ok` does in place.
-/

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Proof.Gcm.X86_64.StitchZTo (dst sAddr pblk ctbT oAddr src_addr)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchTo (batchTo)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the counter pair, the mask, the
increment, the key schedule and its last round key, `src - dst` in `r8`,
nothing written but the output and the working space, and output blocks
below `c` the ciphertext of the plaintext's. -/
structure AInvTo (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = sp s₀ - op s₀
  frame : Frame [oR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < c, blockAt s.mem (oAddr s₀ k) = ctbT s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInvTo.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvTo s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInvTo s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInvTo.keys {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi]; exact (sch_frame hp.toD hI.frame).symm, by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.toD.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

/-- The plaintext is kept. -/
theorem AInvTo.src {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s)
    {k : Nat} (hk : k < nb s₀) : blockAt s.mem (sAddr s₀ k) = pblk s₀ k := by
  have hw := hp.wrap_s
  exact blockAt_frame hI.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_o.sub_left (Offset.sub_base _ (by omega))
    · exact hp.s_p.sub_left (Offset.sub_base _ (by omega))

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨oAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨oAddr s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := Stitch.aregs_ok
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (32 * j + 16 * i) = oAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have saddr : ∀ i, s.gpr .rdx + s.gpr .r8 + BitVec.ofNat 64 (32 * j + 16 * i) = sAddr s₀ (c + i) := fun i => by
    rw [hI.r8]; exact src_addr (addr i)
  have e32 : ∀ k, BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (32 * j + 16 * (2 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) := fun k l => by omega
  refine WP.mono (xorDataKTo_ok .xmm13 .rdx .r8 aregs j s₂ hnd h13 (sR s₀) (oR s₀) hp.s_o
      (fun k hk => by
        rw [hg₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e32, saddr]
        exact in_sub hp.s_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [hg₂, f₂.wr, f₁.wr, hI.wr, e32, addr]
        exact in_sub hp.o_in (by simp [aregs] at hk; omega))
      (fun k hk l hl => by
        rw [hg₂, e16, saddr]
        exact Offset.sub_base _ (by simp [aregs] at hk; omega))
      (by
        rw [hg₂, show 32 * j = 32 * j + 16 * 0 by omega, addr, Nat.add_zero]
        exact Offset.sub_base _ (by simp [aregs]; omega))
      (by rw [hg₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hg₂] at b₃ fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      blockAt s₃.mem (oAddr s₀ (c + (2 * k + l))) =
        pblk s₀ (c + (2 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, addr, saddr, hI.src hp (by simp [aregs] at h; omega)] at this
  have fr' : Frame [⟨oAddr s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], by rw [gs, hI.r8], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the output.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨oR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.blocks k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
      have hj : i / 2 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 2) hj (i % 2) (by omega), ks (i / 2) hj (i % 2) (by omega),
        show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]

end VG.Proof.Gcm.X86_64.StitchTo
