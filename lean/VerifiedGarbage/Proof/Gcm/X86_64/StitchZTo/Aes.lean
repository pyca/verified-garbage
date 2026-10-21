module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# The out-of-place AVX-512 loop: a batch of sixteen blocks

`batchTo_ok`: `StitchZTo.batchTo j g` encrypts the sixteen plaintext blocks
at `rdx + r8 + 64 j` (blocks `c … c + 15`, `r8` holding `src - dst`) into
the output blocks at `rdx + 64 j` (`AInvTo`): the counter blocks and the
rounds as in place (`StitchZ.ctrsG_ok`, `VaesZ.aesZ_ok`), then the XOR of the
plaintext, which nothing writes, into the output (`xorDataZTo_ok`), as
`StitchZ.batch_ok` does in place.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZTo (batchTo)
open VG.Proof.Aes.X86_64.VaesZ (aesZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the slot holding the next group's
counter blocks, the address of `Y` kept after it and in `rcx`, the mask, the
key schedule and its last round key, `src - dst` in `r8`, nothing written but
the output and the working space, and output blocks below `c` the ciphertext
of the plaintext's. -/
structure AInvTo (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  slot : Slot.SlotOk (pp s₀) (cb s₀) (fun i => c + i) s.mem
  ysv : s.mem.readW (pp s₀ + BitVec.ofNat 64 Impl.Gcm.X86_64.Slot.ySave) 64 = yp s₀
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  rcx : s.gpr .rcx = yp s₀
  r11 : s.gpr .r11 = pp s₀
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = sp s₀ - op s₀
  frame : Frame [oR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < c, blockAt s.mem (oAddr s₀ k) = ctbT s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInvTo.zframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvTo s₀ c s)
    (f : ZFrame rs s s') (_h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (_h15 : .xmm15 ∉ rs) : AInvTo s₀ c s' :=
  ⟨h.le, by rw [f.mem]; exact h.slot, by rw [f.mem]; exact h.ysv,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.msk l hl, by rw [f.gpr]; exact h.rcx,
    by rw [f.gpr]; exact h.r11, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-- The encryption state kept by changes of `rdx` and `r9` alone. -/
theorem AInvTo.gpr2 {s₀ : State} {c : Nat} {s s' : State} (h : AInvTo s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hl : ∀ r l, s'.zlane r l = s.zlane r l)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AInvTo s₀ c s' :=
  ⟨h.le, by rw [hm]; exact h.slot, by rw [hm]; exact h.ysv, fun l hl' => by rw [hl]; exact h.msk l hl',
    by rw [hg _ (by decide) (by decide)]; exact h.rcx, by rw [hg _ (by decide) (by decide)]; exact h.r11,
    by rw [hg _ (by decide) (by decide)]; exact h.rdi, by rw [hg _ (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide)]; exact h.r10, by rw [hg _ (by decide) (by decide)]; exact h.r8,
    by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.blocks k hk, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr⟩

theorem keysTo_of {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {s : State} (hrdi : s.gpr .rdi = kp s₀)
    (hf : Frame [oR s₀, pR s₀] s₀.mem s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hrdi]; exact (sch_frame hp.toD hf).symm, by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hrd, hwr, hrdi]
      exact Stitch.in_sub_int hp.toD.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem AInvTo.keys {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  keysTo_of hp hI.rdi hI.frame hI.rd hI.wr

/-- The plaintext is kept by what the loops write. -/
theorem src_of {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {m : Mem} (hf : Frame [oR s₀, pR s₀] s₀.mem m)
    {k : Nat} (hk : k < nb s₀) : blockAt m (sAddr s₀ k) = pblk s₀ k := by
  have hw := hp.wrap_s
  exact blockAt_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_o.sub_left (Offset.sub_base _ (by omega))
    · exact hp.s_p.sub_left (Offset.sub_base _ (by omega))

/-- The plaintext is kept. -/
theorem AInvTo.src {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s)
    {k : Nat} (hk : k < nb s₀) : blockAt s.mem (sAddr s₀ k) = pblk s₀ k :=
  src_of hp hI.frame hk

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

/-- `StitchZ.ctrsG_ok` from `AInvTo`, with the key schedule kept. -/
theorem ctrsTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (Q : State → Prop)
    (hq1 : ∀ s s', Q s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [Slot.slotR (pp s₀)] s.mem s'.mem → Q s')
    {c : Nat} {s : State} (hI : AInvTo s₀ c s) (hQ : Q s) :
    WP isa (.block (Impl.Gcm.X86_64.Slot.ctrsM aregs)) s fun s₁ =>
      (∀ k (h : k < aregs.length), ∀ l < 4,
        s₁.zlane aregs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) revMask) ∧
      Slot.SlotOk (pp s₀) (cb s₀) (fun i => c + 16 + i) s₁.mem ∧ Frame [Slot.slotR (pp s₀)] s.mem s₁.mem ∧
      s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ (∀ r, r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l) ∧
      Frame [oR s₀, pR s₀] s₀.mem s₁.mem ∧ Keys (nr s₀) (sch s₀) s₁ ∧ Q s₁ := by
  refine WP.mono (StitchZ.ctrsG_ok Q hq1 hI.slot hI.ysv hI.rcx hI.r11 hI.wr hp.p_in hQ)
    fun s₁ ⟨e₁, c₁, m₁, g₁, rd₁, wr₁, z₁, hQ₁⟩ => ?_
  have hF₁ : Frame [oR s₀, pR s₀] s₀.mem s₁.mem :=
    hI.frame.trans (m₁.sub fun r hr => ⟨pR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact StitchZ.slot_sub s₀⟩)
  exact ⟨e₁, c₁, m₁, g₁, rd₁, wr₁, z₁, hF₁,
    keysTo_of hp (by rw [g₁]; exact hI.rdi) hF₁ (by rw [rd₁, hI.rd]) (by rw [wr₁, hI.wr]), hQ₁⟩

/-- The plaintext of a group XORed with its keystream in `zmm3` … `zmm6` into
the output (`xorDataZTo_ok`), from a state `s₂` after its counter blocks
(`ctrsTo_ok`) and rounds: `AInvTo` after `c + 16` blocks, and `Q` kept
(`hqx`). -/
theorem xorTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (Q : State → Prop) {c j : Nat}
    (hqx : ∀ s s', Q s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q s')
    (hc : c + 16 ≤ nb s₀) {s s₂ : State} (hI : AInvTo s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c)
    (hS : Slot.SlotOk (pp s₀) (cb s₀) (fun i => c + 16 + i) s₂.mem)
    (hm : Frame [Slot.slotR (pp s₀)] s.mem s₂.mem) (hg : s₂.gpr = s.gpr) (hrd : s₂.rd = s.rd)
    (hwr : s₂.wr = s.wr)
    (hks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)))
    (hmsk : ∀ l < 4, s₂.zlane .xmm0 l = revMask) (hQ : Q s₂) :
    WP isa (.block (Impl.Gcm.X86_64.StitchZTo.xorDataZTo .xmm13 .rdx .r8 aregs j)) s₂ fun s₃ =>
      AInvTo s₀ (c + 16) s₃ ∧ Q s₃ ∧ s₃.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s₃.zlane r l = s₂.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩, Slot.slotR (pp s₀)] s.mem s₃.mem := by
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  have hoS : (oR s₀).Disjoint (Slot.slotR (pp s₀)) := hp.o_p.sub_right (StitchZ.slot_sub s₀)
  have hF₂ : Frame [oR s₀, pR s₀] s₀.mem s₂.mem :=
    hI.frame.trans (hm.sub fun r hr => ⟨pR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact StitchZ.slot_sub s₀⟩)
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) = oAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have saddr : ∀ i, s.gpr .rdx + s.gpr .r8 + BitVec.ofNat 64 (64 * j + 16 * i) = sAddr s₀ (c + i) := fun i => by
    rw [hI.r8]; exact src_addr (addr i)
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega
  refine WP.mono (xorDataZTo_ok .xmm13 .rdx .r8 aregs j s₂ hnd h13 (sR s₀) (oR s₀) hp.s_o
      (fun k hk => by
        rw [hg, hrd, hwr, hI.rd, hI.wr, e64, saddr]
        exact in_sub hp.s_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [hg, hwr, hI.wr, e64, addr]
        exact in_sub hp.o_in (by simp [aregs] at hk; omega))
      (fun k hk l hl => by
        rw [hg, e16, saddr]
        exact Offset.sub_base _ (by simp [aregs] at hk; omega))
      (by
        rw [hg, show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero]
        exact Offset.sub_base _ (by simp [aregs]; omega))
      (by rw [hg]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [hg] at b₃ fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (oAddr s₀ (c + (4 * k + l))) =
        pblk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, addr, saddr, src_of hp hF₂ (by simp [aregs] at h; omega)] at this
  have fr' : Frame [⟨oAddr s₀ c, 256⟩] s₂.mem s₃.mem := by simpa [aregs] using fr₃
  have hdat : Region.Disjoint (Slot.slotR (pp s₀)) ⟨oAddr s₀ c, 256⟩ :=
    hoS.symm.sub_right fun _ ha => VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  have fr₃' : Frame [⟨oAddr s₀ c, 256⟩, Slot.slotR (pp s₀)] s.mem s₃.mem :=
    (hm.mono (by simp)).trans (fr'.mono (by simp))
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg]
  refine ⟨⟨by omega, ?_, ?_, fun l hl => by rw [x₃ _ (by decide) (by decide) l hl, hmsk l hl],
    by rw [gs, hI.rcx], by rw [gs, hI.r11], by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], by rw [gs, hI.r8], ?_, ?_,
    by rw [rd₃, hrd, hI.rd], by rw [wr₃, hwr, hI.wr]⟩,
    hqx s₂ s₃ hQ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) fr', gs, x₃, fr₃'⟩
  · have := hS.frame fr' fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdat
    simpa [Nat.add_assoc] using this
  · rw [← hI.ysv]
    exact fr₃'.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.o_p.sub_right (StitchZ.ysv_sub s₀)).symm.sub_right
          fun _ ha => VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
      · exact StitchZ.ysv_slot s₀) (by decide)
  · -- The data written is only in the output, and the slot in the working space.
    refine hI.frame.trans (fr₃'.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨oR s₀, List.mem_cons_self, fun a ha => VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha⟩
    · exact ⟨pR s₀, by simp, StitchZ.slot_sub s₀⟩
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr₃' fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro a h₁ h₂
          exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂
        · exact hoS.sub_left (Offset.sub_base _ (by omega))]
      exact hI.blocks k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 4) hj (i % 4) (by omega), hks (i / 4) hj (i % 4) (by omega),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (hq1 : ∀ s s', Q 1 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [Slot.slotR (pp s₀)] s.mem s'.mem → Q 1 s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩, Slot.slotR (pp s₀)] s.mem s'.mem := by
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  refine WP.seq (WP.mono (ctrsTo_ok hp (Q 1) hq1 hI hQ) fun s₁ ⟨e₁, c₁, m₁, g₁, rd₁, wr₁, z₁, _, hK₁, hQ₁⟩ => ?_)
  refine WP.seq (WP.mono (aesZ_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [g₁, hI.rsi]; simp)
    (by rw [g₁, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  have k₂ : ∀ r, r ≠ .xmm13 → r ∉ aregs → r ∉ G → ∀ l < 4, s₂.zlane r l = s.zlane r l :=
    fun r h13' hr hg' l hl => by rw [f₂.zlane r (by simp [h13', hr, hg']) l hl, z₁ r hr l hl]
  refine WP.mono (xorTo_ok hp (Q 10) hqx hc hI hrdx (by rw [f₂.mem]; exact c₁) (by rw [f₂.mem]; exact m₁)
    (by rw [f₂.gpr, g₁]) (by rw [f₂.rd, rd₁]) (by rw [f₂.wr, wr₁])
    (fun k h l hl => (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm)
    (fun l hl => by rw [k₂ _ (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]) hQ₂)
    fun s₃ ⟨hA, hQ₃, g₃, x₃, fr₃⟩ =>
      ⟨hA, hQ₃, g₃, fun r h13' _ hr hg' l hl => by rw [x₃ r h13' hr l hl, k₂ r h13' hr hg' l hl], fr₃⟩

end VG.Proof.Gcm.X86_64.StitchZTo
