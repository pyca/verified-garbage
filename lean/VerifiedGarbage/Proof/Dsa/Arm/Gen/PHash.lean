module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Add
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: one hash of X

`pHash j` (`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `seed + v` (big-endian, `seedlen` bytes). -/
abbrev seedPlus (G : GP) (sd : List Byte) (v : Nat) : List Byte := Spec.Dsa.encodeBE G.qLen (Spec.Dsa.decodeBE sd + v)

theorem addBE_cert {n : Nat} (hn : n = 20 ∨ n = 32) :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (addBE n) hc).isSome = true := by
  rcases hn with rfl | rfl
  · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (addBE 20), rfl⟩
  · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (addBE 32), rfl⟩

/-- `offset + j` added to the seed at `sMsg`. -/
theorem seedAdd_vp {L j off : Nat} (hL : L = G.pLen) (hq : G.qLen = 20 ∨ G.qLen = 32)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hj : j < 256) (hoff : off + j < 2 ^ 24)
    {sd : List Byte} (hsd : (sMsg, sd) ∈ c.cl) (hsl : sd.length = G.qLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (seedAdd L G.qLen j)
      (St G { c with cl := (sMsg, seedPlus G sd (off + j)) :: cl' } X) := by
  subst hL
  unfold seedAdd
  have hq0 : 0 < G.qLen := by omega
  have e0 : sMsg + G.qLen - 1 = G.qLen - 1 := by simp only [sMsg]; omega
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ?_
    (VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ∧
      s.gpr .r1 = BitVec.ofNat 32 off) ?_
    (VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ∧
      s.gpr .r1 = BitVec.ofNat 32 (off + j)) ?_ ?_))
  · refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block (scr 128 .r0 19)), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8]) fun σ s ⟨h, x⟩ => ?_
    rw [← List.append_nil (scr _ _ _)]
    have := h.gi.scrBig
    exact scr_ok h.r8 rfl h.lens (by simp only [sK, sA, sMsg]; omega) fun t v R M => WP.block_nil
      ⟨⟨h.of_rest R M, x⟩, by rw [v, e0]⟩
  · exact ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide) (x := BitVec.ofNat 32 off)
      (fun σ s h => (h.1.1.slotV hO).trans hOv) fun σ s t ⟨⟨h, x⟩, r0⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r0]⟩, u.gpr⟩
  · refine VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
        (.block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => ?_
    refine wp_dp (op2_imm (encodable_lt hj)) fun t u => WP.block_nil
      ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r0]⟩, ?_⟩
    rw [u.gpr, dpVal, r1, BitVec.ofNat_add]
  · refine VP.taint [.r0] (addBE_cert hq)
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2, h₂.1.2]) fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => ?_
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have hsK : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega
    have hq32 : G.qLen ≤ 32 := by omega
    have a0 : G.sa sMsg = State.addr G.scr := by simp only [GP.sa, sMsg]; rw [BitVec.add_zero]
    have hw : InRegions s.wr (State.addr G.scr) G.qLen := a0 ▸ gi.inScr (o := sMsg) (by simp only [sMsg]; omega)
    refine (addBE_ok (base := G.scr) hq0 (by omega) (by omega) hoff hw r0 r1).mono fun t ⟨e, f, R⟩ => ⟨?_, x⟩
    rw [← a0] at e f
    have b := h.sb (sMsg, sd) hsd
    rw [hsl] at b
    rw [b] at e
    refine h.of_scr R (o := sMsg) (n := G.qLen) (by simp only [sMsg]; omega) (f.mono (by simp)) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
        by simp only [sMsg, VG.Proof.Dsa.encodeBE_length]; omega⟩
    · exact .inl (hcl y hy)

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {σ s : State} (h : SS G σ c s) {B N L : Nat} {md : MdStream.Md B N L} {m : List Byte}
    (hL : L = 8) (hq56 : G.qLen < 56) (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  have b1 := h.sb _ hm
  have b2 := h.sb _ hpad
  have pl := padTail_length md hq56 hL
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega, VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  have a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa G.qLen := by
    simp only [VG.Proof.Bignum.off, GP.sa, sMsg, hml]; rw [BitVec.add_zero]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

/-- The hash of the seed at `k` plus `off + j`, to `dst`. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hj : j < 256) (hoff : off + j < 2 ^ 24)
    (hd1 : 96 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + G.qLen ≤ sA)
    (hpad : (G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  have hq0 : 0 < G.qLen := by omega
  have hq56 : G.qLen < 56 := by omega
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega
  have spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  have hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega), HO.md.digest_length, HO.hN, hk4]
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · exact seedCopy_vp rfl hk hq0 (by omega) (by omega) hsb hS hSv fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hpad, .inr (by simp only [sMsg]; omega)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨m, by simp only [Apart, sMsg] at a ⊢; omega⟩
  · exact seedAdd_vp (c := c1) rfl (by omega) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by simp only [sMsg]; omega)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart, sMsg] at a ⊢; omega⟩
  · refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) rfl (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega, ?_⟩) (by simp only [sState]; omega)
      (by rw [hk4]; omega) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    · exact h.blk_bytes HO.hL hq56 (by simp [c2]) spl (by rw [hpd]; simp [c2])
    refine h.of_scrs R (os := [(sState, 32), (sA, 112), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ (by simpa [GP.rss] using hr)) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [sState, sA, hk4] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, sState, sA] <;> omega
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [hHl]; omega⟩
    · obtain ⟨m, a, b, d⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, sState, sA, hk4] at a b d ⊢ <;> omega

end

end VG.Proof.Dsa.Arm.Gen
