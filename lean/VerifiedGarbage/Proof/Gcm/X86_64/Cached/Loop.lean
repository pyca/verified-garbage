module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-! ### `Gcm.X86_64.Cached.Aes`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.Cached.Keep`, which this module and modules that import it used -/

section

/-! # The cached GCM loops leave the high registers unchanged -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH
open VG VG.X86_64
open VG.Impl.Aes.X86_64.VaesZH (aes keyOp round)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH

/-- The interleaved work may write low registers, but never cached keys. -/
theorem aes_keeps (rs : List XReg) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (aes rs g).all Instr.keepsH = true := by
  simp [aes, keyOp, round, Code.all, List.all_flatMap, List.all_map, Instr.keepsH, hg]

theorem batch_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) (ix : Bool := false) (ld : Bool := false) :
    (batch j g ix ld).all Instr.keepsH = true := by
  simp [batch, Code.all, aes_keeps _ g hg, ctrsZ, Impl.Gcm.X86_64.StitchZ.xorDataZM, aregs, Instr.keepsH]

theorem gq_keeps (j : Nat) : (Impl.Gcm.X86_64.StitchZ.gq j).all Instr.keepsH = true := by
  unfold Impl.Gcm.X86_64.StitchZ.gq
  split
  · unfold Impl.Gcm.X86_64.StitchZ.ghLoad
    split <;> split <;> rfl
  · split <;> rfl

theorem gq48_keeps (b j : Nat) : (Impl.Gcm.X86_64.StitchZ.gq48 b j).all Instr.keepsH = true := by
  unfold Impl.Gcm.X86_64.StitchZ.gq48
  split
  · unfold Impl.Gcm.X86_64.StitchZ.pair
    cases h : decide (b = 0) <;> rfl
  · split
    · unfold Impl.Gcm.X86_64.StitchZ.pair
      rfl
    · split <;> rfl

theorem gD_keeps (k j : Nat) : (gD k j).all Instr.keepsH = true := by
  unfold gD
  split
  · unfold ldGD
    cases (j == k) <;> by_cases h : j - 1 = 0 <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl
  · split <;> rfl

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-! # A GCM batch using cached AES round keys

`batchM_ok`: `StitchZH.batch j g ix` encrypts the sixteen data blocks at
`rdx + 64 j` into the output, over the data or, out of place (`ix`), at
`rdx + r8 + 64 j` (`StitchZ.AInvM`, `xorDataZM_ok`), as `Stitch.batchM_ok`
does with eight blocks; `batch_ok` is the in-place case. -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp cb dp dR pR bAddr blk ctb ciph sch sch_frame addr_eq in_sub)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (batch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

open VG.Proof.Gcm.X86_64.StitchZ (AInv AInvM AInv.toM aregs_ok)

theorem batchM_ok {ix st ld : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hst : st = (ix && !ld))
    (hld : ld = true → ix = true) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvM ix s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hr8 : ix = true → s.gpr .r8 = if ld then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (Stitch.wp ld s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batch_keeps j g hgh st ld) h)
      (fun t ⟨⟨ha, hq, hg, hl, hf⟩, hh⟩ => ⟨ha, hq, hg, hl, hf, hCache.keep hh (ha.keys hp)⟩)

  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwd := hp.wrap_d
  refine WP.seq (WP.mono (WP.hkeep (by decide) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc)) fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys (hI.keys hp) f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hw := hp.wrap_w
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have hwr : (Stitch.wp ld s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64 := by
    cases ld
    · exact hwd
    · obtain rfl := hld rfl; exact hw
  have raddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) =
      Stitch.wp ld s₀ + BitVec.ofNat 64 (16 * (c + i)) := fun i => addr_eq (by omega_using [hrdx])
  have addr : ∀ i, Stitch.oA s ld + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i => by
    cases ld
    · exact raddr i
    · show s.gpr .rdx + s.gpr .r8 + _ = dp s₀ + _
      rw [hr8 (hld rfl)]
      exact StitchZTo.src_addr (raddr i)
  have oaddr : ∀ i, Stitch.oA s st + BitVec.ofNat 64 (64 * j + 16 * i) = Stitch.wAddr ix s₀ (c + i) := fun i => by
    subst hst
    cases ix <;> cases ld
    · exact raddr i
    · exact absurd (hld rfl) (by decide)
    · show s.gpr .rdx + s.gpr .r8 + _ = Stitch.op s₀ + _
      rw [hr8 rfl]
      exact StitchZTo.src_addr (raddr i)
    · exact raddr i
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega_using []
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega_using []
  have o₂ : Stitch.oA s₂ st = Stitch.oA s st := Stitch.oA_congr st hg₂
  have i₂ : Stitch.oA s₂ ld = Stitch.oA s ld := Stitch.oA_congr ld hg₂
  refine WP.mono (StitchZ.xorDataZM_ok st ld .xmm13 aregs j s₂ hnd h13
      (fun k hk => by
        rw [i₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e64, addr]
        exact in_sub hp.d_in (by simp [aregs] at hk; omega_using [hc, hk]))
      (fun k hk => by
        rw [o₂, f₂.wr, f₁.wr, hI.wr, e64, oaddr]
        exact in_sub hp.w_in (by simp [aregs] at hk; omega_using [hc, hk]))
      (fun a b hab hb l hl => by
        rw [i₂, o₂, e16, show 64 * (j + a) = 64 * j + 16 * (4 * a) by omega_using [], addr, oaddr]
        simp only [aregs, List.length_cons, List.length_nil] at hb
        cases ix
        · cases ld
          · exact Offset.disjoint _ (Or.inr (by omega_using [hab])) (by omega_using [hc, hwd, hb, hl]) (by omega_using [hc, hwd, hab, hb])
          · exact absurd (hld rfl) (by decide)
        · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega_using [hc, hb, hl]))).sub_right
            (Offset.sub_base _ (by omega_using [hc, hab, hb])))
      (by simp only [aregs, List.length_cons, List.length_nil]; omega_using [hc, hrdx, hwr]))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃, _⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, i₂, o₂] at b₃
  rw [hm₂, o₂] at fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega_using [], oaddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (Stitch.wAddr ix s₀ (c + (4 * k + l))) =
        blk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega_using [hc, hl, h]) (by omega_using [])] at this
  have fr' : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  have dsep : ∀ k < nb s₀, c + 16 ≤ k → ∀ r ∈ [(⟨Stitch.wAddr ix s₀ c, 256⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk hck r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    cases ix
    · intro a h₁ h₂
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hwd hk hc (by omega_using [hck]) h₁ h₂
    · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Offset.sub_base _ (by omega_using [hc]))
  refine ⟨⟨by omega_using [hc], fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], ?_, ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2 rfl) l hl, hI.inc l hl]
  · refine hI.frame.trans (fr'.sub fun r hr => ⟨Stitch.wR ix s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega_using [hc, hk]) hc (by omega_using [hlo]) h₁ h₂]
      exact hI.out k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega_using [hlo]⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega_using [hk]
      rw [hb3 (i / 4) hj (i % 4) (by omega_using []), ks (i / 4) hj (i % 4) (by omega_using []),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega_using []]
  · intro k hk hck
    rw [blockAt_frame fr' (dsep k hk hck)]
    exact hI.src k hk (by omega_using [hck])

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (batchM_ok (ld := false) (Stitch.SPre.toM hp) rfl (fun h => absurd h (by decide)) g G hG Q hg hq hqx hc hI.toM
    hCache hgh (fun h => absurd h (by decide)) hrdx hQ)
    fun _ ⟨hA, h⟩ => ⟨hA.toAInv, h⟩

end VG.Proof.Gcm.X86_64.StitchZH

end

end

/-! # GCM groups with cached round keys -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16 blockAt_writeW_sep' blocks_ctr32)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq ghLoad ord setupZ lastG fin)
open VG.Impl.Gcm.X86_64.StitchZH (batch body first dbody)
open VG.Proof.Gcm.X86_64.StitchZ hiding batch_ok body_ok first_ok dbody_ok bodyM_ok firstM_ok
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

theorem body_keeps (ld : Bool) : (body ld).all Instr.keepsH = true := by
  have := batch_keeps 4 gq gq_keeps false ld
  simp_all [body, Code.all, Instr.keepsH]

theorem bodyM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvM ix s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (body ix) s fun s' => EInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (body ix) s fun s' => EInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) from
    WP.mono (WP.hkeepCode (by rfl) (body_keeps ix) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_w
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  have hE₁ : GEnv s₀ 0 a X P s := genvM hp hI.a h1e (by omega_arith) hI.rdx hr11 hI.pw
  have hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (Stitch.wp ix s₀).toNat + 16 * (16 * e) := by
    show a.toNat + _ = _; omega_arith
  have hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hI.r8 rfl
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id gq gRegs gRegs_ok
    (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepW ha
      (fun i _ hi => Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega_arith) hI.a hCache gq_keeps hr8 hrdx₁
    ⟨hE₁, hI.m1, by rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun l hl => rfl⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂, _⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂]
  have hA' : AInvM ix s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega_arith]
    exact hA₂.gpr2 fg fl fm frd fwr
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  refine ⟨⟨hA', by omega_arith, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [fm, keepPM hp (by omega_arith) hm₂ hk hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega_arith)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega_arith, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega_arith, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith), show e + 1 - 1 = e by omega_arith]

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (bodyM_ok (Stitch.SPre.toM hp) hf he hI.toM hCache) fun _ ⟨h, hc, hk⟩ => ⟨h.toEInv, hc, hk⟩

/-- The first group, with nothing between its rounds. -/
theorem firstM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (h16 : 16 ≤ nb s₀) {P : Nat → Nat → Block}
    {s : State} (hR : ReadyM ix s₀ P s) (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (first ix) s fun t => EInvM ix s₀ P 1 t ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) t := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  have hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hR.r8 rfl
  refine WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega_arith) hR.a hCache
    (fun _ => rfl) hr8 (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁, hK₁⟩ => ⟨?_, hK₁⟩
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun hi => by rw [hg₁]; exact hR.r8 hi,
    fun r h1 h2 h3 _ h5 => by rw [hg₁]; exact hR.gpr r h1 h2 h3 h5,
    fun k hk l hl => by rw [keepPM hp (by omega_arith) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide)]; simp

theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa first s fun t => EInv s₀ P 1 t ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) t :=
  WP.mono (firstM_ok (Stitch.SPre.toM hp) hp.nb16 hR.toM hCache) fun _ ⟨h, hk⟩ => ⟨h.toEInv, hk⟩

theorem dbody_keeps (ix : Bool) : (dbody ix).all Instr.keepsH = true := by
  have := batch_keeps 0 gq gq_keeps ix
  simp_all [dbody, Code.all, Instr.keepsH]

theorem dbodyM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInvM ix s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (dbody ix) s fun s' => DInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (dbody ix) s fun s' => DInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) from
    WP.mono (WP.hkeepCode (by rfl) (dbody_keeps ix) h)
      (fun t ⟨⟨hi, hz⟩, hh⟩ => ⟨hi, hz, hCache.keep hh (hi.a.keys hp)⟩)

  have hw := hp.wrap_d
  have hww := hp.wrap_w
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  have f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  have hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega_arith),
          hI.a.src _ (by omega_arith) (by omega_arith)]
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * e + 64 * k) from addr_eq (by omega_arith)]
        exact in_sub hp.d_in (by omega_arith)
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  -- The group is hashed after rounds 1–4, before its blocks are decrypted, and reduced after round 5.
  refine WP.seq (WP.mono (batchM_ok (ld := false) hp (by cases ix <;> rfl) (fun h => absurd h (by decide)) gq gRegs
    gRegs_ok (QG s₀ loD a X P yl)
    (gq_ok (fun j => by simp only [loD]; split <;> split <;> omega_arith) (fun j hj1 hj4 => by
      simp only [loD, show j < 5 by omega_arith, ite_true]; exact Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepM hp (by omega_arith) (by omega_arith) ha
      (fun _ i hi _ => by have : 16 ≤ i := hi; omega_arith) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega_arith) hA₁ hCache gq_keeps (fun hi => by rw [f₁.gpr]; exact hI.r8 hi)
    (by rw [f₁.gpr]; show a.toNat + _ = (dp s₀).toNat + _; omega_arith)
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂, _⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : AInvM ix s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega_arith]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10,
      by rw [fm]; exact hA₂.frame, fun k hk => by rw [fm]; exact hA₂.out k hk,
      fun k hk hc => by rw [fm]; exact hA₂.src k hk hc, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun hi => by rw [gk _ (by decide) (by decide)]; exact hI.r8 hi,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [fm, keepPM hp (by omega_arith) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith)]

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInv s₀ P e s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (dbodyM_ok (Stitch.SPre.toM hp) hf he hI.toM hCache) fun _ ⟨h, hc, hk⟩ => ⟨h.toDInv, hc, hk⟩

end VG.Proof.Gcm.X86_64.StitchZH
