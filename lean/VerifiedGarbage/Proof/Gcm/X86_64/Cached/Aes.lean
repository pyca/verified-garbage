module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

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

/-- XOR the four lanes of `b` into the blocks at `rdx + d` …, and store them
to `Stitch.dstK ix d`. -/
theorem xor1ZM_ok (ix : Bool) (t : XReg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 64)
    (hin : InRegions s.wr (Stitch.oA s ix + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load t (VG.Impl.Gcm.X86_64.Pclmul.at_ .rdx d), .zop (.zbin .vpxord b b t),
        .vmovdqu32Store (VG.Impl.Gcm.X86_64.Stitch.dstK ix d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (Stitch.oA s ix + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 4, blockAt s'.mem (Stitch.oA s ix + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr .rdx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := Stitch.oA s ix + BitVec.ofInt 64 (d : Int)
  let as := s.gpr .rdx + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 512
  let s₁ := s.setZ t (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpxord b b t).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact VG.Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by
    simp only [isa, exec, State.load512, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hg₂ : s₂.gpr = s.gpr := by simp [s₂, s₁]
  have hst : isa.exec (.vmovdqu32Store (VG.Impl.Gcm.X86_64.Stitch.dstK ix d) b) s₂ =
      some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, Stitch.ea_dstK, Stitch.oA_congr ix hg₂, s₂, s₁,
      ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb8, ite_false, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [VG.Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl,
      z₂ l hl, VG.Proof.Gcm.X86_64.pshufb_rev_xor, BitVec.xor_comm, ← VG.Proof.Gcm.X86_64.blockAt_eq]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

/-- `xorDataZM ix t regs j`, as `Stitch.xorDataKM_ok` with four lanes. -/
theorem xorDataZM_ok (ix : Bool) (t : XReg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hin : ∀ k < regs.length, InRegions s.wr (Stitch.oA s ix + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hsep : ∀ a b, a < b → b < regs.length → ∀ l < 4,
      Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * (j + b) + l)), 16⟩
        ⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * (j + a)), 64⟩)
    (hw : 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZH.xorDataZM ix t regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        blockAt s'.mem (Stitch.oA s ix + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) =
          blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hsep hw
    rw [VG.Impl.Gcm.X86_64.StitchZH.xorDataZM, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    have hinS0 := hinS 0 (by omega)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1ZM_ok ix t b (64 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have o₁ : Stitch.oA s₁ ix = Stitch.oA s ix := Stitch.oA_congr ix g₁
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hinS (k + 1) (by omega))
      (fun k hk => by
        rw [wr₁, o₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (fun a c hac hc l hl => by
        rw [g₁, o₁, show j + 1 + a = j + (a + 1) by omega, show j + 1 + c = j + (c + 1) by omega]
        exact hsep (a + 1) (c + 1) (by omega) (by omega) l hl)
      (by omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [g₁, o₁] at hb
    rw [o₁] at hf
    rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast] at m₁ b₁
    have adr : ∀ (p : Addr), ∀ l < 4, p + BitVec.ofNat 64 (16 * (4 * j + l)) =
        p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨Stitch.oA s ix + BitVec.ofNat 64 (16 * (4 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr _ l hl, b₁ l hl, adr _ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hd := hsep 0 (k + 1) (by omega) (by omega) l hl
        rw [Nat.add_zero] at hd
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁,
          StitchZTo.blockAt_writeW_out (R := ⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega]; exact hd) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega) (by omega) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

theorem batchM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (g : Nat → List Instr) (G : List XReg)
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
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g ix) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batch j g ix) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batch_keeps j g hgh ix) h)
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
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have oaddr : ∀ i, Stitch.oA s ix + BitVec.ofNat 64 (64 * j + 16 * i) = Stitch.wAddr ix s₀ (c + i) := fun i => by
    cases ix
    · exact addr i
    · show s.gpr .rdx + s.gpr .r8 + _ = Stitch.op s₀ + _
      rw [hI.r8 rfl]
      exact StitchZTo.src_addr (addr i)
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega
  have o₂ : Stitch.oA s₂ ix = Stitch.oA s ix := Stitch.oA_congr ix hg₂
  refine WP.mono (xorDataZM_ok ix .xmm13 aregs j s₂ hnd h13
      (fun k hk => by
        rw [hg₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e64, addr]
        exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [o₂, f₂.wr, f₁.wr, hI.wr, e64, oaddr]
        exact in_sub hp.w_in (by simp [aregs] at hk; omega))
      (fun a b hab hb l hl => by
        rw [hg₂, o₂, e16, show 64 * (j + a) = 64 * j + 16 * (4 * a) by omega, addr, oaddr]
        simp only [aregs, List.length_cons, List.length_nil] at hb
        cases ix
        · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
        · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right
            (Offset.sub_base _ (by omega)))
      (by simp only [aregs, List.length_cons, List.length_nil]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hg₂, o₂] at b₃
  rw [hm₂, o₂] at fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, oaddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (Stitch.wAddr ix s₀ (c + (4 * k + l))) =
        blk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega) (by omega)] at this
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
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hwd hk hc (by omega) h₁ h₂
    · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], fun hi => by rw [gs, hI.r8 hi], ?_, ?_, ?_,
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
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.out k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 4) hj (i % 4) (by omega), ks (i / 4) hj (i % 4) (by omega),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]
  · intro k hk hck
    rw [blockAt_frame fr' (dsep k hk hck)]
    exact hI.src k hk (by omega)

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
  WP.mono (batchM_ok (Stitch.SPre.toM hp) g G hG Q hg hq hqx hc hI.toM hCache hgh hrdx hQ)
    fun _ ⟨hA, h⟩ => ⟨hA.toAInv, h⟩

end VG.Proof.Gcm.X86_64.StitchZH
