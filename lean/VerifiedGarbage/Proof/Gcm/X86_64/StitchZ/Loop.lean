module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Gcm.X86_64.StitchZ.Aes`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH with AVX-512: a batch of sixteen blocks

`batch_ok`: `StitchZ.batch j g` encrypts the sixteen data blocks at
`rdx + 64 j` (blocks `c … c + 15`, `AInv`): the counter blocks into the four
lanes of `zmm3`–`zmm6` (`VaesZ.ctrsZ_ok`), AES of each lane
(`VaesZ.aesZ_ok`), and the XOR into the data (`VaesZ.xorDataZ_ok`). The
blocks `g i` between the rounds do what `Q` says, which neither the counter
blocks, the rounds nor the XOR (which writes only those sixteen blocks)
undo; as `Stitch.batch_ok` does with eight blocks in two lanes. The blocks `g i`
may write `zmm13`, which the next round reloads.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp cb dp dR pR bAddr blk ctb ciph sch sch_frame addr_eq in_sub)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (batch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok aesZ_ok xorDataZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the four counters, the mask, the
increment, the key schedule and its last round key, and the data (blocks
below `c` encrypted, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  inc : ∀ l < 4, s.zlane .xmm15 l = four
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀, blockAt s.mem (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.zframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInv s₀ c s)
    (f : ZFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInv s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.zlane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.zlane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega_using [h],
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega_using [hj, h])⟩

/-- `AInv`, in place or out of place (`Stitch.AInvM` on four lanes). -/
structure AInvM (ix : Bool) (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  inc : ∀ l < 4, s.zlane .xmm15 l = four
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [Stitch.wR ix s₀, pR s₀] s₀.mem s.mem
  out : ∀ k < c, blockAt s.mem (Stitch.wAddr ix s₀ k) = ctb s₀ k
  src : ∀ k < nb s₀, c ≤ k → blockAt s.mem (bAddr s₀ k) = blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.toM {s₀ : State} {c : Nat} {s : State} (h : AInv s₀ c s) : AInvM false s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, h.frame,
    fun k hk => (h.blocks k (by have := h.le; omega_using [hk, this])).trans (by simp only [hk, ite_true]),
    fun k hk hc => (h.blocks k hk).trans (by simp only [show ¬ k < c by omega_using [hc], ite_false]), h.rd, h.wr⟩

theorem AInvM.toAInv {s₀ : State} {c : Nat} {s : State} (h : AInvM false s₀ c s) : AInv s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, h.frame, fun k hk => by
    by_cases hc : k < c
    · simp only [hc, ite_true]; exact h.out k hc
    · simp only [hc, ite_false]; exact h.src k hk (by omega_using [hc]), h.rd, h.wr⟩

theorem AInvM.zframe {ix : Bool} {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvM ix s₀ c s)
    (f : ZFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInvM ix s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.zlane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.zlane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10,
    by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.out k hk,
    fun k hk hc => by rw [f.mem]; exact h.src k hk hc, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInvM.keys {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {c : Nat} {s : State} (hI : AInvM ix s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, Stitch.sch_frameM hp hI.frame], by rcases hp.rounds with h | h | h <;> omega_using [h],
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega_using [hj, h])⟩

/-! ## The XOR into the output -/

/-- XOR the four lanes of `b` into the blocks read at `Stitch.srcK ld d` …,
and store them to `Stitch.dstK ix d`. -/
theorem xor1ZM_ok (ix ld : Bool) (t : XReg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (Stitch.oA s ld + BitVec.ofInt 64 (d : Int)) 64)
    (hin : InRegions s.wr (Stitch.oA s ix + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load t (VG.Impl.Gcm.X86_64.Stitch.srcK ld d), .zop (.zbin .vpxord b b t),
        .vmovdqu32Store (VG.Impl.Gcm.X86_64.Stitch.dstK ix d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (Stitch.oA s ix + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 4, blockAt s'.mem (Stitch.oA s ix + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (Stitch.oA s ld + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      (∀ l < 4, XBinOp.eval .pshufb (s'.zlane b l) revMask =
        blockAt s'.mem (Stitch.oA s ix + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l))) := by
  let a := Stitch.oA s ix + BitVec.ofInt 64 (d : Int)
  let as := Stitch.oA s ld + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 512
  let s₁ := s.setZ t (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpxord b b t).exec s₁
  obtain l₁ : ∀ l < 4, s₁.zlane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact VG.Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by
    simp only [isa, exec, State.load512, Stitch.ea_srcK, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  obtain hg₂ : s₂.gpr = s.gpr := by simp [s₂, s₁]
  obtain hst : isa.exec (.vmovdqu32Store (VG.Impl.Gcm.X86_64.Stitch.dstK ix d) b) s₂ =
      some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, Stitch.ea_dstK, Stitch.oA_congr ix hg₂, s₂, s₁,
      ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  obtain z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb8, ite_false, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_,
    fun l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [VG.Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl,
      z₂ l hl, VG.Proof.Gcm.X86_64.pshufb_rev_xor, BitVec.xor_comm, ← VG.Proof.Gcm.X86_64.blockAt_eq]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]
  · simp only [State.setMem_mem]
    rw [VG.Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl]
    rfl

/-- `xorDataZM ix t ld regs j`, as `Stitch.xorDataKM_ok` with four lanes. -/
theorem xorDataZM_ok (ix ld : Bool) (t : XReg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (Stitch.oA s ld + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hin : ∀ k < regs.length, InRegions s.wr (Stitch.oA s ix + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hsep : ∀ a b, a < b → b < regs.length → ∀ l < 4,
      Region.Disjoint ⟨Stitch.oA s ld + BitVec.ofNat 64 (16 * (4 * (j + b) + l)), 16⟩
        ⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * (j + a)), 64⟩)
    (hw : 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (VG.Impl.Gcm.X86_64.StitchZ.xorDataZM ix t ld regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        blockAt s'.mem (Stitch.oA s ix + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) =
          blockAt s.mem (Stitch.oA s ld + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      (∀ k (h : k < regs.length), ∀ l < 4, XBinOp.eval .pshufb (s'.zlane regs[k] l) revMask =
        blockAt s'.mem (Stitch.oA s ix + BitVec.ofNat 64 (16 * (4 * (j + k) + l)))) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl, fun _ h => absurd h (by simp)⟩
  | cons b bs ih =>
    obtain hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    obtain hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    obtain h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hsep hw
    rw [VG.Impl.Gcm.X86_64.StitchZ.xorDataZM, WP.block_append_iff]
    obtain hin0 := hin 0 (by omega_using [])
    obtain hinS0 := hinS 0 (by omega_using [])
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1ZM_ok ix ld t b (64 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁, c₁⟩ => ?_
    obtain o₁ : Stitch.oA s₁ ix = Stitch.oA s ix := Stitch.oA_congr ix g₁
    obtain i₁ : Stitch.oA s₁ ld = Stitch.oA s ld := Stitch.oA_congr ld g₁
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, i₁, show j + 1 + k = j + (k + 1) by omega_using []]; exact hinS (k + 1) (by omega_using [hk]))
      (fun k hk => by
        rw [wr₁, o₁, show j + 1 + k = j + (k + 1) by omega_using []]; exact hin (k + 1) (by omega_using [hk]))
      (fun a c hac hc l hl => by
        rw [i₁, o₁, show j + 1 + a = j + (a + 1) by omega_using [], show j + 1 + c = j + (c + 1) by omega_using []]
        exact hsep (a + 1) (c + 1) (by omega_using [hac]) (by omega_using [hc]) l hl)
      (by omega_using [hw])) fun s' ⟨hb, hf, g, rd, wr, hx, hc⟩ => ?_
    rw [i₁, o₁] at hb
    rw [o₁] at hf hc
    rw [VG.Proof.Aes.X86_64.AesNi.ofInt_natCast] at m₁ b₁ c₁
    obtain adr : ∀ (p : Addr), ∀ l < 4, p + BitVec.ofNat 64 (16 * (4 * j + l)) =
        p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega_using []]
    obtain hdj : ∀ l < 4, ∀ r ∈ [(⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨Stitch.oA s ix + BitVec.ofNat 64 (16 * (4 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega_using [hl]) (by omega_using [hw, hl]) (by omega_using [hw])
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_,
      fun k hk l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr _ l hl, b₁ l hl, adr _ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        obtain hk' : k < bs.length := by simpa using hk
        obtain hd := hsep 0 (k + 1) (by omega_using []) (by omega_using [hk']) l hl
        rw [Nat.add_zero] at hd
        rw [show j + (k + 1) = j + 1 + k by omega_using [], hb k hk' l hl, m₁,
          StitchZTo.blockAt_writeW_out (R := ⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega_using []]; exact hd) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨Stitch.oA s ix + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_using [])).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega_using []) (by omega_using []) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hb8 hbs l hl, blockAt_frame hf (hdj l hl), adr _ l hl, c₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        obtain hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega_using []]
        exact hc k hk' l hl

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

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
    (hr8 : ix = true → s.gpr .r8 = if ld then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (Stitch.wp ld s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwd := hp.wrap_d
  refine WP.seq (WP.mono (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  obtain hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys (hI.keys hp) f₁
  obtain hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesZ_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  obtain ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hw := hp.wrap_w
  obtain hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  obtain hwr : (Stitch.wp ld s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64 := by
    cases ld
    · exact hwd
    · obtain rfl := hld rfl; exact hw
  obtain raddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) =
      Stitch.wp ld s₀ + BitVec.ofNat 64 (16 * (c + i)) := fun i => addr_eq (by omega_using [hrdx])
  obtain addr : ∀ i, Stitch.oA s ld + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i => by
    cases ld
    · exact raddr i
    · show s.gpr .rdx + s.gpr .r8 + _ = dp s₀ + _
      rw [hr8 (hld rfl)]
      exact StitchZTo.src_addr (raddr i)
  obtain oaddr : ∀ i, Stitch.oA s st + BitVec.ofNat 64 (64 * j + 16 * i) = Stitch.wAddr ix s₀ (c + i) := fun i => by
    subst hst
    cases ix <;> cases ld
    · exact raddr i
    · exact absurd (hld rfl) (by decide)
    · show s.gpr .rdx + s.gpr .r8 + _ = Stitch.op s₀ + _
      rw [hr8 rfl]
      exact StitchZTo.src_addr (raddr i)
    · exact raddr i
  obtain e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega_using []
  obtain e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega_using []
  obtain o₂ : Stitch.oA s₂ st = Stitch.oA s st := Stitch.oA_congr st hg₂
  obtain i₂ : Stitch.oA s₂ ld = Stitch.oA s ld := Stitch.oA_congr ld hg₂
  refine WP.mono (xorDataZM_ok st ld .xmm13 aregs j s₂ hnd h13
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
  obtain hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, i₂, o₂] at b₃
  rw [hm₂, o₂] at fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega_using [], oaddr, Nat.add_zero] at fr₃
  obtain hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (Stitch.wAddr ix s₀ (c + (4 * k + l))) =
        blk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega_using [hc, hl, h]) (by omega_using [])] at this
  obtain fr' : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  obtain kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  obtain gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  obtain dsep : ∀ k < nb s₀, c + 16 ≤ k → ∀ r ∈ [(⟨Stitch.wAddr ix s₀ c, 256⟩ : Region)],
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
      obtain hj : i / 4 < aregs.length := by simp [aregs]; omega_using [hk]
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
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem :=
  WP.mono (batchM_ok (ld := false) (Stitch.SPre.toM hp) rfl (fun h => absurd h (by decide)) g G hG Q hg hq hqx hc hI.toM
    (fun h => absurd h (by decide)) hrdx hQ) fun _ ⟨hA, h⟩ => ⟨hA.toAInv, h⟩

end VG.Proof.Gcm.X86_64.StitchZ

end

end

/-!
# Interleaved counter mode and GHASH with AVX-512: the loops

`EInv s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the
first `e - 1` hashed into `Y` (lane 0 of `zmm2`, the other lanes 0), the
powers `P` in the working space; `rdx` points to group `e - 1`, the next to
hash. `body_ok`: a body encrypts group `e` (`batch_ok`) while it hashes group
`e - 1` between its rounds (`gq_ok`), which it does not write (`QG.keepW`).
`bodyM_ok`, `firstM_ok` and `finalM_ok` prove the encryption loop for an
output in place or out of place (`EInvM`, over `Stitch.LPre`); the in-place
lemmas and `StitchZTo/Loop.lean`'s are their two cases.
`DInv` and `dbody_ok` are the same for decryption, which hashes each group
during its own rounds, before its blocks are overwritten. The setup is
`Stitch`'s, and then the four lanes (`setupZ_ok`); the stores at the end are
`Stitch`'s. `final_ok` and `dfinal_ok` are the stores after the loops, for
any powers whose products add up to `GHASH` (`FinOk`), without the field;
`StitchZ/Loop48.lean` puts the loops of three groups in front of these.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16 blockAt_writeW_sep' blocks_ctr32)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (batch body gq ghLoad ord setupZ first lastG dbody fin)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## Helpers -/

/-- `vpshufb x, x', ymm0` (`VEX.128`) and a 16-byte store of `x` to `[b]`. -/
theorem store16Z_ok (x x' : XReg) (b : Reg) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr b) 16) :
    WP isa (.block [.vop (.vbin .vpshufb .l128 x x' .xmm0), .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ b 0) x])
      s fun s' => s'.mem = s.mem.writeW (s.gpr b) (XBinOp.eval .pshufb (s.lane x' 0) revMask) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ x → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  obtain hin' : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  simp only [State.lane] at h0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.setV, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, VBinOp.sse, State.lane, ite_true, hin', h0, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  simp [State.zlane, State.lane, hr]

/-! ## The GHASH state, kept by the data written -/

/-- The GHASH state is kept by a write apart from the blocks still to read
(group `g` from `b`) and from the working space. -/
theorem QG.keepW {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {j g : Nat} {R : Region} {b : Addr}
    (ha : a.toNat = b.toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → Region.Disjoint ⟨b + BitVec.ofNat 64 (16 * (16 * g + i)), 16⟩ R)
    (hP : (pR s₀).Disjoint R)
    {t t' : State} (h : QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [R] t.mem t'.mem) : QG s₀ lo a X P yl j t' := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain kp : ∀ l < 4, prod (t'.zproj l) = prod (t.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, hlane .xmm8 (by decide) (by decide) l hl,
      hlane .xmm9 (by decide) (by decide) l hl, hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = b + BitVec.ofNat 64 (16 * (16 * g + i)) := addr_eq (by omega_using [ha])
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hsep i hi hi']
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_using [hk, hl]) (by omega_using [hk, hl]))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hP) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        fun l h1 h4 => by rw [hlane _ (by decide) (by decide) l h4]; exact h2.2 l h1 h4⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun hj l hl => by rw [kp l hl]; exact h2.1 hj l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-- The GHASH state is kept by the sixteen output blocks written: in place,
blocks the loads still to come do not read; out of place, apart from the
data. -/
theorem QG.keepM {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {j c g : Nat}
    (hc : c + 16 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ix = false → ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 16))
    {t t' : State} (h : QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] t.mem t'.mem) : QG s₀ lo a X P yl j t' := by
  have hw := hp.wrap_d
  have hww := hp.wrap_w
  refine QG.keepW ha (fun i hi hi' => ?_) (hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_using [hc]))) h hgpr hrd hwr
    hlane hf
  cases ix
  · intro x h₁ h₂
    exact run_sep hw (by omega_using [hg, hi']) hc (hsep rfl i hi hi') h₁ h₂
  · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega_using [hg, hi']))).sub_right (Offset.sub_base _ (by omega_using [hc]))

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {j c g : Nat}
    (hc : c + 16 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 16))
    {t t' : State} (h : QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] t.mem t'.mem) : QG s₀ lo a X P yl j t' :=
  QG.keepM (Stitch.SPre.toM hp) hc hg ha (fun _ => hsep) h hgpr hrd hwr hlane hf

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The end of an encryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 32`. -/
theorem nextE_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 32)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  obtain e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a decryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 16`. -/
theorem nextD_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 16)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The powers in the working space are kept by the output written. -/
theorem keepPM {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] m m') {k l : Nat} (hk : k < 4) (hl : l < 4) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 := by
  have hw := hp.wrap_w
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) (by decide)

/-- The powers in the working space are kept by the data written. -/
theorem keepP {s₀ : State} (hp : SPre s₀) {c : Nat} (hc : c + 16 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {k l : Nat} (hk : k < 4) (hl : l < 4) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 :=
  keepPM (Stitch.SPre.toM hp) hc hf hk hl

/-- `EInv`, in place or out of place (`Stitch.EInvM` on four lanes): the
output's blocks hashed, `rdx` at the output's group `e - 1`, and, out of
place, the distance from the output to the data in `r8`. -/
structure EInvM (ix : Bool) (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvM ix s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  r8 : ix = true → s.gpr .r8 = dp s₀ - Stitch.op s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem EInv.toM {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EInv s₀ P e s) :
    EInvM false s₀ P e s :=
  ⟨h.a.toM, h.one, h.rdx, h.r9, h.rax, fun h' => absurd h' (by decide),
    fun r h1 h2 _ h4 h5 => h.gpr r h1 h2 h4 h5, h.pw, h.m1, h.y, h.y1⟩

theorem EInvM.toEInv {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : EInvM false s₀ P e s) :
    EInv s₀ P e s :=
  ⟨h.a.toAInv, h.one, h.rdx, h.r9, h.rax, fun r h1 h2 h4 h5 => h.gpr r h1 h2 (fun h' => absurd h' (by decide)) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

/-- `AInv.gpr2`, in place or out of place: the encryption state kept by
changes of `rdx` and `r9` alone. -/
theorem AInvM.gpr2 {ix : Bool} {s₀ : State} {c : Nat} {s s' : State} (h : AInvM ix s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hl : ∀ r l, s'.zlane r l = s.zlane r l)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AInvM ix s₀ c s' :=
  ⟨h.le, fun l hl' => by rw [hl]; exact h.ctr l hl', fun l hl' => by rw [hl]; exact h.msk l hl',
    fun l hl' => by rw [hl]; exact h.inc l hl',
    by rw [hg _ (by decide) (by decide)]; exact h.rdi, by rw [hg _ (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide)]; exact h.r10,
    by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.out k hk,
    fun k hk hc => by rw [hm]; exact h.src k hk hc, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

/-- What hashing output group `e - 1` needs, from `rdx` pointing to it with
its blocks below `c` encrypted. -/
theorem genvM {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} {e c : Nat} {s : State}
    (hA : AInvM ix s₀ c s) (h1e : 1 ≤ e) (hec : 16 * e ≤ c)
    (hrdx : (s.gpr .rdx).toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1)) (hr11 : s.gpr .r11 = pp s₀)
    (hpw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l) :
    GEnv s₀ 0 (s.gpr .rdx) (fun i => ctb s₀ (16 * (e - 1) + i)) P s :=
  have hw := hp.wrap_w
  have := hA.le
  { rdx := rfl
    r11 := hr11
    xs := fun i _ hi => by
      rw [show s.gpr .rdx + BitVec.ofNat 64 (16 * i) = Stitch.wAddr ix s₀ (16 * (e - 1) + i) from
        addr_eq (by omega_arith), hA.out _ (by omega_arith)]
    pv := hpw
    ina := fun k hk => by
      rw [hA.rd, hA.wr, BitVec.ofInt_natCast,
        show s.gpr .rdx + BitVec.ofNat 64 (64 * k) = Stitch.wp ix s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
          addr_eq (by omega_arith)]
      exact in_rdwr (in_sub hp.w_in (by omega_arith))
    inp := fun k hk => by
      rw [hA.rd, hA.wr]
      exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
    m0 := hA.msk }

theorem bodyM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (body ix) s fun s' => EInvM ix s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_w
  have h1e := hI.one
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  obtain hE₁ : GEnv s₀ 0 a X P s := genvM hp hI.a h1e (by omega_arith) hI.rdx hr11 hI.pw
  obtain hrdx₁ : (s.gpr .rdx).toNat + 64 * 4 = (Stitch.wp ix s₀).toNat + 16 * (16 * e) := by
    show a.toNat + _ = _; omega_arith
  obtain hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hI.r8 rfl
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id gq gRegs gRegs_ok
    (QG s₀ (fun _ => 0) a X P yl)
    (gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepW ha
      (fun i _ hi => Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))
      (hp.w_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega_arith) hI.a hr8 hrdx₁
    ⟨hE₁, hI.m1, by rw [ite_f (by decide)]; exact ⟨fun h => absurd h (by decide), fun l hl => rfl⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  obtain gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂]
  obtain hA' : AInvM ix s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega_arith]
    exact hA₂.gpr2 fg fl fm frd fwr
  obtain hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
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
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) :=
  WP.mono (bodyM_ok (Stitch.SPre.toM hp) hf he hI.toM) fun _ ⟨h, hc⟩ => ⟨h.toEInv, hc⟩

/-! ## The setup -/

theorem State.zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (l : Nat) :
    (s.setV .l256 d lo hi).zlane r l =
      if r = d then (if l = 0 then lo else if l = 1 then hi else 0) else s.zlane r l := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega_arith : l = 0 ∨ l = 1 ∨ 2 ≤ l) with rfl | rfl | hl
    · simp
    · simp
    · simp [show ¬ l < 2 by omega_arith, show l ≠ 0 by omega_arith, show l ≠ 1 by omega_arith]
  · simp [h]

theorem paddd_two_two : XBinOp.eval .paddd VG.Proof.Aes.X86_64.Vaes.two VG.Proof.Aes.X86_64.Vaes.two = four := by
  decide

theorem lane0_zlane (t : State) (r : XReg) : t.lane r 0 = t.zlane r 0 := rfl
theorem lane1_zlane (t : State) (r : XReg) : t.lane r 1 = t.zlane r 1 := rfl

theorem shuf44_0 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 0 = a 0 := rfl
theorem shuf44_1 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 1 = a 1 := rfl
theorem shuf44_2 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 2 = b 0 := rfl
theorem shuf44_3 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 3 = b 1 := rfl

structure Ready (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The four lanes, from the two of `Stitch.setup`: the powers of the `k`-th
load are the `2k`-th and `2k + 1`-th of `Stitch`'s. -/
theorem setupZ_run {s : State} {cb : Block}
    (hc : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (0 + l) cb) (hm : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hi : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block setupZ) s fun s' => ((∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l cb) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ∧
      ZFrame [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm1, .xmm2] s s' :=
  WP.zframe (is := setupZ) (rs := [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm1, .xmm2]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l cb) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) (by
  obtain c0 : s.xmm .xmm14 = Nat.repeat inc32 0 cb := by
    obtain h := hc 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  obtain c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 cb := by
    obtain h := hc 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  obtain i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
    obtain h := hi 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  obtain i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
    obtain h := hi 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  obtain m0 : s.xmm .xmm0 = revMask := by
    obtain h := hm 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  obtain m1 : s.ymmHi .xmm0 = revMask := by
    obtain h := hm 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  obtain p0 : s.xmm .xmm1 = poly := by
    obtain h := h1 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  obtain p1 : s.ymmHi .xmm1 = poly := by
    obtain h := h1 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  rw [setupZ]
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
    fun l hl => ?_, ?_, fun l hl1 hl4 => ?_⟩⟩
  all_goals simp only [VOp.exec]
  all_goals try rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals try omega_arith
  all_goals simp (disch := decide) only [lane0_zlane, lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4, State.zlane_setV256,
    State.zlane_setV128, shuf44_0, shuf44_1, shuf44_2, shuf44_3, reduceCtorEq,
    ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
  all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
    show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
  all_goals first
    | exact c0 | exact c1 | exact m0 | exact m1 | exact p0 | exact p1
    | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
    | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
    | (rw [i0]; exact paddd_two_two) | (rw [i1]; exact paddd_two_two))

/-- The state the loops start from, from `Stitch.Ready`. -/
theorem setupZ_ok {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Stitch.Ready s₀ P s) :
    WP isa (.block setupZ) s (Ready s₀ fun k l => P (2 * k + l / 2) (l % 2)) := by
  refine WP.mono (setupZ_run hR.a.ctr hR.a.msk hR.a.inc hR.m1) fun s' ⟨⟨c14, m0, i15, p1, y0, y1⟩, f⟩ => ?_
  have hA := hR.a
  refine ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.zero_add], m0, i15, by rw [f.gpr]; exact hA.rdi,
    by rw [f.gpr]; exact hA.rsi, by rw [f.gpr]; exact hA.r10, by rw [f.mem]; exact hA.frame,
    fun k hk => by rw [f.mem]; exact hA.blocks k hk, by rw [f.rd]; exact hA.rd, by rw [f.wr]; exact hA.wr⟩,
    by rw [f.gpr]; exact hR.rdx, by rw [f.gpr]; exact hR.rax, fun r h1 h2 h3 => by rw [f.gpr]; exact hR.gpr r h1 h2 h3,
    fun k hk l hl => ?_, fun l hl => ?_, by rw [y0]; exact hR.y, y1⟩
  · rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    exact hR.pw _ (by omega_arith) _ (by omega_arith)
  · exact p1 l hl

/-- `Ready`, in place or out of place. -/
structure ReadyM (ix : Bool) (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvM ix s₀ 0 s
  rdx : s.gpr .rdx = Stitch.wp ix s₀
  r8 : ix = true → s.gpr .r8 = dp s₀ - Stitch.op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem Ready.toM {s₀ : State} {P : Nat → Nat → Block} {s : State} (h : Ready s₀ P s) : ReadyM false s₀ P s :=
  ⟨h.a.toM, h.rdx, fun h' => absurd h' (by decide), h.rax, fun r h1 h2 _ h4 => h.gpr r h1 h2 h4, h.pw, h.m1, h.y,
    h.y1⟩

/-- The first group, with nothing between its rounds. -/
theorem firstM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (h16 : 16 ≤ nb s₀) {P : Nat → Nat → Block}
    {s : State} (hR : ReadyM ix s₀ P s) : WP isa (first ix) s (EInvM ix s₀ P 1) := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  obtain hr8 : ix = true → s.gpr .r8 = if ix then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀ := fun hi => by
    subst hi; exact hR.r8 rfl
  refine WP.mono (batchM_ok (st := false) (ld := ix) hp (by cases ix <;> rfl) id (fun _ => []) [] (by simp)
    (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega_arith) hR.a hr8
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun hi => by rw [hg₁]; exact hR.r8 hi,
    fun r h1 h2 h3 _ h5 => by rw [hg₁]; exact hR.gpr r h1 h2 h3 h5,
    fun k hk l hl => by rw [keepPM hp (by omega_arith) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide)]; simp

theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) :=
  WP.mono (firstM_ok (Stitch.SPre.toM hp) hp.nb16 hR.toM) fun _ h => h.toEInv

/-- `cmp r9, 32`. -/
theorem cmpEM_ok {ix : Bool} {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInvM ix s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) :=
  WP.mono (cmpEM_ok hI.toM) fun _ ⟨h, hc⟩ => ⟨h.toEInv, hc⟩

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of a group. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {yl : Nat → Block} :
    ∀ n, n ≤ 4 → ∀ s, GEnv s₀ 0 a X P s → (∀ l < 4, s.zlane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ord i))) s fun s' => GEnv s₀ 0 a X P s' ∧
        (0 < n → ∀ l < 4, prod (s'.zproj l) = accN X P yl l n) ∧ (∀ l < 4, s'.zlane .xmm2 l = yl l) ∧
        ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun h => absurd h (by decide), hy, ZFrame.refl _ _⟩
  | n + 1, hn, s, hE, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ghRun_ok n (by omega_arith) s hE hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (ghStep (by omega_arith) (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨hE', fun _ => p', y', f₁.trans f'⟩

theorem finalM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvM ix s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (Stitch.EPostM ix s₀) := by
  have hw := hp.wrap_w
  have hwp := hp.wrap_p
  have h1e := hI.one
  obtain hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  obtain cD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.w_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain cP : ∀ k < 4, ∀ l < 4, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (Stitch.wp ix s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  obtain hE₂ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [g₁]
      r11 := by rw [g₁]; exact hr11
      xs := fun i _ hi => by
        rw [m₁, show a + BitVec.ofNat 64 (16 * i) = Stitch.wAddr ix s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          blockAt_writeW_sep' (cD _ (by omega_arith)) rfl, hI.a.out _ (by omega_arith)]
      pv := fun k hk l hl => by
        rw [m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = Stitch.wp ix s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.w_in (by omega_arith))
      inp := fun k hk => by
        rw [rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  refine WP.mono (ghRun_ok (yl := yl) 4 (Nat.le_refl _) s₁ hE₂
    (fun l hl => by rw [l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.zlane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ (by decide) 0 (by decide), p₃ (by decide) 1 (by decide), p₃ (by decide) 2 (by decide),
    p₃ (by decide) 3 (by decide)] at y4
  obtain hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), f₄.zlane _ (by decide) 0 (by decide), f₃.zlane _ (by decide) 0 (by decide),
      l₁ _ (by decide) 0 (by decide)]; exact hI.a.msk 0 (by decide)
  obtain g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  obtain hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, wr₁, hI.a.wr, hrcx]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₄, hrcx] at m₅
  obtain m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem]
  rw [m₄, m₁] at m₅
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.w_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₅.mem (Stitch.wAddr ix s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.out k (by omega_arith)
  refine ⟨hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, wr₁, hI.a.wr]⟩
  · show blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₅.mem (yp s₀) = _
    rw [m₅, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), y4]
    refine (hf X yl hI.y1).trans ?_
    rw [he, show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4 h5

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) :=
  WP.mono (finalM_ok (Stitch.SPre.toM hp) hf he hI.toM) fun _ h => h.toEPost

/-! ## Decryption -/

structure DInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- `DInv`, in place or out of place. -/
structure DInvM (ix : Bool) (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvM ix s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  /-- Out of place, the distance from the data to the output. -/
  r8 : ix = true → s.gpr .r8 = Stitch.op s₀ - dp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → (ix = true → r ≠ .r8) → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

theorem DInv.toM {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : DInv s₀ P e s) :
    DInvM false s₀ P e s :=
  ⟨h.a.toM, h.rdx, h.r9, h.rax, fun h' => absurd h' (by decide), fun r h1 h2 _ h4 h5 => h.gpr r h1 h2 h4 h5, h.pw,
    h.m1, h.y, h.y1⟩

theorem DInvM.toDInv {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (h : DInvM false s₀ P e s) :
    DInv s₀ P e s :=
  ⟨h.a.toAInv, h.rdx, h.r9, h.rax, fun r h1 h2 h4 h5 => h.gpr r h1 h2 (fun h' => absurd h' (by decide)) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

/-- Which blocks of the group the GHASH loads to come still read: all until
they are done, after round 4. -/
abbrev loD (j : Nat) : Nat := if j < 5 then 0 else 16

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInv s₀ P e s) :
    WP isa dbody s fun s' => DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.zlane .xmm2 l
  obtain ha : a.toNat = (dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  obtain f₁ : ZFrame [.xmm8, .xmm9, .xmm10] s s := ZFrame.refl _ _
  obtain hE₁ : GEnv s₀ 0 a X P s :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega_arith),
          hI.a.blocks _ (by omega_arith)]
        simp only [show ¬ 16 * e + i < 16 * e by omega_arith, ite_false]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = dp s₀ + BitVec.ofNat 64 (256 * e + 64 * k) from addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  obtain hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  -- The group is hashed after rounds 1–4, before its blocks are decrypted, and reduced after round 5.
  refine WP.seq (WP.mono (batch_ok hp gq gRegs gRegs_ok (QG s₀ loD a X P yl)
    (gq_ok (fun j => by simp only [loD]; split <;> split <;> omega_arith) (fun j hj1 hj4 => by
      simp only [loD, show j < 5 by omega_arith, ite_true]; exact Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega_arith) (by omega_arith) ha
      (fun i hi _ => by have : 16 ≤ i := hi; omega_arith) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega_arith) hA₁ (by rw [f₁.gpr]; show a.toNat + _ = _; omega_arith)
    ⟨hE₁, fun l hl => by
      rw [f₁.zlane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun h => absurd h (by decide), fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  obtain gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  obtain hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega_arith]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  obtain hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, keepP hp (by omega_arith) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [fl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith)]

theorem dfinalM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {P : Nat → Nat → Block} {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : DInvM ix s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (Stitch.DPostM ix s₀) := by
  have hw := hp.wrap_w
  obtain hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  obtain hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  obtain hm0₁ : s₁.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide), State.zlane_lt2 _ _ (by decide)]; exact hm0
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₁ hm0₁
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  obtain e2 : s₁.lane .xmm2 0 = s.zlane .xmm2 0 := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide)]
  rw [g₁, hrcx, m₁, e2] at m₂
  obtain cD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.w_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.w_y.sub_left (Offset.sub_base _ (by omega_arith))
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show blockAt s₂.mem _ = _
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.out k (by omega_arith)
  · show blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₂.mem (yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4 h5

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {e : Nat} (he : nb s₀ = 16 * e) {s : State}
    (hI : DInv s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) :=
  WP.mono (dfinalM_ok (Stitch.SPre.toM hp) he hI.toM) fun _ h => h.toDPost

end VG.Proof.Gcm.X86_64.StitchZ
