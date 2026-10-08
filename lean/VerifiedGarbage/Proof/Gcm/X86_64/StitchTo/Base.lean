import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Impl.Gcm.X86_64.StitchTo

/-!
# The out-of-place VAES loop: the data

Untrusted: everything here is checked by Lean. The out-of-place loop
(`Impl.Gcm.X86_64.StitchTo`) starts from a state `s₀` meeting
`Stitch.SPreTo`, whose in-place view `StitchZTo.dst s₀` (the output in
`r8`) meets `SPre` (`SPreTo.toD`), so that the lemmas of the in-place
proofs about the output, the working space and the GHASH apply to it.

`xorDataKTo_ok`: `xorDataKTo t base idx regs j` XORs the lanes of the
registers into the blocks loaded from `base + idx + 32 (j + i)` and stores
them to `base + 32 (j + i)`, for a source and a destination in disjoint
regions, as `Vaes.xorData_ok` does in place.
-/

namespace VG.Proof.Gcm.X86_64.StitchTo

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchTo (xorDataKTo)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx blockAt_writeW_out)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi)
open VG.Proof.Aes.X86_64.AesNi (ofInt_natCast blockAt_frame eval_pxor)
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- Lane `l` of a 32-byte store, as a block. -/
theorem blockAt_writeW_lane2 (m : Mem) (a : Addr) (v : BitVec 256) {l : Nat} (hl : l < 2) :
    blockAt (m.writeW a v) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (v.extractLsb' (128 * l) 128) revMask := by
  have e := readW_writeW_inside m a v (k := 16 * l) (n := 16) (by omega) (by decide)
  rw [show 8 * (16 * l) = 128 * l by omega] at e
  rw [blockAt_eq, e]

/-- Lane `l` of a 32-byte load. -/
theorem load256_lane (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    (m.readW a 256).extractLsb' (128 * l) 128 = m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using load256_lo m a
  · simpa using load256_hi m a

/-- Lane `l` of a register's 256 bits. -/
theorem ymm_lane2 (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (128 * l) 128 = s.lane r l := by
  rw [State.ymm_eq]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact VG.Proof.Aes.X86_64.Vaes.extract_lo _ _
  · exact VG.Proof.Aes.X86_64.Vaes.extract_hi _ _

/-- XOR the two lanes of `b` into the blocks at `base + idx + d` and the
next, and store them to `base + d` and the next. -/
theorem xor1KTo_ok (t : XReg) (base idx : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)) 32)
    (hin : InRegions s.wr (s.gpr base + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 t (atIx base idx d), .vop (.vbin .vpxor .l256 b b t),
        .vmovdquStore .l256 (at_ base d) b]) s fun s' =>
      (∃ v : BitVec 256, s'.mem = s.mem.writeW (s.gpr base + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 2, blockAt s'.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.lane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let a := s.gpr base + BitVec.ofInt 64 (d : Int)
  let as := s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 256
  let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vbin .vpxor .l256 b b t).exec s₁
  have l₁ : ∀ l < 2, s₁.lane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₁, State.lane_setV256, v]
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_atIx, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (at_ base d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.ymm b))) := by
    simp only [isa, exec, State.store256_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, s₂, s₁, VOp.exec_gpr,
      State.setV_gpr, VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 2, s₂.lane b l = s.lane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, lane_vbin256, ite_true, VBinOp.sse, ← l₁ l hl]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [s₁, State.lane_setV256, hb8, eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [blockAt_writeW_lane2 _ _ _ hl, ymm_lane2 _ _ hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq]
  · simp [s₂, s₁, lane_vbin256, State.lane_setV256, h1, h2]

theorem xorDataKTo_ok (t : XReg) (base idx : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs) (S D : Region) (hSD : S.Disjoint D)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr base + s.gpr idx + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hS : ∀ k < regs.length, ∀ l < 2,
      Region.Sub ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (2 * (j + k) + l)), 16⟩ S)
    (hD : Region.Sub ⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩ D)
    (hw : (s.gpr base).toNat + 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataKTo t base idx regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        blockAt s'.mem (s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) =
          blockAt s.mem (s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.lane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hS hD hw
    rw [xorDataKTo, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    have hinS0 := hinS 0 (by omega)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1KTo_ok t base idx b (32 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hD₁ : Region.Sub ⟨s.gpr base + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ D :=
      fun a ha => hD a (Offset.sub _ (by omega) (by omega) a ha)
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hinS (k + 1) (by omega))
      (fun k hk => by
        rw [wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (fun k hk l hl => by
        rw [g₁, show j + 1 + k = j + (k + 1) by omega]; exact hS (k + 1) (by omega) l hl)
      (by rw [g₁]; exact hD₁) (by rw [g₁]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [g₁] at hb hf
    rw [ofInt_natCast] at m₁ b₁
    have adr : ∀ (p : Addr), ∀ l < 2, p + BitVec.ofNat 64 (16 * (2 * j + l)) =
        p + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 16 * l = 16 * (2 * j + l) by omega]
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr base + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    -- The write of the first register is in `D`, apart from the plaintext blocks still to read.
    have hW : ∀ k < bs.length + 1, ∀ l < 2, Region.Disjoint
        ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (2 * (j + k) + l)), 16⟩
        ⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32⟩ := fun k hk l hl =>
      (hSD.sub_left (hS k hk l hl)).sub_right fun a ha => hD a (Region.sub_prefix (by omega) a ha)
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr _ l hl, b₁ l hl, adr _ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁,
          blockAt_writeW_out (R := ⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega]; exact hW (k + 1) (by omega) l hl) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega) (by omega) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

end VG.Proof.Gcm.X86_64.StitchTo
