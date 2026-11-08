module
public import VerifiedGarbage.Impl.Aes.X86.AesNi
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86.Rev

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-! XOR the encrypted SIMD lanes into writable data. The execution proof
keeps register updates folded, and expresses memory through writeW. -/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ xorData)
open VG.Proof.Gcm.X86 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (blockAt)

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ea_setXmm (s : State) (b : XReg) (v : BitVec 128) (a : MemOp) :
    (s.setXmm b v).ea a = s.ea a := rfl

theorem blockAt_writeW_sep (m : Mem) {p q : Addr} (v : BitVec 128) (h : Mem.Sep q 16 p 16) :
    blockAt (m.writeW p v) q = blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- A block of a region disjoint from the frame's is unchanged. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : blockAt m' p = blockAt m p :=
  Proof.Gcm.blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk


/-- A single lane XOR, with public effective addresses: the block at `esi`
read and the result stored at `d`. -/
theorem xor1_ok (b : XReg) (d : Reg) (o : Nat) (s : State) (hb : b ≠ .xmm7)
    (hinS : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi o)) 16) (hinD : InRegions s.wr (s.ea (at_ d o)) 16) :
    WP isa (.block [.movdquLoad .xmm7 (at_ .esi o), .xop (.bin .pxor b .xmm7),
        .movdquStore (at_ d o) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.ea (at_ d o))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (s.ea (at_ .esi o)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm7 → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, XOp.exec, isa, State.load128, State.store128, ea_setXmm,
    gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm,
    hinS, hinD, hb,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · intro r h1 h2
    simp only [h1, h2, ite_false]

/-- The written bytes represent XOR in the standard's block byte order. -/
theorem blockAt_writeW_xor (m : Mem) (p q : Addr) (x : BitVec 128) :
    blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW q 128))) p =
      blockAt m q ^^^ XBinOp.eval .pshufb x revMask := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide)]
  change XBinOp.eval .pshufb (x ^^^ m.readW q 128) revMask = _
  rw [pshufb_rev_xor, BitVec.xor_comm]

/-- The lanes `regs` XORed into the blocks at `esi` from block `j` on, and
stored at `d`: back to the data (`d = esi`), or to a destination apart. -/
theorem xorData_ok (d : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (h7 : .xmm7 ∉ regs)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hinD : ∀ k < regs.length,
      InRegions s.wr (((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwS : (s.gpr .esi).toNat + 16 * (j + regs.length) ≤ 2 ^ 32)
    (hwD : (s.gpr d).toNat + 16 * (j + regs.length) ≤ 2 ^ 32)
    (hsd : s.gpr .esi = s.gpr d ∨ Region.Disjoint
      ⟨(s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩
      ⟨(s.gpr d).setWidth 64 + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩) :
    WP isa (.block (xorData d regs j)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (((s.gpr .esi).setWidth 64) + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.xmm regs[k]) revMask) ∧
      Frame [⟨((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb7 : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h7' : .xmm7 ∉ bs := fun h => h7 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hinD hwS hwD hsd
    have wS : ((s.gpr .esi).setWidth 64).toNat = (s.gpr .esi).toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.gpr .esi).isLt; omega)
    have wD : ((s.gpr d).setWidth 64).toNat = (s.gpr d).toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.gpr d).isLt; omega)
    rw [xorData, WP.block_append_iff]
    have hinS0 := hinS 0 (by omega)
    have hinD0 := hinD 0 (by omega)
    rw [Nat.add_zero] at hinS0 hinD0
    refine WP.mono (xor1_ok b d (16 * j) s hb7 (by
      rw [ea_mk]; simp only [at_]; rw [addr_eq (by omega)]; exact hinS0) (by
      rw [ea_mk]; simp only [at_]; rw [addr_eq (by omega)]; exact hinD0)) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hbS : (s₁.gpr .esi).setWidth 64 = (s.gpr .esi).setWidth 64 := by rw [g₁]
    have hbD : (s₁.gpr d).setWidth 64 = (s.gpr d).setWidth 64 := by rw [g₁]
    -- The block written is apart from the blocks of the source still to be read.
    have sepW : ∀ k, k < bs.length → Mem.Sep ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * (j + 1 + k))) 16
        ((s.gpr d).setWidth 64 + BitVec.ofNat 64 (16 * j)) 16 := fun k hk => by
      rcases hsd with he | hdis
      · rw [he]; exact Offset.sep _ (by omega) (by omega) (by omega)
      · have e : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * (j + 1 + k)) =
            ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * j)) + BitVec.ofNat 64 (16 * (1 + k)) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
        rw [e]
        refine hdis.sep (Offset.contains_base _ (by omega) (by omega)) ?_
        have := Offset.contains_base ((s.gpr d).setWidth 64 + BitVec.ofNat 64 (16 * j)) (d := 0) (n := 16)
          (k := 16 * (bs.length + 1)) (by omega) (by omega)
        simpa using this
    have hsd' : s₁.gpr .esi = s₁.gpr d ∨ Region.Disjoint
        ⟨(s₁.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩
        ⟨(s₁.gpr d).setWidth 64 + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ := by
      rw [g₁]
      rcases hsd with he | hdis
      · exact .inl he
      · have sub : ∀ (X : Addr), Region.Sub ⟨X + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩
            ⟨X + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩ := fun X => by
          rw [show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
          exact Offset.sub_base _ (by omega)
        exact .inr ((hdis.sub_left (sub _)).sub_right (sub _))
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h7'
        (fun k hk => by
          rw [rd₁, wr₁, hbS, show j + 1 + k = j + (k + 1) by omega]; exact hinS (k + 1) (by omega))
        (fun k hk => by rw [wr₁, hbD, show j + 1 + k = j + (k + 1) by omega]; exact hinD (k + 1) (by omega))
        (by rw [g₁]; omega) (by rw [g₁]; omega) hsd') fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hbS, hbD] at hb
    rw [hbD] at hf
    rw [ea_mk, ea_mk] at m₁
    simp only [at_] at m₁
    rw [addr_eq (x := s.gpr d) (by omega), addr_eq (x := s.gpr .esi) (by omega)] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Offset.toNat_sub_add _ _ (by omega)] at h₁ h₂
      have := (a - (s.gpr d).setWidth 64).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf hdj, m₁, blockAt_writeW_xor]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, blockAt_writeW_sep _ _ (sepW k hk'),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h7' (h ▸ List.getElem_mem hk'))]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨((s.gpr d).setWidth 64) + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Offset.toNat_sub_add _ _ (by omega)] at ha ⊢
      have := (a - (s.gpr d).setWidth 64).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2, x₁ r hr'.1 hr]

end VG.Proof.Aes.X86.AesNi
