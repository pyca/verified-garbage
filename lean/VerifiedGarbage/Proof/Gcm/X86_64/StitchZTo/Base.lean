import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZTo

/-!
# The out-of-place AVX-512 loop: the setting, and the data

Untrusted: everything here is checked by Lean. The out-of-place loop
(`Impl.Gcm.X86_64.StitchZTo`) starts from a state `s₀` meeting
`Stitch.SPreTo`. `dst s₀` is `s₀` with the output in `r8`, where the in-place
loops find their data: it meets `SPre` (`SPreTo.toD`), so that the lemmas of
the in-place proofs about the output, the working space and the GHASH
(stated for any state, through `dp`, `pp`, `bAddr`, …) apply to it. The
plaintext is block `k` at `sAddr s₀ k` (`pblk`), its ciphertext `ctbT`.

`xorDataZTo_ok`: `xorDataZTo t base idx regs j` XORs the lanes of the
registers into the blocks loaded from `base + idx + 64 (j + i)` and stores
them to `base + 64 (j + i)`, for a source and a destination in disjoint
regions, as `VaesZ.xorDataZ_ok` does in place.
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreP SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx xorDataZTo)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane zmm_lane blockAt_writeW_lane)
open VG.Proof.Aes.X86_64.AesNi (ofInt_natCast inRegions_wr blockAt_frame)
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-! ## The in-place view -/

/-- `s₀` with the output in `r8`. -/
def dst (s₀ : State) : State := s₀.setReg .r8 (s₀.gpr .r10)

theorem dst_mem (s₀ : State) : (dst s₀).mem = s₀.mem := rfl
theorem dst_gpr_ne (s₀ : State) {r : Reg} (h : r ≠ .r8) : (dst s₀).gpr r = s₀.gpr r := by
  simp [dst, State.setReg, h]
theorem nb_dst (s₀ : State) : nb (dst s₀) = nb s₀ := rfl
theorem dp_dst (s₀ : State) : dp (dst s₀) = op s₀ := rfl

theorem inRegions_prefix {rs : List Region} {a : Addr} {n L : Nat} (h : InRegions rs a L) (hn : n ≤ L) :
    InRegions rs a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, by unfold Region.Contains at *; omega⟩

/-- The in-place loops' view of the out-of-place one's start. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPreTo.toD {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) : SPre (dst s₀) where
  rounds := hp.rounds
  nb16 := hp.nb16
  k_in := inRegions_prefix hp.k_in M.ge
  c_in := hp.c_in
  y_in := hp.y_in
  d_in := hp.o_in
  p_in := hp.p_in
  d_k := hp.k_o.symm.sub_right (Region.sub_prefix M.ge)
  d_c := hp.o_c
  d_y := hp.o_y
  d_p := hp.o_p
  p_k := hp.k_p.symm.sub_right (Region.sub_prefix M.ge)
  p_c := hp.p_c
  p_y := hp.p_y
  c_y := hp.c_y
  c_k := hp.k_c.symm.sub_right (Region.sub_prefix M.ge)
  y_k := hp.k_y.symm.sub_right (Region.sub_prefix M.ge)
  wrap_d := hp.wrap_o
  wrap_k := by
    have := hp.wrap_k; have := M.ge
    show (kp s₀).toNat + 256 ≤ 2 ^ 64; omega
  wrap_p := hp.wrap_p

/-- The same, with the powers in the key context. -/
theorem _root_.VG.Proof.Gcm.X86_64.Stitch.SPreTo.toP {s₀ : State} (hp : SPreTo CtxMode.powers s₀) : SPreP (dst s₀) :=
  ⟨hp.toD, hp.k_in, hp.wrap_k, hp.k_o.symm, hp.k_p.symm, hp.ok⟩

/-! ## The plaintext and the ciphertext -/

section
variable (s₀ : State)

/-- Block `k` of the plaintext, where it starts, and encrypted; where block
`k` of the output starts. -/
abbrev sAddr (k : Nat) : Addr := sp s₀ + BitVec.ofNat 64 (16 * k)
abbrev pblk (k : Nat) : Block := blockAt s₀.mem (sAddr s₀ k)
abbrev ctbT (k : Nat) : Block := pblk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀))
abbrev oAddr (k : Nat) : Addr := op s₀ + BitVec.ofNat 64 (16 * k)

end

/-- The source address of the output address `r + x`, `r8` holding
`src - dst`. -/
theorem src_addr {r o s : Addr} {x y : Nat} (h : r + BitVec.ofNat 64 x = o + BitVec.ofNat 64 y) :
    r + (s - o) + BitVec.ofNat 64 x = s + BitVec.ofNat 64 y := by
  rw [BitVec.add_assoc, BitVec.add_comm (s - o), ← BitVec.add_assoc, h, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 y), ← BitVec.add_assoc, BitVec.add_comm o (s - o), BitVec.sub_add_cancel]

/-! ## The data -/

theorem ea_atIx (s : State) (b i : Reg) (d : Nat) :
    s.ea (atIx b i d) = s.gpr b + s.gpr i + BitVec.ofInt 64 (d : Int) := by
  show s.gpr b + s.gpr i * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.mul_one]

/-- XOR the four lanes of `b` into the blocks at `base + idx + d` … and store
them to `base + d` …. -/
theorem xor1ZTo_ok (t : XReg) (base idx : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)) 64)
    (hin : InRegions s.wr (s.gpr base + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Load t (atIx base idx d), .zop (.zbin .vpxord b b t),
        .vmovdqu32Store (at_ base d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr base + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 4, blockAt s'.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := s.gpr base + BitVec.ofInt 64 (d : Int)
  let as := s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 512
  let s₁ := s.setZ t (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpxord b b t).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_atIx, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ base d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, s₂, s₁, ZOp.exec_gpr,
      State.setZ_gpr, ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb8, ite_false, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

/-- A block disjoint from a region written is kept. -/
theorem blockAt_writeW_out {m : Mem} {p : Addr} {R : Region} {w : Nat} {v : BitVec w}
    (hd : Region.Disjoint ⟨p, 16⟩ R) (hw : w / 8 = R.len) : blockAt (m.writeW R.base v) p = blockAt m p :=
  Stitch.blockAt_writeW_sep' hd hw

theorem xorDataZTo_ok (t : XReg) (base idx : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs) (S D : Region) (hSD : S.Disjoint D)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr base + s.gpr idx + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hS : ∀ k < regs.length, ∀ l < 4,
      Region.Sub ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (4 * (j + k) + l)), 16⟩ S)
    (hD : Region.Sub ⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩ D)
    (hw : (s.gpr base).toNat + 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataZTo t base idx regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        blockAt s'.mem (s.gpr base + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) =
          blockAt s.mem (s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (4 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hS hD hw
    rw [xorDataZTo, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    have hinS0 := hinS 0 (by omega)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1ZTo_ok t base idx b (64 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hD₁ : Region.Sub ⟨s.gpr base + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ D :=
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
    have adr : ∀ (p : Addr), ∀ l < 4, p + BitVec.ofNat 64 (16 * (4 * j + l)) =
        p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * j + 16 * l = 16 * (4 * j + l) by omega]
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨s.gpr base + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + BitVec.ofNat 64 (16 * (4 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    -- The write of the first register is in `D`, apart from the plaintext blocks still to read.
    have hW : ∀ k < bs.length + 1, ∀ l < 4, Region.Disjoint
        ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (4 * (j + k) + l)), 16⟩
        ⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64⟩ := fun k hk l hl =>
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
          blockAt_writeW_out (R := ⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega]; exact hW (k + 1) (by omega) l hl) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (64 * j), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega) (by omega) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]

end VG.Proof.Gcm.X86_64.StitchZTo
