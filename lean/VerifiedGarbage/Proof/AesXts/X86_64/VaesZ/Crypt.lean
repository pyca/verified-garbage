module

public import VerifiedGarbage.Impl.AesXts.X86_64VaesZ
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Top
public import VerifiedGarbage.Proof.AesXts.X86_64.VaesTo.Crypt
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Body
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Dec
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Tail
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Call

/-!
# XTS-AES with AVX-512 VAES on x86-64: correctness

`encrypt_wp`, `decrypt_wp`, `VaesTo.encryptTo_wp` and `VaesTo.decryptTo_wp`:
the functions of `Impl/AesXts/X86_64VaesZ.lean` meet the contracts of their
in-place and out-of-place counterparts with 256-bit registers. Section by
section below: the operations on 512-bit registers, the sixteen-block loop
in place, and the same out of place.
-/

@[expose] public section

/-! ## XTS-AES with AVX-512 VAES on x86-64: the operations on 512-bit registers

The lanes of the EVEX.512 byte shifts and carry-less multiply
(`zlane_vpsrldqZ`, `zlane_vpslldqZ`, `zlane_vpclmulZ`); `stepZ_ok`: the four
tweaks in a register times `α⁸` (`Vaes.stepW`, as `Vaes.stepT_ok` proves of
two); `constKZ_ok`: `0x87` in the four lanes of `zmm11`; `pre1Z_ok` and
`post1Z_ok`: four blocks loaded with their tweaks XORed in, and XORed again
and stored.
-/

namespace VG.Proof.AesXts.X86_64.VaesZ

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.AesXts.X86_64VaesZ (stepZ constKZ)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane zmm_lane)
open VG.Proof.AesXts.X86_64.Vaes (stepW pclmul_step psrldq_15 pslldq_1)

@[simp] theorem zlane_vpsrldqZ (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpsrldq d a n).exec s).zlane r i =
      if r = d then XShiftOp.psrldq.eval (s.zlane a i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => XShiftOp.psrldq.eval (s.zlane a i) n) hi]

@[simp] theorem zlane_vpslldqZ (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpslldq d a n).exec s).zlane r i =
      if r = d then XShiftOp.pslldq.eval (s.zlane a i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => XShiftOp.pslldq.eval (s.zlane a i) n) hi]

@[simp] theorem zlane_vpclmulZ (d a b : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpclmulqdq d a b n).exec s).zlane r i =
      if r = d then pclmul (s.zlane a i) (s.zlane b i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => pclmul (s.zlane a i) (s.zlane b i) n) hi]

/-- `d := t · α⁸` in each of the four lanes. -/
theorem stepZ_ok (d t : XReg) (h9 : t ≠ .xmm9) (h10 : t ≠ .xmm10) (s : State)
    (hK : ∀ l < 4, qword (s.zlane .xmm11 l) 0 = 0x87) :
    WP isa (.block (stepZ d t)) s fun s' =>
      (∀ l < 4, s'.zlane d l = stepW (s.zlane t l)) ∧ ZFrame [d, .xmm9, .xmm10] s s' := by
  let s₁ := (ZOp.vpsrldq .xmm10 t 15).exec s
  let s₂ := (ZOp.vpclmulqdq .xmm10 .xmm10 .xmm11 0).exec s₁
  let s₃ := (ZOp.vpslldq .xmm9 t 1).exec s₂
  let s₄ := (ZOp.zbin .vpxord d .xmm9 .xmm10).exec s₃
  rw [stepZ, WP.block_cons_iff]; refine ⟨s₁, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₄, rfl, WP.block_nil ?_⟩
  have n910 : (XReg.xmm9 = XReg.xmm10) = False := by decide
  have n1011 : (XReg.xmm11 = XReg.xmm10) = False := by decide
  have n109 : (XReg.xmm10 = XReg.xmm9) = False := by decide
  have ht9 : (t = XReg.xmm9) = False := propext ⟨h9, False.elim⟩
  have ht10 : (t = XReg.xmm10) = False := propext ⟨h10, False.elim⟩
  refine ⟨fun l hl => ?_, ⟨by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂, s₁],
    by simp [s₄, s₃, s₂, s₁], fun r hr l hl => ?_⟩⟩
  · simp only [s₄, s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, zlane_vpslldqZ _ _ _ _ _ hl,
      zlane_vpclmulZ _ _ _ _ _ _ hl, zlane_vpsrldqZ _ _ _ _ _ hl, ite_true, ht10, n910, n1011, n109,
      ite_false, ZBinOp.sse]
    rw [psrldq_15, pclmul_step _ _ (hK l hl), pslldq_1]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₄, s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, zlane_vpslldqZ _ _ _ _ _ hl,
      zlane_vpclmulZ _ _ _ _ _ _ hl, zlane_vpsrldqZ _ _ _ _ _ hl, hr.1, hr.2.1, hr.2.2]

/-- `0x87` into the low quadword of the four lanes of `zmm11`. -/
theorem constKZ_ok (s : State) : WP isa (.block constKZ) s fun s' =>
    (∀ l < 4, qword (s'.zlane .xmm11 l) 0 = 0x87) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .xmm11 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  apply WP.of_runBlock
  simp only [constKZ, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h => by simp [State.setReg, h], by simp [State.setReg],
    by simp [State.setReg], by simp [State.setReg], fun r hr l hl => ?_⟩
  · rw [zlane_vpbroadcastq _ _ _ _ hl]
    simp only [ite_true]
    simp [State.setV, State.setReg, qword]
  · rw [zlane_vpbroadcastq _ _ _ _ hl, State.zlane_setV128 _ _ _ _ _ hl]
    simp [hr, State.zlane, State.setReg, State.lane]

/-- Lane `l` of a 64-byte load into `d`. -/
theorem zlane_ld (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)).zlane d l =
      s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) hl]
  exact load512_lane _ _ hl

/-- Four blocks at `ld` into `b`, with the tweaks in `t` XORed in. -/
theorem pre1Z_ok (b t : XReg) (hbt : t ≠ b) (ld : MemOp) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea ld) 64) :
    WP isa (.block [.vmovdqu32Load b ld, .zop (.zbin .vpxord b b t)]) s fun s' =>
      (∀ l < 4, s'.zlane b l = s.mem.readW (s.ea ld + BitVec.ofNat 64 (16 * l)) 128 ^^^ s.zlane t l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let v := s.mem.readW (s.ea ld) 512
  let s₁ := s.setZ b (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128)
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, hin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨(ZOp.zbin .vpxord b b t).exec s₁, rfl, WP.block_nil ?_⟩
  have htb : (t = b) = False := propext ⟨hbt, False.elim⟩
  refine ⟨fun l hl => ?_, by simp [s₁], by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l hl => ?_⟩
  · rw [zlane_zbin _ _ _ _ _ _ hl]
    simp only [ite_true, ZBinOp.sse]
    rw [zlane_ld s b (s.ea ld) hl, State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [htb, ite_false]
    rfl
  · rw [zlane_zbin _ _ _ _ _ _ hl]
    simp only [hr, ite_false, s₁]
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp [hr]

/-- The tweaks in `t` XORed into `b` again, and its four blocks stored at
`r11 + d`. -/
theorem post1Z_ok (b t : XReg) (d : Nat) (s : State)
    (hd : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.zop (.zbin .vpxord b b t), .vmovdqu32Store (at_ .r11 d) b]) s fun s' =>
      (∀ l < 4, s'.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) 128 =
        s.zlane b l ^^^ s.zlane t l) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofInt 64 (d : Int), 64⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let s₁ := (ZOp.zbin .vpxord b b t).exec s
  let a := s.gpr .r11 + BitVec.ofInt 64 (d : Int)
  rw [WP.block_cons_iff]
  refine ⟨s₁, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ .r11 d) b) s₁ = some (s₁.setMem (s.mem.writeW a (s₁.zmm b))) := by
    simp only [isa, exec, State.store512_eq, ea_at, s₁, ZOp.exec_gpr, ZOp.exec_wr, ZOp.exec_mem, hd, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, ?_, by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l hl => ?_⟩
  · simp only [State.setMem_mem]
    have e := readW_writeW_inside s.mem a (s₁.zmm b) (k := 16 * l) (n := 16) (by omega) (by decide)
    rw [show 8 * (16 * l) = 128 * l by omega] at e
    rw [e, zmm_lane _ _ hl]
    simp only [s₁, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse]
    rfl
  · simp only [State.setMem_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp [s₁, zlane_zbin _ _ _ _ _ _ hl, hr]

open VG.Impl.AesXts.X86_64VaesZ (preZ postZ)

theorem addZ (B : Addr) (a b : Nat) : B + BitVec.ofNat 64 a + BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Block registers `regs[k]` from the blocks at `B + 64 (j + k)`, with the
tweaks `ts[k]` XORed in, for loads `ld d` at `B + d`. -/
theorem preZList_ok (ld : Nat → MemOp) (B : Addr) (regs ts : List XReg) (j : Nat) (s : State)
    (hnd : regs.Nodup) (hlen : ts.length = regs.length) (hdis : ∀ t ∈ ts, t ∉ regs)
    (hea : ∀ t : State, t.gpr = s.gpr → ∀ d, t.ea (ld d) = B + BitVec.ofNat 64 d)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (64 * (j + k))) 64) :
    WP isa (.block (preZ ld regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4, s'.zlane regs[k] l =
        s.mem.readW (B + BitVec.ofNat 64 (64 * (j + k) + 16 * l)) 128 ^^^ s.zlane (ts[k]'(by omega)) l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing ts j s with
  | nil =>
    cases ts with
    | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd hlen
    have htb : t ≠ b := fun h => hdis t List.mem_cons_self (h ▸ List.mem_cons_self)
    rw [preZ, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    rw [Nat.add_zero] at hd0
    refine WP.mono (pre1Z_ok b t htb (ld (64 * j)) s (by rw [hea s rfl]; exact hd0))
      fun s₁ ⟨lo₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
        (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
        (fun u hu => hea u (hu.trans g₁))
        (fun k hk => by rw [rd₁, wr₁, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, lo₁ l hl, hea s rfl, addZ]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hkt' : k < ts.length := by omega
        have hkt : ts[k] ≠ b := fun h =>
          hdis _ (List.mem_cons_of_mem _ (List.getElem_mem hkt')) (by rw [h]; exact List.mem_cons_self)
        rw [hb k hk' l hl, show j + 1 + k = j + (k + 1) by omega, o₁ _ hkt l hl]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2 l hl, o₁ r hr.1 l hl]

/-- The tweaks `ts[k]` XORed into block registers `regs[k]` again, stored to
the blocks at `r11 + 64 (j + k)`. -/
theorem postZList_ok (regs ts : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (hlen : ts.length = regs.length)
    (hdis : ∀ t ∈ ts, t ∉ regs)
    (hd : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int)) 64)
    (hw : (s.gpr .r11).toNat + 64 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (postZ regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (64 * (j + k) + 16 * l)) 128 =
          s.zlane regs[k] l ^^^ s.zlane (ts[k]'(by omega)) l) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (64 * j), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing ts j s with
  | nil =>
    cases ts with
    | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
    simp only [List.length_cons] at hd hw hlen
    rw [postZ, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    rw [Nat.add_zero] at hd0
    refine WP.mono (post1Z_ok b t (64 * j) s hd0) fun s₁ ⟨v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    rw [ofInt_natCast] at v₁ f₁
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have htb : ∀ t' ∈ t :: ts, t' ≠ b := fun t' ht' h => hdis t' ht' (h ▸ List.mem_cons_self)
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
      (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
      (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
      (by rw [h11]; omega)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11] at hb
    rw [h11] at hf
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (64 * (j + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .r11).isLt
      omega
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), ← addZ, v₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        have hkt' : k < ts.length := by omega
        have hkt : ts[k] ≠ b := htb _ (List.mem_cons_of_mem _ (List.getElem_mem hkt'))
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, x₁ _ hne l hl, x₁ _ hkt l hl]
    · simp only [List.length_cons]
      refine (f₁.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩) <;>
      · simp only [List.mem_singleton] at hr
        subst hr
        simp only [Region.Contains] at ha ⊢
        rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha
        rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)]
        have := (a - s.gpr .r11).isLt
        omega
    · simp only [List.mem_cons, not_or] at hr
      rw [xs r hr.2 l hl, x₁ r hr.1 l hl]

/-- Part of an access that is allowed. -/
theorem inRegions_off {X : List Region} {p : Addr} {n o k : Nat} (h : InRegions X p n) (hk : o + k ≤ n)
    (ho : o < 2 ^ 64) : InRegions X (p + BitVec.ofNat 64 o) k := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  have := Nat.mod_le ((p - r.base).toNat + o) (2 ^ 64)
  omega

open VG.Impl.AesXts.X86_64VaesZ (stepsZ ldTZ stTZ)
open VG.Impl.AesXts.X86_64Vaes (bufOff)

/-- The next group's tweaks: `zmm4 := zmm6 · α⁸`, `zmm5 := zmm7 · α⁸`, then
`zmm6 := zmm4 · α⁸`, `zmm7 := zmm5 · α⁸`. -/
theorem stepsZ_ok (s : State) (hK : ∀ l < 4, qword (s.zlane .xmm11 l) 0 = 0x87) :
    WP isa (.block stepsZ) s fun s' =>
      (∀ l < 4, s'.zlane .xmm4 l = stepW (s.zlane .xmm6 l)) ∧
      (∀ l < 4, s'.zlane .xmm5 l = stepW (s.zlane .xmm7 l)) ∧
      (∀ l < 4, s'.zlane .xmm6 l = stepW (stepW (s.zlane .xmm6 l))) ∧
      (∀ l < 4, s'.zlane .xmm7 l = stepW (stepW (s.zlane .xmm7 l))) ∧
      ZFrame [.xmm4, .xmm5, .xmm6, .xmm7, .xmm9, .xmm10] s s' := by
  have sub : ∀ d : XReg, d ∈ [.xmm4, .xmm5, .xmm6, .xmm7] → ∀ r, r ∈ [d, .xmm9, .xmm10] →
      r ∈ [.xmm4, .xmm5, .xmm6, .xmm7, .xmm9, .xmm10] := by decide
  have kK : ∀ {u u' : State} {d : XReg}, d ∈ [.xmm4, .xmm5, .xmm6, .xmm7] → ZFrame [d, .xmm9, .xmm10] u u' →
      (∀ l < 4, qword (u.zlane .xmm11 l) 0 = 0x87) → ∀ l < 4, qword (u'.zlane .xmm11 l) 0 = 0x87 :=
    fun hd hf hk l hl => by
      rw [hf.zlane _ (fun h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd h
        rcases hd with rfl | rfl | rfl | rfl <;> simp at h) l hl]
      exact hk l hl
  rw [stepsZ, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (stepZ_ok .xmm4 .xmm6 (by decide) (by decide) s hK) fun s₁ ⟨e₁, f₁⟩ => ?_
  refine WP.mono (stepZ_ok .xmm5 .xmm7 (by decide) (by decide) s₁ (kK (by decide) f₁ hK)) fun s₂ ⟨e₂, f₂⟩ => ?_
  refine WP.mono (stepZ_ok .xmm6 .xmm4 (by decide) (by decide) s₂ (kK (by decide) f₂ (kK (by decide) f₁ hK)))
    fun s₃ ⟨e₃, f₃⟩ => ?_
  refine WP.mono (stepZ_ok .xmm7 .xmm5 (by decide) (by decide) s₃
    (kK (by decide) f₃ (kK (by decide) f₂ (kK (by decide) f₁ hK)))) fun s₄ ⟨e₄, f₄⟩ => ?_
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ?_⟩
  · rw [f₄.zlane _ (by decide) l hl, f₃.zlane _ (by decide) l hl, f₂.zlane _ (by decide) l hl, e₁ l hl]
  · rw [f₄.zlane _ (by decide) l hl, f₃.zlane _ (by decide) l hl, e₂ l hl, f₁.zlane _ (by decide) l hl]
  · rw [f₄.zlane _ (by decide) l hl, e₃ l hl, f₂.zlane _ (by decide) l hl, e₁ l hl]
  · rw [e₄ l hl, f₃.zlane _ (by decide) l hl, e₂ l hl, f₁.zlane _ (by decide) l hl]
  · exact (f₁.mono (sub _ (by decide))).trans ((f₂.mono (sub _ (by decide))).trans
      ((f₃.mono (sub _ (by decide))).trans (f₄.mono (sub _ (by decide)))))

/-- Four 128-bit words at `ld` into `b`. -/
theorem ldZ_ok (b : XReg) (ld : MemOp) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.ea ld) 64) :
    WP isa (.block [.vmovdqu32Load b ld]) s fun s' =>
      (∀ l < 4, s'.zlane b l = s.mem.readW (s.ea ld + BitVec.ofNat 64 (16 * l)) 128) ∧ ZFrame [b] s s' := by
  let v := s.mem.readW (s.ea ld) 512
  rw [WP.block_cons_iff]
  refine ⟨s.setZ b (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128),
    by simp only [isa, exec, State.load512, hin, ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => zlane_ld s b (s.ea ld) hl, ⟨by simp, by simp, by simp, by simp, fun r hr l hl => ?_⟩⟩
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [List.mem_singleton] at hr
  simp [hr]

/-- The four lanes of `b` stored at `base + d`. -/
theorem st1Z_ok (base : Reg) (b : XReg) (d : Nat) (s : State)
    (hd : InRegions s.wr (s.gpr base + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Store (at_ base d) b]) s fun s' =>
      (∀ l < 4, s'.mem.readW (s.gpr base + BitVec.ofNat 64 (d + 16 * l)) 128 = s.zlane b l) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 d, 64⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := s.gpr base + BitVec.ofNat 64 d
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW a (s.zmm b)), by
    simp only [isa, exec, State.store512_eq, ea_at, ofInt_natCast, hd, ite_true, a], WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, ?_, by simp, by simp, by simp, fun r l hl => by simp⟩
  · simp only [State.setMem_mem]
    have e := readW_writeW_inside s.mem a (s.zmm b) (k := 16 * l) (n := 16) (by omega) (by decide)
    rw [show 8 * (16 * l) = 128 * l by omega] at e
    rw [← addZ, e, zmm_lane _ _ hl]
  · simp only [State.setMem_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The tweaks of the first eight blocks from the scratch buffer at `r8`,
and those of the next eight from them. -/
theorem ldTZ_ok (s : State) (hK : ∀ l < 4, qword (s.zlane .xmm11 l) 0 = 0x87)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 bufOff) 128) :
    WP isa (.block ldTZ) s fun s' =>
      (∀ l < 4, s'.zlane .xmm4 l = s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * l)) 128) ∧
      (∀ l < 4, s'.zlane .xmm5 l = s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 64 + 16 * l)) 128) ∧
      (∀ l < 4, s'.zlane .xmm6 l = stepW (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * l)) 128)) ∧
      (∀ l < 4, s'.zlane .xmm7 l = stepW (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 64 + 16 * l)) 128)) ∧
      ZFrame [.xmm4, .xmm5, .xmm6, .xmm7, .xmm9, .xmm10] s s' := by
  have e4 : s.ea (at_ .r8 bufOff) = s.gpr .r8 + BitVec.ofNat 64 bufOff := by rw [ea_at, ofInt_natCast]
  have i4 : InRegions (s.rd ++ s.wr) (s.ea (at_ .r8 bufOff)) 64 := by
    rw [e4]; simpa using inRegions_off hin (o := 0) (k := 64) (by decide) (by decide)
  rw [show ldTZ = [.vmovdqu32Load .xmm4 (at_ .r8 bufOff)] ++ [.vmovdqu32Load .xmm5 (at_ .r8 (bufOff + 64))] ++
      stepZ .xmm6 .xmm4 ++ stepZ .xmm7 .xmm5 from rfl, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (ldZ_ok .xmm4 _ s i4) fun s₁ ⟨v₁, f₁⟩ => ?_
  have e5 : s₁.ea (at_ .r8 (bufOff + 64)) = s.gpr .r8 + BitVec.ofNat 64 (bufOff + 64) := by
    rw [ea_at, ofInt_natCast, f₁.gpr]
  have i5 : InRegions (s₁.rd ++ s₁.wr) (s₁.ea (at_ .r8 (bufOff + 64))) 64 := by
    rw [e5, f₁.rd, f₁.wr, ← addZ]; exact inRegions_off hin (o := 64) (k := 64) (by decide) (by decide)
  refine WP.mono (ldZ_ok .xmm5 _ s₁ i5) fun s₂ ⟨v₂, f₂⟩ => ?_
  have k₂ : ∀ l < 4, qword (s₂.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [f₂.zlane _ (by decide) l hl, f₁.zlane _ (by decide) l hl]; exact hK l hl
  refine WP.mono (stepZ_ok .xmm6 .xmm4 (by decide) (by decide) s₂ k₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  have k₃ : ∀ l < 4, qword (s₃.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [f₃.zlane _ (by decide) l hl]; exact k₂ l hl
  refine WP.mono (stepZ_ok .xmm7 .xmm5 (by decide) (by decide) s₃ k₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m₁ : s₁.mem = s.mem := f₁.mem
  have l4 : ∀ l < 4, s₂.zlane .xmm4 l = s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * l)) 128 :=
    fun l hl => by rw [f₂.zlane _ (by decide) l hl, v₁ l hl, e4, addZ]
  have l5 : ∀ l < 4, s₂.zlane .xmm5 l = s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 64 + 16 * l)) 128 :=
    fun l hl => by rw [v₂ l hl, e5, addZ, m₁]
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ?_⟩
  · rw [f₄.zlane _ (by decide) l hl, f₃.zlane _ (by decide) l hl, l4 l hl]
  · rw [f₄.zlane _ (by decide) l hl, f₃.zlane _ (by decide) l hl, l5 l hl]
  · rw [f₄.zlane _ (by decide) l hl, v₃ l hl, l4 l hl]
  · rw [v₄ l hl, f₃.zlane _ (by decide) l hl, l5 l hl]
  · exact (f₁.mono (by decide)).trans ((f₂.mono (by decide)).trans ((f₃.mono (by decide)).trans
      (f₄.mono (by decide))))

/-- The tweaks in `zmm4` and `zmm5` back to the scratch buffer at `r8`. -/
theorem stTZ_ok (s : State) (hin : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 bufOff) 128) :
    WP isa (.block stTZ) s fun s' =>
      (∀ l < 4, s'.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * l)) 128 = s.zlane .xmm4 l) ∧
      (∀ l < 4, s'.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 64 + 16 * l)) 128 = s.zlane .xmm5 l) ∧
      Frame [⟨s.gpr .r8 + BitVec.ofNat 64 bufOff, 128⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hb : bufOff + 128 ≤ 2 ^ 64 := by decide
  rw [show stTZ = [.vmovdqu32Store (at_ .r8 bufOff) .xmm4] ++ [.vmovdqu32Store (at_ .r8 (bufOff + 64)) .xmm5]
    from rfl, WP.block_append_iff]
  have i4 : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 bufOff) 64 := by
    simpa using inRegions_off hin (o := 0) (k := 64) (by decide) (by decide)
  refine WP.mono (st1Z_ok .r8 .xmm4 bufOff s i4) fun s₁ ⟨v₁, f₁, g₁, rd₁, wr₁, z₁⟩ => ?_
  refine WP.mono (st1Z_ok .r8 .xmm5 (bufOff + 64) s₁ (by
      rw [wr₁, g₁, ← addZ]; exact inRegions_off hin (o := 64) (k := 64) (by decide) (by decide)))
    fun s₂ ⟨v₂, f₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  rw [g₁] at v₂ f₂
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁,
    fun r l hl => by rw [z₂ r l hl, z₁ r l hl]⟩
  · rw [f₂.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * l), 16⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))
      (by decide), v₁ l hl]
  · rw [v₂ l hl, z₁ _ l hl]
  · refine (f₁.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩) <;>
    · simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by simp only [bufOff]; omega)] at ha
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by simp only [bufOff]; omega)]
      have := (a - s.gpr .r8).isLt
      simp only [bufOff] at ha ⊢
      omega

end VG.Proof.AesXts.X86_64.VaesZ

/-! ## XTS-AES with AVX-512 VAES on x86-64, in place: sixteen blocks at a time

`TwZ s₀ c`: the tweak registers `zmm4`–`zmm7` hold the tweaks of blocks
`c … c + 15` (lane `l` of `zmm4 + k`, block `c + 4 k + l`), and `zmm11` the
constant `0x87` in its four lanes. `group16_wp`: one run of `group16 ldIn f`
takes `Vaes.GInv b c ∧ TwZ c` to `c + 16`, for rounds `f` computing the
cipher (or its inverse) on the four lanes of `zmm0`–`zmm3` (`Blk16`).
`loop16_wp`: from `GInv b b`, the tweaks loaded from the scratch buffer, the
loop while sixteen blocks are left, and the tweaks of the next eight stored
back reach `GInv c c` with fewer than sixteen left; `loops_ok`: with the
eight-block loop after it, `Vaes.LoopOk`.
-/

namespace VG.Proof.AesXts.X86_64.VaesZ

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff)
open VG.Impl.AesXts.X86_64VaesZ (regsZ twsZ group16 loop16 loops ldIn constKZ ldTZ stTZ)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast ea_at)
open VG.Proof.AesXts.X86_64.Vaes (slot bufR Stable GInv outBlk stF xts_word bytesAt_b16 next_add stepW
  group_data_n slot_scr buf_scr Blk8 LoopOk)

/-- `f` computes the cipher (or its inverse) on the four lanes of `zmm0`–`zmm3`. -/
def Blk16 (enc : Bool) (f : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f regsZ) s fun s' =>
    (∀ b ∈ regsZ, ∀ l < 4, st (s'.zlane b l) = stF enc (R s₀) (wK s₀) (st (s.zlane b l))) ∧
      ZFrame (.xmm8 :: regsZ) s s'

/-- The tweaks of blocks `c … c + 15` in `zmm4`–`zmm7`, and `0x87` in the
four lanes of `zmm11`. -/
structure TwZ (s₀ : State) (c : Nat) (s : State) : Prop where
  tw : ∀ k (h : k < twsZ.length), ∀ l < 4, b16 (s.zlane twsZ[k] l) = Spec.Xts.next (iv0 s₀) (c + (4 * k + l))
  k87 : ∀ l < 4, qword (s.zlane .xmm11 l) 0 = 0x87

theorem twsZ_regsZ : ∀ t ∈ twsZ, t ∉ regsZ := by decide

theorem b16_stepW (t : List Byte) (v : BitVec 128) (n : Nat) (h : b16 v = Spec.Xts.next t n) :
    b16 (stepW v) = Spec.Xts.next t (n + 8) := by
  rw [stepW, ← next_b8, h, ← next_add]

/-- One group of sixteen blocks. -/
theorem group16_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f KP s₀) {b c : Nat} (hc : c + 16 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ b c s) (ht : TwZ s₀ c s) :
    WP isa (group16 ldIn f) s fun s' =>
      (GInv enc KP s₀ b (c + 16) s' ∧ TwZ s₀ (c + 16) s') ∧ s'.cf = some (decide (N s₀ - (c + 16) < 16)) := by
  have hw := hp.data_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have inD : ∀ k < 4, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((64 * (0 + k) : Nat) : Int)) 64 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  -- The blocks, with the tweaks XORed in.
  refine WP.seq (WP.mono (preZList_ok ldIn (s.gpr .r11) regsZ twsZ 0 s (by decide) rfl twsZ_regsZ
    (fun u hu d => by rw [ldIn, ea_at, ofInt_natCast, hu])
    (fun k hk => inRegions_wr (by rw [← ofInt_natCast]; exact inD k hk)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ h.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have o₂ : ∀ r, r ∉ regsZ → r ≠ .xmm8 → ∀ l < 4, s₂.zlane r l = s.zlane r l := fun r hr h8 l hl => by
    rw [f₂.zlane r (by simp [h8, hr]) l hl, x₁ r hr l hl]
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postZList_ok regsZ twsZ 0 s₂ (by decide) rfl twsZ_regsZ
    (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (by rw [g₂, h.r11, hp.blk_toNat (by omega)]; show _ + 64 * (0 + 4) ≤ _; omega))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 64 * regsZ.length = 16 * 16 from rfl] at f₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have o₃ : ∀ r, r ∉ regsZ → r ≠ .xmm8 → ∀ l < 4, s₃.zlane r l = s.zlane r l := fun r hr h8 l hl => by
    rw [x₃ r hr l hl, o₂ r hr h8 l hl]
  have hK₃ : ∀ l < 4, qword (s₃.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [o₃ _ (by decide) (by decide) l hl]; exact ht.k87 l hl
  -- The next group's tweaks.
  rw [WP.block_append_iff]
  refine WP.mono (stepsZ_ok s₃ hK₃) fun s₄ ⟨t4, t5, t6, t7, f₄⟩ => ?_
  have g₄' : s₄.gpr = s.gpr := f₄.gpr.trans g₃'
  have m₄ : s₄.mem = s₃.mem := f₄.mem
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [f₄.gpr]) (by rw [f₄.gpr]) (by rw [f₄.gpr]) (by rw [f₄.gpr]) f₄.rd f₄.wr
    (by rw [m₄]; exact Frame.refl _ _)
  have hK₄ : ∀ l < 4, qword (s₄.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [f₄.zlane _ (by decide) l hl]; exact hK₃ l hl
  -- The tweaks of the group, as they were.
  have T : ∀ k (hk : k < 4), ∀ l < 4, s₃.zlane (twsZ[k]'hk) l = s.zlane (twsZ[k]'hk) l := fun k hk l hl =>
    o₃ _ (twsZ_regsZ _ (List.getElem_mem hk)) (by
      have : twsZ[k] ∈ twsZ := List.getElem_mem hk
      intro h8; rw [h8] at this; exact absurd this (by decide)) l hl
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    rw [m₄]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 16 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [m₄]
    by_cases hin : c ≤ k ∧ k < c + 16
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < 16 := by omega
      have hkk : i / 4 < regsZ.length := by have : regsZ.length = 4 := rfl; omega
      have hkt : i / 4 < twsZ.length := by have : twsZ.length = 4 := rfl; omega
      have hl : i % 4 < 4 := Nat.mod_lt _ (by decide)
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (64 * (0 + i / 4) + 16 * (i % 4)) := by
        rw [h.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← ab]
      have hT : s₂.zlane twsZ[i / 4] (i % 4) = s.zlane twsZ[i / 4] (i % 4) :=
        o₂ _ (twsZ_regsZ _ (List.getElem_mem hkt)) (by
          have : twsZ[i / 4] ∈ twsZ := List.getElem_mem hkt
          intro h8; rw [h8] at this; exact absurd this (by decide)) _ hl
      have e1 := e₁ _ hkk _ hl
      rw [← ab] at e1
      have hc' : st (s₂.zlane regsZ[i / 4] (i % 4)) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.zlane twsZ[i / 4] (i % 4))) :=
        (e₂ _ (List.getElem_mem hkk) _ hl).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      rw [hT]
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ht.tw _ hkt _ hl, h.data _ hk, show c + (4 * (i / 4) + i % 4) = c + i by omega]
      simp only [show ¬ c + i < c by omega, ite_false, show c + i < c + 16 by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 16 by omega]
      · simp only [hlt, ite_false, show ¬ k < c + 16 by omega]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := by
    intro j hj
    rw [m₄, AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega))).symm) (by decide),
      h.buf j hj]
  have htw : ∀ k (hk : k < twsZ.length), ∀ l < 4,
      b16 (s₄.zlane twsZ[k] l) = Spec.Xts.next (iv0 s₀) (c + 16 + (4 * k + l)) := by
    intro k hk l hl
    have T6 : s₃.zlane .xmm6 l = s.zlane .xmm6 l := T 2 (by decide) l hl
    have T7 : s₃.zlane .xmm7 l = s.zlane .xmm7 l := T 3 (by decide) l hl
    have w6 : b16 (s.zlane .xmm6 l) = Spec.Xts.next (iv0 s₀) (c + (8 + l)) := ht.tw 2 (by decide) l hl
    have w7 : b16 (s.zlane .xmm7 l) = Spec.Xts.next (iv0 s₀) (c + (12 + l)) := ht.tw 3 (by decide) l hl
    rcases (by have : twsZ.length = 4 := rfl; omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show b16 (s₄.zlane .xmm4 l) = _
      rw [t4 l hl, T6, b16_stepW _ _ _ w6]; congr 1; omega
    · show b16 (s₄.zlane .xmm5 l) = _
      rw [t5 l hl, T7, b16_stepW _ _ _ w7]; congr 1; omega
    · show b16 (s₄.zlane .xmm6 l) = _
      rw [t6 l hl, T6, b16_stepW _ _ _ (b16_stepW _ _ _ w6)]; congr 1; omega
    · show b16 (s₄.zlane .xmm7 l) = _
      rw [t7 l hl, T7, b16_stepW _ _ _ (b16_stepW _ _ _ w7)]; congr 1; omega
  have hrd : s₄.rd = s₀.rd := by rw [f₄.rd, rd₃, rd₂, h.rd]
  have hwr : s₄.wr = s₀.wr := by rw [f₄.wr, wr₃, wr₂, h.wr]
  -- `add r11, 256`, `sub r9, 16` and `cmp r9, 16`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 16 = BitVec.ofNat 64 (N s₀ - (c + 16)) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + 256 = blk s₀ (c + 16) := by
    rw [blk, blk, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 256 = 16 * (c + 16) by omega]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, ⟨htw, hK₄⟩⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 16) < 2 ^ 64 by omega),
    show (16 : BitVec 64).toNat = 16 from rfl]

/-- `cmp r9, k`. -/
theorem cmpR9_ok {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {c : Nat} {s : State}
    (h : GInv enc KP s₀ c c s) (k : BitVec 32) (n : Nat) (hk : k.signExtend 64 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r9 (.imm k)]) s fun s' =>
      GInv enc KP s₀ c c s' ∧ s'.cf = some (decide (N s₀ - c < n)) := by
  have hr9 := h.r9
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hk, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.congr hst (fun _ _ _ => rfl) rfl rfl rfl, ?_⟩
  simp only [arithFlags, State.setFlags, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hn]

/-- The sixteen-block loop, from block `b`, while sixteen blocks are left. -/
theorem loop16_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f KP s₀) {b : Nat} {s : State} (h : GInv enc KP s₀ b b s)
    (hcf : s.cf = some (decide (N s₀ - b < 16))) :
    WP isa (loop16 ldIn f) s fun s' => ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ c c s' := by
  have hsw := hp.scr_wrap
  refine WP.ite (decide (N s₀ - b < 16)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨b, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (constKZ_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
    have h₁ : GInv enc KP s₀ b b s₁ := h.congr hst (fun r h1 _ => g₁ r h1) m₁ rd₁ wr₁
    have hW : s₁.rd ++ s₁.wr = s₀.rd ++ [ivR s₀, dataR s₀, scrR s₀] := by rw [h₁.rd, h₁.wr, hp.wr]
    refine WP.mono (ldTZ_ok s₁ k₁ ⟨scrR s₀, by rw [hW]; simp, by
        rw [h₁.r8]; exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
      fun s₂ ⟨l4, l5, l6, l7, f₂⟩ => ?_
    have h₂ : GInv enc KP s₀ b b s₂ := h₁.congr hst (fun r _ _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr
    have sl : ∀ j < 8, s₁.mem.readW (s₁.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * j)) 128 = s₁.mem.readW (slot s₀ j) 128 :=
      fun j _ => by rw [h₁.r8]
    have bj : ∀ j < 8, b16 (s₁.mem.readW (slot s₀ j) 128) = Spec.Xts.next (iv0 s₀) (b + j) := fun j hj => by
      rw [← bytesAt_b16]; exact h₁.buf j hj
    have t₂ : TwZ s₀ b s₂ := by
      refine ⟨fun k hk l hl => ?_, fun l hl => by rw [f₂.zlane _ (by decide) l hl]; exact k₁ l hl⟩
      rcases (by have : twsZ.length = 4 := rfl; omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · show b16 (s₂.zlane .xmm4 l) = _
        rw [l4 l hl, sl l (by omega), bj l (by omega)]; congr 1; omega
      · show b16 (s₂.zlane .xmm5 l) = _
        rw [l5 l hl, show bufOff + 64 + 16 * l = bufOff + 16 * (4 + l) by omega, sl _ (by omega), bj _ (by omega)]
      · show b16 (s₂.zlane .xmm6 l) = _
        rw [l6 l hl, sl l (by omega), b16_stepW _ _ _ (bj l (by omega))]; congr 1; omega
      · show b16 (s₂.zlane .xmm7 l) = _
        rw [l7 l hl, show bufOff + 64 + 16 * l = bufOff + 16 * (4 + l) by omega, sl _ (by omega),
          b16_stepW _ _ _ (bj _ (by omega))]
        congr 1; omega
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 16 ≤ N s₀ ∧ GInv enc KP s₀ b c t ∧ TwZ s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group16 ldIn f) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ b c t' ∧ TwZ s₀ c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hT⟩
      refine WP.mono (group16_wp hp hst hf hc hI hT) fun t' ⟨⟨hI', hT'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 16) < 16
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 16, hlt, hI', hT'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 16), by omega, c + 16, rfl, by omega, hI', hT'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀ - b) s₂ ⟨b, rfl, by omega, h₂, t₂⟩)
      fun s₃ ⟨c, hc, h₃, t₃⟩ => ?_)
    -- The tweaks of the next eight blocks back to the buffer.
    have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h₃.wr, hp.wr]
    refine WP.mono (stTZ_ok s₃ ⟨scrR s₀, by rw [hW₃]; simp, by
        rw [h₃.r8]; exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
      fun s₄ ⟨w4, w5, f, g, rd, wr, _⟩ => ?_
    rw [h₃.r8] at w4 w5 f
    have fb : Frame [bufR s₀] s₃.mem s₄.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, Region.sub_prefix (by decide)⟩
    have fs : Frame [scrR s₀] s₃.mem s₄.mem := fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, buf_scr⟩
    refine ⟨c, hc, hst s₃ s₄ h₃.kp (by rw [g]) (by rw [g]) (by rw [g]) (by rw [g]) rd wr (fb.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, fun _ h => h⟩),
      h₃.le, by rw [g, h₃.r8], by rw [g, h₃.r9], by rw [g, h₃.r11], by rw [g, h₃.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g, h₃.keep r h1 h2 h3 h4 h5 h6 h7], by rw [rd, h₃.rd], by rw [wr, h₃.wr],
      h₃.frame.trans (fs.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩),
      fun k hk => by
        rw [AesCbc.X86_64.bytesAt_frame fb (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right buf_scr) (by decide), h₃.data k hk],
      fun j hj => ?_, by rw [g, h₃.rdx]⟩
    rw [bytesAt_b16]
    by_cases hj4 : j < 4
    · rw [show slot s₀ j = S s₀ + BitVec.ofNat 64 (bufOff + 16 * j) from rfl, w4 j hj4]
      have := t₃.tw 0 (by decide) j hj4
      rw [show c + (4 * 0 + j) = c + j by omega] at this
      exact this
    · rw [show slot s₀ j = S s₀ + BitVec.ofNat 64 (bufOff + 64 + 16 * (j - 4)) by
          rw [slot]; congr 2; omega, w5 (j - 4) (by omega)]
      have := t₃.tw 1 (by decide) (j - 4) (by omega)
      rw [show c + (4 * 1 + (j - 4)) = c + j by omega] at this
      exact this

/-- The sixteen-block loop, then the eight-block loop: `Vaes.LoopOk`. -/
theorem loops_ok {enc : Bool} {KP : State → Prop} {f16 f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf16 : Blk16 enc f16 KP s₀) (hf8 : Blk8 enc f8 KP s₀) :
    LoopOk enc (loops ldIn f16 (Impl.AesXts.X86_64Vaes.loop8 f8)) KP s₀ := by
  intro s h _
  refine WP.seq (WP.mono (cmpR9_ok hst h 16 16 (by decide) (by decide)) fun s₁ ⟨h₁, cf₁⟩ => ?_)
  refine WP.seq (WP.mono (loop16_wp hp hst hf16 h₁ (by rw [cf₁, Nat.sub_zero])) fun s₂ ⟨c, _, h₂⟩ => ?_)
  rw [show ([.vop .vzeroupper, .alu .cmp .r9 (.imm 8)] : List Instr) = [.vop .vzeroupper] ++
    [.alu .cmp .r9 (.imm 8)] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have v : WP isa (.block [.vop .vzeroupper]) s₂ (GInv enc KP s₀ c c) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact h₂.congr hst (fun _ _ _ => rfl) rfl rfl rfl
  refine WP.mono v fun s₃ h₃ => WP.mono (cmpR9_ok hst h₃ 8 8 (by decide) (by decide)) fun s₄ ⟨h₄, cf₄⟩ => ?_
  exact Vaes.groups_wp hp hst hf8 h₄ cf₄

open VG.Proof.AesCbc.X86_64 (modeX86_64)
open VG.Proof.AesXts.X86_64.Vaes (crypt_wp KPe KPd kpe_stable kpd_stable kpe_pre imc_pre rsi_ofNat)
open VG.Impl.AesXts.X86_64Vaes (regs4)

theorem encrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode true)).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesZ.encrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loops_ok hp₁ (kpe_stable hp₁) ?_ ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, kpe_pre hp₁ h⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    refine WP.mono (Aes.X86_64.VaesZ.aesZ_ok .xmm8 regsZ (by decide) (by decide) hp₁.rounds (fun _ => []) []
      (fun _ h => absurd h List.not_mem_nil) (fun _ _ => True)
      (fun _ _ _ s _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial) s hK trivial
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, _, f⟩ => ⟨fun b hb l hl => e b hb l hl, by simpa using f⟩
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.Vaes.aes_ok regs4 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem decrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode false)).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesZ.decrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loops_ok hp₁ (kpd_stable hp₁) ?_ ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => imc_pre hp₁ h)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesZ.aesDecZ_ok .xmm8 regsZ (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesBlocks.aesDec_ok regs4 (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

end VG.Proof.AesXts.X86_64.VaesZ

/-! ## XTS-AES with AVX-512 VAES on x86-64, out of place: sixteen blocks at a time

`group16To_wp`, `loop16To_wp` and `loopsTo_ok`: `group16_wp`, `loop16_wp`
and `loops_ok` of `VaesZ/Loop.lean` for the out-of-place functions, whose
blocks are loaded from `src` (`[r11 + rcx]`, `VaesTo.ix`), with the
invariant of `VaesTo/Crypt.lean`; with `VaesTo.crypt_wp`, `encryptTo_wp` and
`decryptTo_wp`.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Impl.AesXts.X86_64Vaes (bufOff regs4)
open VG.Impl.AesXts.X86_64VaesZ (regsZ twsZ group16 loop16 loops constKZ ldTZ stTZ)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast ea_at)
open VG.Proof.AesXts.X86_64.Vaes (slot bufR stF xts_word bytesAt_b16 next_add stepW Blk8 KPe KPd rsi_ofNat)
open VG.Proof.AesXts.X86_64.VaesZ (Blk16 TwZ twsZ_regsZ b16_stepW preZList_ok postZList_ok stepsZ_ok
  constKZ_ok ldTZ_ok stTZ_ok)

/-- One group of sixteen blocks. -/
theorem group16To_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f KP s₀) {b c : Nat} (hc : c + 16 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ b c s) (ht : TwZ s₀ c s) :
    WP isa (group16 Impl.AesXts.X86_64VaesTo.ix f) s fun s' =>
      (GInv enc KP s₀ b (c + 16) s' ∧ TwZ s₀ (c + 16) s') ∧ s'.cf = some (decide (N s₀ - (c + 16) < 16)) := by
  have hw := hp.data_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have inD : ∀ k < 4, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((64 * (0 + k) : Nat) : Int)) 64 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  -- The blocks, with the tweaks XORed in.
  have hnl := hp.n_lt
  refine WP.seq (WP.mono (preZList_ok Impl.AesXts.X86_64VaesTo.ix (s.gpr .r11 + s.gpr .rcx) regsZ twsZ 0 s
    (by decide) rfl twsZ_regsZ (fun u hu d => by rw [ea_ix, ofInt_natCast, hu])
    (fun k hk => by
      have : regsZ.length = 4 := rfl
      rw [← ofInt_natCast]; exact hp.ix_in h.r11 h.rcx h.rd (by omega) (by omega)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ h.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have o₂ : ∀ r, r ∉ regsZ → r ≠ .xmm8 → ∀ l < 4, s₂.zlane r l = s.zlane r l := fun r hr h8 l hl => by
    rw [f₂.zlane r (by simp [h8, hr]) l hl, x₁ r hr l hl]
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postZList_ok regsZ twsZ 0 s₂ (by decide) rfl twsZ_regsZ
    (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (by rw [g₂, h.r11, hp.blk_toNat (by omega)]; show _ + 64 * (0 + 4) ≤ _; omega))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 64 * regsZ.length = 16 * 16 from rfl] at f₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have o₃ : ∀ r, r ∉ regsZ → r ≠ .xmm8 → ∀ l < 4, s₃.zlane r l = s.zlane r l := fun r hr h8 l hl => by
    rw [x₃ r hr l hl, o₂ r hr h8 l hl]
  have hK₃ : ∀ l < 4, qword (s₃.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [o₃ _ (by decide) (by decide) l hl]; exact ht.k87 l hl
  -- The next group's tweaks.
  rw [WP.block_append_iff]
  refine WP.mono (stepsZ_ok s₃ hK₃) fun s₄ ⟨t4, t5, t6, t7, f₄⟩ => ?_
  have g₄' : s₄.gpr = s.gpr := f₄.gpr.trans g₃'
  have m₄ : s₄.mem = s₃.mem := f₄.mem
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [f₄.gpr]) (by rw [f₄.gpr]) (by rw [f₄.gpr]) (by rw [f₄.gpr]) f₄.rd f₄.wr
    (by rw [m₄]; exact Frame.refl _ _)
  have hK₄ : ∀ l < 4, qword (s₄.zlane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [f₄.zlane _ (by decide) l hl]; exact hK₃ l hl
  -- The tweaks of the group, as they were.
  have T : ∀ k (hk : k < 4), ∀ l < 4, s₃.zlane (twsZ[k]'hk) l = s.zlane (twsZ[k]'hk) l := fun k hk l hl =>
    o₃ _ (twsZ_regsZ _ (List.getElem_mem hk)) (by
      have : twsZ[k] ∈ twsZ := List.getElem_mem hk
      intro h8; rw [h8] at this; exact absurd this (by decide)) l hl
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    rw [m₄]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 16 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [m₄]
    by_cases hin : c ≤ k ∧ k < c + 16
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < 16 := by omega
      have hkk : i / 4 < regsZ.length := by have : regsZ.length = 4 := rfl; omega
      have hkt : i / 4 < twsZ.length := by have : twsZ.length = 4 := rfl; omega
      have hl : i % 4 < 4 := Nat.mod_lt _ (by decide)
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (64 * (0 + i / 4) + 16 * (i % 4)) := by
        rw [h.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← ab]
      have hT : s₂.zlane twsZ[i / 4] (i % 4) = s.zlane twsZ[i / 4] (i % 4) :=
        o₂ _ (twsZ_regsZ _ (List.getElem_mem hkt)) (by
          have : twsZ[i / 4] ∈ twsZ := List.getElem_mem hkt
          intro h8; rw [h8] at this; exact absurd this (by decide)) _ hl
      have e1 := e₁ _ hkk _ hl
      rw [ix_sblk h.r11 h.rcx _ i (by omega), hp.src_kept h.frame (by omega)] at e1
      have hc' : st (s₂.zlane regsZ[i / 4] (i % 4)) = stF enc (R s₀) (wK s₀)
          (st (s₀.mem.readW (sblk s₀ (c + i)) 128 ^^^ s.zlane twsZ[i / 4] (i % 4))) :=
        (e₂ _ (List.getElem_mem hkk) _ hl).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      rw [hT]
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ht.tw _ hkt _ hl, show c + (4 * (i / 4) + i % 4) = c + i by omega]
      simp only [show c + i < c + 16 by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 16 by omega]
      · simp only [hlt, ite_false, show ¬ k < c + 16 by omega]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := by
    intro j hj
    rw [m₄, AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega))).symm) (by decide),
      h.buf j hj]
  have htw : ∀ k (hk : k < twsZ.length), ∀ l < 4,
      b16 (s₄.zlane twsZ[k] l) = Spec.Xts.next (iv0 s₀) (c + 16 + (4 * k + l)) := by
    intro k hk l hl
    have T6 : s₃.zlane .xmm6 l = s.zlane .xmm6 l := T 2 (by decide) l hl
    have T7 : s₃.zlane .xmm7 l = s.zlane .xmm7 l := T 3 (by decide) l hl
    have w6 : b16 (s.zlane .xmm6 l) = Spec.Xts.next (iv0 s₀) (c + (8 + l)) := ht.tw 2 (by decide) l hl
    have w7 : b16 (s.zlane .xmm7 l) = Spec.Xts.next (iv0 s₀) (c + (12 + l)) := ht.tw 3 (by decide) l hl
    rcases (by have : twsZ.length = 4 := rfl; omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show b16 (s₄.zlane .xmm4 l) = _
      rw [t4 l hl, T6, b16_stepW _ _ _ w6]; congr 1; omega
    · show b16 (s₄.zlane .xmm5 l) = _
      rw [t5 l hl, T7, b16_stepW _ _ _ w7]; congr 1; omega
    · show b16 (s₄.zlane .xmm6 l) = _
      rw [t6 l hl, T6, b16_stepW _ _ _ (b16_stepW _ _ _ w6)]; congr 1; omega
    · show b16 (s₄.zlane .xmm7 l) = _
      rw [t7 l hl, T7, b16_stepW _ _ _ (b16_stepW _ _ _ w7)]; congr 1; omega
  have hrd : s₄.rd = s₀.rd := by rw [f₄.rd, rd₃, rd₂, h.rd]
  have hwr : s₄.wr = s₀.wr := by rw [f₄.wr, wr₃, wr₂, h.wr]
  -- `add r11, 256`, `sub r9, 16` and `cmp r9, 16`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 16 = BitVec.ofNat 64 (N s₀ - (c + 16)) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + 256 = blk s₀ (c + 16) := by
    rw [blk, blk, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 256 = 16 * (c + 16) by omega]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10], by simp [g₄', h.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, ⟨htw, hK₄⟩⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 16) < 2 ^ 64 by omega),
    show (16 : BitVec 64).toNat = 16 from rfl]

/-- `cmp r9, k`. -/
theorem cmpR9To_ok {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {c : Nat} {s : State}
    (h : GInv enc KP s₀ c c s) (k : BitVec 32) (n : Nat) (hk : k.signExtend 64 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r9 (.imm k)]) s fun s' =>
      GInv enc KP s₀ c c s' ∧ s'.cf = some (decide (N s₀ - c < n)) := by
  have hr9 := h.r9
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, hk, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.congr hst (fun _ _ => rfl) rfl rfl rfl, ?_⟩
  simp only [arithFlags, State.setFlags, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hn]

/-- The sixteen-block loop, from block `b`, while sixteen blocks are left. -/
theorem loop16To_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f KP s₀) {b : Nat} {s : State} (h : GInv enc KP s₀ b b s)
    (hcf : s.cf = some (decide (N s₀ - b < 16))) :
    WP isa (loop16 Impl.AesXts.X86_64VaesTo.ix f) s fun s' => ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ c c s' := by
  have hsw := hp.scr_wrap
  refine WP.ite (decide (N s₀ - b < 16)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨b, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (constKZ_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
    have h₁ : GInv enc KP s₀ b b s₁ := h.congr hst (fun r h1 => g₁ r h1) m₁ rd₁ wr₁
    have hW : s₁.rd ++ s₁.wr = s₀.rd ++ [ivR s₀, dataR s₀, scrR s₀] := by rw [h₁.rd, h₁.wr, hp.wr]
    refine WP.mono (ldTZ_ok s₁ k₁ ⟨scrR s₀, by rw [hW]; simp, by
        rw [h₁.r8]; exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
      fun s₂ ⟨l4, l5, l6, l7, f₂⟩ => ?_
    have h₂ : GInv enc KP s₀ b b s₂ := h₁.congr hst (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr
    have sl : ∀ j < 8, s₁.mem.readW (s₁.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * j)) 128 = s₁.mem.readW (slot s₀ j) 128 :=
      fun j _ => by rw [h₁.r8]
    have bj : ∀ j < 8, b16 (s₁.mem.readW (slot s₀ j) 128) = Spec.Xts.next (iv0 s₀) (b + j) := fun j hj => by
      rw [← bytesAt_b16]; exact h₁.buf j hj
    have t₂ : TwZ s₀ b s₂ := by
      refine ⟨fun k hk l hl => ?_, fun l hl => by rw [f₂.zlane _ (by decide) l hl]; exact k₁ l hl⟩
      rcases (by have : twsZ.length = 4 := rfl; omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      · show b16 (s₂.zlane .xmm4 l) = _
        rw [l4 l hl, sl l (by omega), bj l (by omega)]; congr 1; omega
      · show b16 (s₂.zlane .xmm5 l) = _
        rw [l5 l hl, show bufOff + 64 + 16 * l = bufOff + 16 * (4 + l) by omega, sl _ (by omega), bj _ (by omega)]
      · show b16 (s₂.zlane .xmm6 l) = _
        rw [l6 l hl, sl l (by omega), b16_stepW _ _ _ (bj l (by omega))]; congr 1; omega
      · show b16 (s₂.zlane .xmm7 l) = _
        rw [l7 l hl, show bufOff + 64 + 16 * l = bufOff + 16 * (4 + l) by omega, sl _ (by omega),
          b16_stepW _ _ _ (bj _ (by omega))]
        congr 1; omega
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 16 ≤ N s₀ ∧ GInv enc KP s₀ b c t ∧ TwZ s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group16 Impl.AesXts.X86_64VaesTo.ix f) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ b c t' ∧ TwZ s₀ c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hT⟩
      refine WP.mono (group16To_wp hp hst hf hc hI hT) fun t' ⟨⟨hI', hT'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 16) < 16
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 16, hlt, hI', hT'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 16), by omega, c + 16, rfl, by omega, hI', hT'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀ - b) s₂ ⟨b, rfl, by omega, h₂, t₂⟩)
      fun s₃ ⟨c, hc, h₃, t₃⟩ => ?_)
    -- The tweaks of the next eight blocks back to the buffer.
    have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h₃.wr, hp.wr]
    refine WP.mono (stTZ_ok s₃ ⟨scrR s₀, by rw [hW₃]; simp, by
        rw [h₃.r8]; exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
      fun s₄ ⟨w4, w5, f, g, rd, wr, _⟩ => ?_
    rw [h₃.r8] at w4 w5 f
    have fb : Frame [bufR s₀] s₃.mem s₄.mem := f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, Region.sub_prefix (by decide)⟩
    have fs : Frame [scrR s₀] s₃.mem s₄.mem := fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, buf_scr⟩
    refine ⟨c, hc, hst s₃ s₄ h₃.kp (by rw [g]) (by rw [g]) (by rw [g]) (by rw [g]) rd wr (fb.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, fun _ h => h⟩),
      h₃.le, by rw [g, h₃.r8], by rw [g, h₃.r9], by rw [g, h₃.r11], by rw [g, h₃.r10], by rw [g, h₃.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g, h₃.keep r h1 h2 h3 h4 h5 h6 h7], by rw [rd, h₃.rd], by rw [wr, h₃.wr],
      h₃.frame.trans (fs.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩),
      fun k hk => by
        rw [AesCbc.X86_64.bytesAt_frame fb (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right buf_scr) (by decide), h₃.data k hk],
      fun j hj => ?_, by rw [g, h₃.rdx]⟩
    rw [bytesAt_b16]
    by_cases hj4 : j < 4
    · rw [show slot s₀ j = S s₀ + BitVec.ofNat 64 (bufOff + 16 * j) from rfl, w4 j hj4]
      have := t₃.tw 0 (by decide) j hj4
      rw [show c + (4 * 0 + j) = c + j by omega] at this
      exact this
    · rw [show slot s₀ j = S s₀ + BitVec.ofNat 64 (bufOff + 64 + 16 * (j - 4)) by
          rw [slot]; congr 2; omega, w5 (j - 4) (by omega)]
      have := t₃.tw 1 (by decide) (j - 4) (by omega)
      rw [show c + (4 * 1 + (j - 4)) = c + j by omega] at this
      exact this

/-- The sixteen-block loop, then the eight-block loop: `Vaes.LoopOk`. -/
theorem loopsTo_ok {enc : Bool} {KP : State → Prop} {f16 f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf16 : Blk16 enc f16 KP s₀) (hf8 : Blk8 enc f8 KP s₀) :
    LoopOk enc (loops Impl.AesXts.X86_64VaesTo.ix f16 (Impl.AesXts.X86_64VaesTo.loop8 f8)) KP s₀ := by
  intro s h _
  refine WP.seq (WP.mono (cmpR9To_ok hst h 16 16 (by decide) (by decide)) fun s₁ ⟨h₁, cf₁⟩ => ?_)
  refine WP.seq (WP.mono (loop16To_wp hp hst hf16 h₁ (by rw [cf₁, Nat.sub_zero])) fun s₂ ⟨c, _, h₂⟩ => ?_)
  rw [show ([.vop .vzeroupper, .alu .cmp .r9 (.imm 8)] : List Instr) = [.vop .vzeroupper] ++
    [.alu .cmp .r9 (.imm 8)] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have v : WP isa (.block [.vop .vzeroupper]) s₂ (GInv enc KP s₀ c c) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact h₂.congr hst (fun _ _ => rfl) rfl rfl rfl
  refine WP.mono v fun s₃ h₃ => WP.mono (cmpR9To_ok hst h₃ 8 8 (by decide) (by decide)) fun s₄ ⟨h₄, cf₄⟩ => ?_
  exact groups_wp hp hst hf8 h₄ cf₄

theorem encryptTo_wp {s₀ : State} (h0 : (To.xtsToX86_64 true).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesZ.encryptTo s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 true).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loopsTo_ok hp₁ (kpe_stable hp₁) ?_ ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, kpe_pre hp₁ h⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    refine WP.mono (Aes.X86_64.VaesZ.aesZ_ok .xmm8 regsZ (by decide) (by decide) hp₁.rounds (fun _ => []) []
      (fun _ h => absurd h List.not_mem_nil) (fun _ _ => True)
      (fun _ _ _ s _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial) s hK trivial
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, _, f⟩ => ⟨fun b hb l hl => e b hb l hl, by simpa using f⟩
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.Vaes.aes_ok regs4 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem decryptTo_wp {s₀ : State} (h0 : (To.xtsToX86_64 false).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesZ.decryptTo s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 false).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loopsTo_ok hp₁ (kpd_stable hp₁) ?_ ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => imc_pre hp₁ h)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesZ.aesDecZ_ok .xmm8 regsZ (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesBlocks.aesDec_ok regs4 (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

end VG.Proof.AesXts.X86_64.VaesTo
