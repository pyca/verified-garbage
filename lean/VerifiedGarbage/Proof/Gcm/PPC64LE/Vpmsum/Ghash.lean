module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Fold
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Base
public import VerifiedGarbage.Proof.Gcm.Clmul.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.Spec
import Mathlib.Tactic.Ring.RingNF
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Impl.Gcm.PPC64LE.Vpmsum
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Lit

/-! # GHASH using POWER8 polynomial multiplication -/

@[expose] public section
namespace VG.Proof.Gcm.PPC64LE.Vpmsum
open VG VG.PPC64LE
open VG.Impl.Gcm.PPC64LE.Vpmsum (Y C U LO MID HI A T H MASK Z keyLow keyHigh)
open VG.Proof.Gcm.Clmul VG.Proof.Gcm.Poly
open VG.Spec.Gcm (blockAt blocksAt ghashFrom)

structure Buffers (s₀ s : State) : Prop where
  yptr : s.gpr .r4 = yp s₀
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Buffers.keep {rs : List VReg} {s₀ s t : State} (h : Buffers s₀ s)
    (ho : VOnly rs s t) : Buffers s₀ t :=
  ⟨(congrFun ho.gpr .r4).trans h.yptr, ho.mem.trans h.mem, ho.rd.trans h.rd, ho.wr.trans h.wr⟩

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  cfg : Config s
  stable : Buffers s₀ s
  r5 : s.gpr .r5 = blkAddr s₀ i
  r6 : s.gpr .r6 = BitVec.ofNat 64 (nb s₀-i)
  key : x * φ (s.vpr H) = φ (H₀ s₀)
  y : ρ (s.vpr Y) = φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i))

theorem φ_ext8_self (v : BitVec 128) : φ (ext8 v v) = ρ v := by
  have h := ρ_ext8_self (ext8 v v)
  rw [ext8_ext8] at h
  exact h.symm

theorem init_ok (s₀ : State) (hp : Pre s₀) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.prologue) s₀ (Inv s₀ 0) := by
  rw [Impl.Gcm.PPC64LE.Vpmsum.prologue]
  repeat rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₀) fun s₁ ⟨hc₁, hh₁, hs₁⟩ => ?_
  have hinH : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r3) 16 := by
    rw [hs₁.rd, hs₁.wr, hs₁.regs .r3 (by decide)]
    exact ⟨hR s₀, by simp [hp.rd], by simp [Region.Contains]⟩
  refine WP.mono (loadRev_ok A .r3 s₁ (by decide) hc₁.zero hc₁.mask (by decide) hinH)
    fun s₂ ⟨ha₂, ho₂⟩ => ?_
  have hc₂ := hc₁.keep ho₂ (by decide) (by decide) (by decide)
  have hs₂ := hs₁.trans (VOnly.stable ho₂)
  have ha₂' : s₂.vpr A = ext8 (H₀ s₀) (H₀ s₀) := by
    simpa only [hs₁.mem, hs₁.regs .r3 (by decide)] using ha₂
  have hh₂ : s₂.vpr H = xInv2 := (ho₂.v H (by decide)).trans hh₁
  refine WP.mono (mul_ok H A H s₂ (by unfold Free; decide) (by unfold Free; decide) hc₂.c hc₂.z)
    fun s₃ ⟨hh₃, ho₃⟩ => ?_
  have hc₃ := hc₂.keep ho₃ (by decide) (by decide) (by decide)
  have hs₃ := hs₂.trans (VOnly.stable ho₃)
  refine WP.mono (vector_step _ H _ s₃ (exec_shift8 H H H s₃)) fun s₄ ⟨hh₄, ho₄⟩ => ?_
  have hc₄ := hc₃.keep ho₄ (by decide) (by decide) (by decide)
  have hs₄ := hs₃.trans (VOnly.stable ho₄)
  have hinY : InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .r4) 16 := by
    rw [hs₄.rd, hs₄.wr, hs₄.regs .r4 (by decide)]
    exact ⟨yR s₀, by simp [hp.wr], by simp [Region.Contains]⟩
  refine WP.mono (loadRev_ok Y .r4 s₄ (by decide) hc₄.zero hc₄.mask (by decide) hinY)
    fun s₅ ⟨hy₅, ho₅⟩ => ?_
  have hs₅ := hs₄.trans (VOnly.stable ho₅)
  refine ⟨hc₄.keep ho₅ (by decide) (by decide) (by decide),
    ⟨hs₅.regs .r4 (by decide), hs₅.mem, hs₅.rd, hs₅.wr⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [blkAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hs₅.regs .r5 (by decide)
  · simpa only [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hs₅.regs .r6 (by decide)
  · rw [ho₅.v H (by decide), hh₄, half_self, φ_ext8_self, hh₃, ρ_mulV, ha₂', hh₂, ρ_ext8_self]
    calc
      x * (x * φ (H₀ s₀) * φ xInv2) = φ (H₀ s₀) * (x^2 * φ xInv2) := by ring
      _ = φ (H₀ s₀) := by rw [x2_φ_xInv2, mul_one]
  · rw [hy₅, hs₄.mem, hs₄.regs .r4 (by decide), ρ_ext8_self]
    simp only [blocksAt, List.range_zero, List.map_nil, ghashFrom, List.foldl_nil]

theorem advance_ok (s : State) :
    WP isa (.block [.addi .r5 .r5 16, .subi .r6 .r6 1]) s
      (· = (s.write .r5 (s.gpr .r5 + 16)).write .r6 (s.gpr .r6 - 1)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi' (d := .r5) (n := .r5) (imm := 16) (by decide),
    exec_subi' (d := .r6) (n := .r6) (imm := 1) (by decide), RegUpd.gpr_write, reduceCtorEq, ite_false,
    BitVec.ofNat_eq_ofNat, Option.some.injEq, exists_eq_left']

theorem body_ok {s₀ s : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) (h : Inv s₀ i s) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.body) s (Inv s₀ (i+1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r5) 16 := by
    rw [h.stable.rd, h.stable.wr, h.r5]
    refine ⟨dR s₀, by simp [hp.rd], contains_offset (by omega) (by have := hp.nb_lt; omega)⟩
  rw [Impl.Gcm.PPC64LE.Vpmsum.body]
  repeat rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .r5 s (by decide) h.cfg.zero h.cfg.mask (by decide) hin)
    fun s₁ ⟨ha₁, ho₁⟩ => ?_
  have hc₁ := h.cfg.keep ho₁ (by decide) (by decide) (by decide)
  have hb₁ := h.stable.keep ho₁
  refine WP.mono (vector_step _ A _ s₁ (exec_xor A A Y s₁)) fun s₂ ⟨ha₂, ho₂⟩ => ?_
  have hc₂ := hc₁.keep ho₂ (by decide) (by decide) (by decide)
  have hb₂ := hb₁.keep ho₂
  refine WP.mono (mul_ok Y A H s₂ (by unfold Free; decide) (by unfold Free; decide) hc₂.c hc₂.z)
    fun s₃ ⟨hy₃, ho₃⟩ => ?_
  have hc₃ := hc₂.keep ho₃ (by decide) (by decide) (by decide)
  have hb₃ := hb₂.keep ho₃
  have hg : s₃.gpr = s.gpr := ho₃.gpr.trans (ho₂.gpr.trans ho₁.gpr)
  have hh : s₃.vpr H = s.vpr H := (ho₃.v H (by decide)).trans
    ((ho₂.v H (by decide)).trans (ho₁.v H (by decide)))
  have hy : ρ (s₃.vpr Y) = φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i+1))) := by
    rw [hy₃, ρ_mulV, ha₂, ρ_xor, ha₁, h.stable.mem, h.r5, ρ_ext8_self,
      ho₂.v H (by decide), ho₁.v H (by decide), ho₁.v Y (by decide), h.y,
      Proof.Gcm.ghashFrom_blocksAt_succ, φ_mul, φ_xor]
    calc
      x * (φ (blockAt s₀.mem (blkAddr s₀ i)) +
          φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i))) * φ (s.vpr H) =
        (φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)) +
          φ (blockAt s₀.mem (blkAddr s₀ i))) * (x * φ (s.vpr H)) := by ring
      _ = _ := by rw [h.key]
  refine WP.mono (advance_ok s₃) fun s₄ he => ?_
  subst s₄
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hc₃.zero
  · simpa only [vpr_write] using hc₃.c
  · simpa only [vpr_write] using hc₃.mask
  · simpa only [vpr_write] using hc₃.z
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hb₃.yptr
  · simpa only [RegUpd.mem_write] using hb₃.mem
  · simpa only [RegUpd.rd_write] using hb₃.rd
  · simpa only [RegUpd.wr_write] using hb₃.wr
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, hg, h.r5,
      blkAddr, Nat.mul_succ]
    change dp s₀ + BitVec.ofNat 64 (16*i) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
  · simp only [RegUpd.gpr_write_self, hg, h.r6]
    change BitVec.ofNat 64 (nb s₀-i) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simpa only [vpr_write, hh] using h.key
  · simpa only [vpr_write] using hy

theorem epilogue_ok {s₀ s : State} (hp : Pre s₀) (h : Inv s₀ (nb s₀) s) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.epilogue) s (Proof.Gcm.ghashPPC64LE.post s₀) := by
  have hout : InRegions s.wr (s.gpr .r4) 16 := by
    rw [h.stable.wr, h.stable.yptr]
    exact ⟨yR s₀, by simp [hp.wr], by simp [Region.Contains]⟩
  have hs : exec (.stxvd2x T .r4 .r0) (s.writeV T (rev128 (s.vpr Y))) =
      some { s.writeV T (rev128 (s.vpr Y)) with
        mem := s.mem.write (s.gpr .r4) 16 (swapDwords (rev128 (s.vpr Y))) } := by
    simp only [reduceExec, addrX, reduceCtorEq, ne_eq, not_false_eq_true, ite_true,
      gpr_writeV, h.cfg.zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.bind_some,
      State.store, wr_writeV, hout, vpr_writeV, mem_writeV]
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.epilogue, runBlock_cons, runStep_some, runBlock_nil,
    exec_reverse _ _ _ h.cfg.mask, hs, Option.some.injEq, exists_eq_left']
  change blockAt (s.mem.write (s.gpr .r4) 16 (swapDwords (rev128 (s.vpr Y)))) (yp s₀) = _
  rw [h.stable.yptr, store_value]
  apply φ_inj
  rw [φ_ext8_self, h.y]

structure BulkInv (h : BitVec 128) (s₀ : State) (i : Nat) (s : State) : Prop where
  cfg : Config s
  stable : Buffers s₀ s
  r5 : s.gpr .r5 = blkAddr s₀ i
  r6 : s.gpr .r6 = BitVec.ofNat 64 (nb s₀-i)
  keys : PackedKeys h 4 s
  y : ρ (s.vpr Y) = φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i))

theorem prepare_bulk_ok {s₀ s : State} {i : Nat} (hi : Inv s₀ i s) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.preparePowers 8 ++ Impl.Gcm.PPC64LE.Vpmsum.packedKeys)) s
      (BulkInv (s.vpr H) s₀ i) := by
  rw [WP.block_append_iff]
  refine WP.mono (powers_ok 8 (by decide) (by decide) s hi.cfg.c hi.cfg.z) fun u ⟨hp,hu⟩ => ?_
  refine WP.mono (packedKeys_ok (s.vpr H) u hp) fun v ⟨hk,hv⟩ => ?_
  have hf := hu.trans hv
  exact ⟨(hi.cfg.keep hu (by decide) (by decide) (by decide)).keep hv
      (by decide) (by decide) (by decide),
    hi.stable.keep hf, (congrFun hf.gpr .r5).trans hi.r5,
    (congrFun hf.gpr .r6).trans hi.r6, hk, (congrArg ρ (hf.v Y (by decide))).trans hi.y⟩

theorem bulk_body_ok {s₀ s : State} (hp : Pre s₀) {h : BitVec 128} {i : Nat}
    (hkey : x * φ h = φ (H₀ s₀)) (hi : i+8 ≤ nb s₀) (hs : BulkInv h s₀ i s) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.packedBody) s (BulkInv h s₀ (i+8)) := by
  have hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .r5+BitVec.ofNat 64 (16*k)) 16 := by
    intro k hk
    rw [hs.stable.rd, hs.stable.wr, hs.r5, blkAddr, Offset.add_add]
    refine ⟨dR s₀, by simp [hp.rd], contains_offset (by omega) (by have := hp.nb_lt; omega)⟩
  refine WP.mono (packedBody_ok h s hs.cfg hs.keys hr) fun t ⟨hy,hf⟩ => ?_
  have hy' : ρ (t.vpr Y) = φ (ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i+8))) := by
    rw [hkey, hs.y] at hy
    have hld : ∀ j, ρ (loadedAt s (16*j)) =
        φ (Spec.Gcm.blockAt s₀.mem (dp s₀+BitVec.ofNat 64 (16*(i+j)))) := by
      intro j
      rw [loadedAt, ρ_ext8_self, hs.stable.mem, hs.r5, blkAddr, Offset.add_add, ← Nat.mul_add]
    simp_rw [hld] at hy
    rw [← hashField_ghash] at hy
    exact hy
  have hc : Config ((s.write .r5 (s.gpr .r5+128)).write .r6 (s.gpr .r6-8)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.cfg.zero
    · simpa only [vpr_write] using hs.cfg.c
    · simpa only [vpr_write] using hs.cfg.mask
    · simpa only [vpr_write] using hs.cfg.z
  refine ⟨hc.keep hf (by decide) (by decide) (by decide), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hy'⟩
  · rw [hf.gpr]
    simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.stable.yptr
  · rw [hf.mem]
    simpa only [RegUpd.mem_write] using hs.stable.mem
  · rw [hf.rd]
    simpa only [RegUpd.rd_write] using hs.stable.rd
  · rw [hf.wr]
    simpa only [RegUpd.wr_write] using hs.stable.wr
  · rw [hf.gpr]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, hs.r5, blkAddr]
    change dp s₀+BitVec.ofNat 64 (16*i)+BitVec.ofNat 64 128 = _
    rw [Offset.add_add, show 16*i+128=16*(i+8) by omega]
  · rw [hf.gpr]
    simp only [RegUpd.gpr_write_self, hs.r6]
    change BitVec.ofNat 64 (nb s₀-i)-BitVec.ofNat 64 8 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · intro j hj
    have f : keyLow j ∉ bulkWritten ∧ keyHigh j ∉ bulkWritten := by
      have f : ∀ j : Fin 4, keyLow j ∉ bulkWritten ∧ keyHigh j ∉ bulkWritten := by decide
      exact f ⟨j,hj⟩
    rw [hf.v (keyLow j) f.1, hf.v (keyHigh j) f.2]
    simpa only [vpr_write] using hs.keys j hj

theorem loop_ok {s₀ s : State} (hp : Pre s₀) {start : Nat} (hpos : start < nb s₀) (h : Inv s₀ start s) :
    WP isa (.loop (.block Impl.Gcm.PPC64LE.Vpmsum.body) (.nonzero .d .r6)) s
      (Inv s₀ (nb s₀)) := by
  let I : Nat → State → Prop := fun m t => ∃ i, m = nb s₀-i ∧ i < nb s₀ ∧ Inv s₀ i t
  have step : ∀ m t, I m t → WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.body) t fun u =>
      (eval (.nonzero .d .r6) u = some false ∧ Inv s₀ (nb s₀) u) ∨
      (eval (.nonzero .d .r6) u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨i, rfl, hi, ht⟩
    refine WP.mono (body_ok hp hi ht) fun u hu => ?_
    have he : eval (.nonzero .d .r6) u = some (BitVec.ofNat 64 (nb s₀-(i+1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hu.r6]
    by_cases hl : i+1 = nb s₀
    · left
      rw [hl, Nat.sub_self] at he
      exact ⟨he.trans (by decide), hl ▸ hu⟩
    · right
      have hne : BitVec.ofNat 64 (nb s₀-(i+1)) ≠ 0 := by
        intro hz
        have hn := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.nb_lt; omega)] at hn
        have hn0 : (0 : BitVec 64).toNat = 0 := rfl
        rw [hn0] at hn
        omega
      exact ⟨he.trans (by simpa using hne),
        nb s₀-(i+1), by omega, i+1, rfl, by omega, hu⟩
  exact WP.loop (M := isa) I step (nb s₀-start) s ⟨start, rfl, hpos, h⟩

theorem Config.write10 {s : State} (h : Config s) (v : BitVec 64) : Config (s.write .r10 v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using h.zero
  · simpa only [vpr_write] using h.c
  · simpa only [vpr_write] using h.mask
  · simpa only [vpr_write] using h.z

theorem Buffers.write10 {s₀ s : State} (h : Buffers s₀ s) (v : BitVec 64) : Buffers s₀ (s.write .r10 v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using h.yptr
  · simpa only [RegUpd.mem_write] using h.mem
  · simpa only [RegUpd.rd_write] using h.rd
  · simpa only [RegUpd.wr_write] using h.wr

theorem Inv.write10 {s₀ s : State} {i : Nat} (h : Inv s₀ i s) (v : BitVec 64) : Inv s₀ i (s.write .r10 v) := by
  refine ⟨h.cfg.write10 v, h.stable.write10 v, ?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using h.r5
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using h.r6
  · simpa only [vpr_write] using h.key
  · simpa only [vpr_write] using h.y

theorem BulkInv.write10 {h : BitVec 128} {s₀ s : State} {i : Nat} (hs : BulkInv h s₀ i s)
    (v : BitVec 64) : BulkInv h s₀ i (s.write .r10 v) := by
  refine ⟨hs.cfg.write10 v, hs.stable.write10 v, ?_, ?_, ?_, ?_⟩
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.r5
  · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.r6
  · simpa only [PackedKeys, vpr_write] using hs.keys
  · simpa only [vpr_write] using hs.y

theorem probe_ok (sh : Nat) (hsh : sh < 64) (s : State) :
    WP isa (.block [.lsr .d .r10 .r6 sh]) s (· = s.write .r10 (s.gpr .r6 >>> sh)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_lsr_d hsh,
    Option.some.injEq, exists_eq_left']

theorem quotient_zero {j : Nat} (hj : j < 2^64) (sh : Nat) :
    (BitVec.ofNat 64 j >>> sh) = 0 ↔ j < 2^sh := by
  constructor
  · intro he
    have hh := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
      Nat.shiftRight_eq_div_pow] at hh
    change j / 2^sh = 0 at hh
    exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos sh) hh
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
      Nat.shiftRight_eq_div_pow]
    change j / 2^sh = 0
    exact Nat.div_eq_of_lt he

theorem bulk_loop_ok {s₀ s : State} (hp : Pre s₀) {h : BitVec 128} {start : Nat}
    (hkey : x * φ h = φ (H₀ s₀)) (hpos : start+8 ≤ nb s₀) (hs : BulkInv h s₀ start s) :
    WP isa (.loop (.block (Impl.Gcm.PPC64LE.Vpmsum.packedBody ++ ([.lsr .d .r10 .r6 3] : List Instr)))
      (.nonzero .d .r10)) s fun t => ∃ j, j ≤ nb s₀ ∧ nb s₀-j < 8 ∧ BulkInv h s₀ j t := by
  let I : Nat → State → Prop := fun j t => BulkInv h s₀ j t ∧ t.gpr .r10 = BitVec.ofNat 64 (nb s₀-j) >>> 3
  have step : ∀ j t, j+8 ≤ nb s₀ → BulkInv h s₀ j t →
      WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedBody ++ ([.lsr .d .r10 .r6 3] : List Instr))) t (I (j+8)) := by
    intro j t hj ht
    rw [WP.block_append_iff]
    refine WP.mono (bulk_body_ok hp hkey hj ht) fun u hu => ?_
    refine WP.mono (probe_ok 3 (by decide) u) fun v hv => ?_
    subst v
    exact ⟨hu.write10 _, by rw [RegUpd.gpr_write_self, hu.r6]⟩
  refine WP.loop (M := isa)
    (fun m t => ∃ j, m = nb s₀-j ∧ j+8 ≤ nb s₀ ∧ BulkInv h s₀ j t)
    (fun m t ht => ?_) (nb s₀-start) s ⟨start,rfl,hpos,hs⟩
  obtain ⟨j,rfl,hj,ht⟩ := ht
  refine WP.mono (step j t hj ht) fun u hu => ?_
  have hz : u.gpr .r10 = 0 ↔ nb s₀-(j+8) < 8 := by
    rw [hu.2]
    exact quotient_zero (by have := hp.nb_lt; omega) 3
  have hev : eval (.nonzero .d .r10) u = some (u.gpr .r10 != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  by_cases hlast : nb s₀-(j+8) < 8
  · left
    rw [hz.mpr hlast] at hev
    exact ⟨hev.trans (by decide), j+8, hj, hlast, hu.1⟩
  · right
    have hne : u.gpr .r10 ≠ 0 := fun he => hlast (hz.mp he)
    exact ⟨hev.trans (by simpa using hne), nb s₀-(j+8), by omega,
      j+8,rfl,by omega,hu.1⟩

theorem bulk_ok {s₀ s : State} (hp : Pre s₀) {start : Nat}
    (hpos : start+8 ≤ nb s₀) (hs : Inv s₀ start s) :
    WP isa Impl.Gcm.PPC64LE.Vpmsum.bulk s fun t => ∃ j, j ≤ nb s₀ ∧ Inv s₀ j t := by
  unfold Impl.Gcm.PPC64LE.Vpmsum.bulk
  refine WP.seq (WP.mono (prepare_bulk_ok hs) fun u hu => ?_)
  refine WP.seq (WP.mono (bulk_loop_ok hp hs.key hpos hu) fun v ⟨j,hj,_,hv⟩ => ?_)
  refine WP.mono (recoverKey_ok (s.vpr H) v hv.keys) fun t ⟨hh,ht⟩ => ?_
  refine ⟨j,hj,hv.cfg.keep ht (by decide) (by decide) (by decide),
    hv.stable.keep ht, (congrFun ht.gpr .r5).trans hv.r5,
    (congrFun ht.gpr .r6).trans hv.r6, ?_, ?_⟩
  · rw [hh]
    exact hs.key
  · rw [ht.v Y (by decide)]
    exact hv.y

theorem finish_ok {s₀ s : State} (hp : Pre s₀) {i : Nat} (hi : i ≤ nb s₀) (hs : Inv s₀ i s) :
    WP isa Impl.Gcm.PPC64LE.Vpmsum.finish s (Proof.Gcm.ghashPPC64LE.post s₀) := by
  unfold Impl.Gcm.PPC64LE.Vpmsum.finish
  have hev : eval (.zero .d .r6) s = some (s.gpr .r6 == 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.seq (WP.ite (s.gpr .r6 == 0) hev (fun he => ?_) (fun he => ?_))
  · have hz : BitVec.ofNat 64 (nb s₀-i) = 0 := hs.r6.symm.trans (by simpa only [beq_iff_eq] using he)
    have hz' := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.nb_lt; omega)] at hz'
    change nb s₀-i = 0 at hz'
    have heq : i = nb s₀ := by omega
    subst i
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    exact epilogue_ok hp hs
  · have hipos : i < nb s₀ := by
      have hne : s.gpr .r6 ≠ 0 := by simpa only [beq_eq_false_iff_ne] using he
      by_contra hn
      have heq : i = nb s₀ := by omega
      rw [hs.r6,heq,Nat.sub_self] at hne
      exact hne rfl
    exact WP.mono (loop_ok hp hipos hs) fun t ht => epilogue_ok hp ht

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Gcm.PPC64LE.Vpmsum.ghash s₀ (Proof.Gcm.ghashPPC64LE.post s₀) := by
  unfold Impl.Gcm.PPC64LE.Vpmsum.ghash
  have hev : eval (.zero .d .r6) s₀ = some (s₀.gpr .r6 == 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite (s₀.gpr .r6 == 0) hev (fun he => ?_) (fun he => ?_)
  ·
    have hz : nb s₀ = 0 := by
      have he' : s₀.gpr .r6 = 0 := by simpa only [beq_iff_eq] using he
      simp [nb, he']
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    change Y₀ s₀ = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    rw [hz, Proof.Gcm.ghashFrom_blocksAt_zero]
  · refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (init_ok s₀ hp) fun u hu => ?_
    refine WP.mono (probe_ok 4 (by decide) u) fun v hv => ?_
    subst v
    have hinv := hu.write10 (u.gpr .r6 >>> 4)
    refine WP.seq ?_
    have hev' : eval (.zero .d .r10) (u.write .r10 (u.gpr .r6 >>> 4)) =
        some ((u.gpr .r6 >>> 4) == 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self]
    refine WP.ite ((u.gpr .r6 >>> 4) == 0) hev' (fun _ => ?_) (fun hn => ?_)
    · apply WP.of_runBlock
      simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
      exact finish_ok hp (Nat.zero_le _) hinv
    · have hne : u.gpr .r6 >>> 4 ≠ 0 := by simpa only [beq_eq_false_iff_ne] using hn
      rw [hu.r6] at hne
      have h16 : ¬ nb s₀ < 16 := by
        intro hlt
        exact hne ((quotient_zero (by have := hp.nb_lt; omega) 4).mpr hlt)
      refine WP.mono (bulk_ok hp (by omega) hinv) fun t ⟨j,hj,ht⟩ => finish_ok hp hj ht


def written : List Reg := [.r0, .r5, .r6, .r8, .r9, .r10]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Gcm.PPC64LE.Vpmsum.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPPC64LE.post s s' := by
  obtain ⟨t, s', he, hq, hk⟩ := WP.keep written (correct (pre_of s hs)) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hq⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashPPC64LE.pre Proof.Gcm.ghashPPC64LE.pub
    Impl.Gcm.PPC64LE.Vpmsum.ghash := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified :
    Verified PPC64LE.target Impl.Gcm.PPC64LE.Vpmsum.ghash (Spec.Gcm.ghashContract PPC64LE.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashPPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [Proof.Gcm.PPC64LE.Vpmsum.satState] using Proof.Gcm.PPC64LE.Vpmsum.satState)

end VG.Proof.Gcm.PPC64LE.Vpmsum
