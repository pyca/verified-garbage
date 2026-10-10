import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ## Aes -/
section

/-!
# AES rounds with interleaved work that writes scratch memory

The intervening work preserves the AES states and the key invariant, but
may prepare the next batch in memory and reuse the round-key register.
`Q` describes that work; ordinary AES rounds preserve it through `YFrame`.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.StitchAvx8 (aesFixed)
open VG.Impl.Aes.X86_64.Vaes (keyOpL roundL)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.Vaes (RInv lanes keyOpL_ok roundL_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys st rnds_zero cipher_eq ea_at
  byte_roundKey pxor_st aesenclast_st)
open VG.Spec.Aes (roundKey cipher)

theorem fixedRounds_ok (regs : List XReg) (hnd : regs.Nodup) (h1 : .xmm1 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Nat → Spec.Aes.State}
    (g : Nat → List Instr) (Q : Nat → State → Prop)
    (hkeys : ∀ j s, Q j s → Keys nr w s)
    (hg : ∀ j, 1 ≤ j → j < nr → ∀ s, Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧
        ∀ b ∈ regs, ∀ l < lanes .l128, s'.lane b l = s.lane b l)
    (hq : ∀ j s s', Q j s → YFrame (.xmm1 :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k < nr)
    (hI : RInv .l128 regs w x 0 s) (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j =>
      roundL .l128 .xmm1 regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv .l128 regs w x k s' ∧ Q (k + 1) s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hI, hQ⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (roundL_ok .l128 .xmm1 regs hnd h1 (k := k) (by omega)
      (hkeys _ _ hQ₁) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) hk s₂ (hq _ _ _ hQ₁ hf₂))
      fun s' ⟨hQ', he⟩ => ⟨fun b hb l hl => ?_, hQ'⟩
    rw [he b hb l hl]
    exact hI₂ b hb l hl

theorem aesFixed_ok (nr : Nat) (hnr : 0 < nr) (regs : List XReg)
    (hnd : regs.Nodup) (h1 : .xmm1 ∉ regs) {w : List Byte}
    (g : Nat → List Instr) (Q : Nat → State → Prop)
    (hkeys : ∀ j s, Q j s → Keys nr w s)
    (hg : ∀ j, 1 ≤ j → j < nr → ∀ s, Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧
        ∀ b ∈ regs, ∀ l < lanes .l128, s'.lane b l = s.lane b l)
    (hq : ∀ j s s', Q j s → YFrame (.xmm1 :: regs) s s' → Q j s')
    (hlast : ∀ s, Q nr s →
      s.ea (at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int))
    (s : State) (hQ : Q 1 s) :
    WP isa (aesFixed nr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < lanes .l128,
        st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧ Q nr s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.lane b l)
  have hK := hkeys _ _ hQ
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  rw [aesFixed, List.append_assoc, WP.block_append_iff]
  refine WP.mono (keyOpL_ok .l128 .xmm1 regs .vpxor _ s hnd h1
    (by rw [ea_at]; exact hK.keys 0 (by omega))) fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : RInv .l128 regs w x 0 s₁ := fun b hb l hl => by
    rw [hv₁ b hb l hl]
    show st (XBinOp.eval .pxor _ _) = _
    rw [pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
  rw [WP.block_append_iff]
  refine WP.mono (fixedRounds_ok regs hnd h1 g Q hkeys hg hq (nr - 1) s₁
    (by omega) hI₁ (hq _ _ _ hQ hf₁)) fun s₂ ⟨hI₂, hQ₂⟩ => ?_
  have hn : nr - 1 + 1 = nr := by omega
  rw [hn] at hQ₂
  have hK₂ := hkeys _ _ hQ₂
  have hea := hlast _ hQ₂
  refine WP.mono (keyOpL_ok .l128 .xmm1 regs .vaesenclast _ s₂ hnd h1
    (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _))) fun s' ⟨hv, hf⟩ =>
      ⟨fun b hb l hl => ?_, hq _ _ _ hQ₂ hf⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## GhBits -/
section

/-!
# The eight-block loop's carry-less products and reduction

The first product initializes the accumulators. Reduction folds `lo` into
`mid` and then `mid` into `hi`, using the same `reduceB` as the AVX-512
implementation, on a single 128-bit lane.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only reduceB eval_pxor)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchAvx8 (accInit acc reduceFinal)

private theorem xmm_setXmm (s : State) (d r : XReg) (v : BitVec 128) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

private theorem liftPure (is ss : List Instr) (rs : List XReg)
    (hcode : lane0Block is = some ss) (hgp : is.all noGpr = true)
    (hdst : ∀ r, r ∉ rs → r ∉ is.filterMap vdst)
    (post : State → Prop) (s : State)
    (h : WP isa (.block ss) (s.proj 0) fun t => post t ∧ Only rs (s.proj 0) t) :
    WP isa (.block is) s fun s' => post (s'.proj 0) ∧ YFrame rs s s' := by
  refine WP.mono (WP.lane0 hcode h) fun s' ⟨⟨hp, ho⟩, hi, hg⟩ => ?_
  refine ⟨hp, hg hgp, by simpa using ho.mem, by simpa using ho.rd,
    by simpa using ho.wr, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using ho.xmm r hr
  · exact hi r (hdst r hr)

private def initSse : List Instr :=
  [.xop (.bin .movdqa .xmm8 .xmm7), .xop (.pclmulqdq .xmm8 .xmm12 0x00),
   .xop (.bin .movdqa .xmm10 .xmm7), .xop (.pclmulqdq .xmm10 .xmm12 0x11),
   .xop (.bin .movdqa .xmm9 .xmm7), .xop (.pclmulqdq .xmm9 .xmm12 0x01),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x10),
   .xop (.bin .pxor .xmm9 .xmm11)]

private theorem initSse_ok (s : State) :
    WP isa (.block initSse) s fun s' =>
      prod s' = Prod.zero.acc (s.xmm .xmm7) (s.xmm .xmm12) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [initSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, eval_pxor, eval_movdqa, xmm_setXmm, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prod, Prod.acc, Prod.zero, xmm_setXmm]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem accInit_ok (s : State) :
    WP isa (.block (accInit .xmm7 .xmm12)) s fun s' =>
      prod (s'.proj 0) = Prod.zero.acc (s.lane .xmm7 0) (s.lane .xmm12 0) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine liftPure _ initSse _ rfl rfl ?_ _ s (initSse_ok (s.proj 0))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [accInit, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem acc_ok (s : State) :
    WP isa (.block (acc .xmm7 .xmm12)) s fun s' =>
      prod (s'.proj 0) = (prod (s.proj 0)).acc (s.lane .xmm7 0) (s.lane .xmm12 0) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine liftPure _ (Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12) _ rfl rfl ?_ _ s
    (Pclmul.acc_ok .xmm7 .xmm12 (s.proj 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [acc, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

private def redSse : List Instr :=
  [.movdquLoad .xmm1 (at_ .r11 784),
   .xop (.bin .movdqa .xmm11 .xmm8), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm8 .xmm8 0x4e),
   .xop (.bin .pxor .xmm9 .xmm8), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa .xmm11 .xmm9), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm9 .xmm9 0x4e),
   .xop (.bin .movdqa .xmm2 .xmm10), .xop (.bin .pxor .xmm2 .xmm9),
   .xop (.bin .pxor .xmm2 .xmm11)]

private theorem redSse_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block redSse) s fun s' =>
      s'.xmm .xmm2 = reduceB (prod s) ∧ Only [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [redSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, hin, Option.map_some, eval_pxor, eval_movdqa,
    xmm_setXmm, reduceCtorEq, ↓reduceIte, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceB, Pclmul.fold, prod, BitVec.xor_assoc]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem reduceFinal_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block reduceFinal) s fun s' =>
      s'.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧
      YFrame [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] s s' := by
  refine liftPure _ redSse _ rfl rfl ?_ _ s (redSse_ok (s.proj 0) hin hc)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [reduceFinal, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## GhLoad -/
section

/-!
# Hashing a prepared input

The order 1, …, 7, 0 initializes the accumulators on block 1 and incorporates
the previous hash value on block 0. Both input and power are already in
native field order in the scratch buffer.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (gh8)
open VG.Spec.Gcm (Block)

def power (s : State) (k : Nat) : BitVec 128 :=
  s.mem.readW (s.ea (at_ .r11 (16 * (8 + k % 8)))) 128

def input (s : State) (k : Nat) : BitVec 128 :=
  s.mem.readW (s.ea (at_ .r11 (512 + 16 * (k % 8)))) 128 ^^^
    (if k % 8 = 0 then s.lane .xmm2 0 else 0)

private def inputs (s : State) (k : Nat) : State :=
  (s.setV .l128 .xmm12 (power s k) 0).setV .l128 .xmm7 (input s k) 0

private def loadInputs (k : Nat) : List Instr :=
  [.vmovdquLoad .l128 .xmm12 (at_ .r11 (16 * (8 + k % 8))),
   .vmovdquLoad .l128 .xmm7 (at_ .r11 (512 + 16 * (k % 8)))] ++
    (if k % 8 = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else [])

private theorem prefix_ok (s : State) (k : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k % 8)))) 16)
    (hx : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * (k % 8)))) 16) :
    WP isa (.block (loadInputs k)) s fun t => t = inputs s k := by
  apply WP.of_runBlock
  by_cases hk : k % 8 = 0 <;>
    (try simp only [hk] at hp hx) <;>
    simp only [loadInputs, hk, ite_true, ite_false, List.append_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, hp, hx,
      State.setV_rd, State.setV_wr, State.setV_ea, State.setV_mem, Option.map_some,
      VOp.exec, VBinOp.sse, XBinOp.eval, State.lane, xmm_setV,
      reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left',
      inputs, input, power] <;>
    simp (config := { contextual := true }) [State.setV]

private theorem inputs_frame (s : State) (k : Nat) :
    YFrame [.xmm12, .xmm7] s (inputs s k) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro r hr l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [inputs, State.lane, xmm_setV, ymmHi_setV_128, hr.1, hr.2, ite_false]

/-- Registers modified by one hash product. -/
abbrev ghRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11]

theorem gh8_ok (s : State) (k : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k % 8)))) 16)
    (hx : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * (k % 8)))) 16) :
    WP isa (.block (gh8 k)) s fun t =>
      prod (t.proj 0) = (if k % 8 = 1 then Prod.zero else prod (s.proj 0)).acc
        (input s k) (power s k) ∧ YFrame ghRegs s t := by
  change WP isa (.block (loadInputs k ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (prefix_ok s k hp hx) fun t ht => ?_
  subst t
  have hf := inputs_frame s k
  have finish : ∀ t, YFrame [.xmm8, .xmm9, .xmm10, .xmm11] (inputs s k) t →
      YFrame ghRegs s t := fun t h => (hf.comp h).mono fun r hr => by
        simpa only [ghRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          or_assoc] using hr
  by_cases hk : k % 8 = 1
  · rw [ite_eq_left hk]
    refine WP.mono (accInit_ok (inputs s k)) fun t ⟨hp, hfr⟩ => ⟨?_, finish t hfr⟩
    simpa only [inputs, State.lane, xmm_setV, reduceCtorEq, ite_true, ite_false, hk, ite_true] using hp
  · rw [ite_eq_right hk]
    refine WP.mono (acc_ok (inputs s k)) fun t ⟨hp, hfr⟩ => ⟨?_, finish t hfr⟩
    simpa only [inputs, prod, State.proj_xmm, State.lane, xmm_setV, reduceCtorEq,
      ite_true, ite_false, hk, ite_false] using hp

def hashInput (X : Nat → Block) (y : Block) (k : Nat) : Block :=
  X k ^^^ (if k = 0 then y else 0)

def accN (X P : Nat → Block) (y : Block) (n : Nat) : Prod :=
  (List.range n).foldl (fun a i => a.acc (hashInput X y ((i + 1) % 8)) (P ((i + 1) % 8))) Prod.zero

theorem accN_succ (X P : Nat → Block) (y : Block) (n : Nat) :
    accN X P y (n + 1) = (accN X P y n).acc (hashInput X y ((n + 1) % 8)) (P ((n + 1) % 8)) := by
  simp only [accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Hash -/
section

/-!
# Hashing a complete prepared batch

All eight inputs are consumed in the order 1, …, 7, 0. The first product
does not depend on the old accumulators. Memory and the AES state registers
are preserved throughout.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (gh8 hash8 reduceFinal)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block)

def bufferBlock (s : State) (k : Nat) : Block :=
  s.mem.readW (s.ea (at_ .r11 (512 + 16 * k))) 128

def bufferPower (s : State) (k : Nat) : Block :=
  s.mem.readW (s.ea (at_ .r11 (16 * (8 + k)))) 128

private theorem input_frame {s t : State} (f : YFrame ghRegs s t) (k : Nat) :
    input t k = hashInput (bufferBlock s) (s.lane .xmm2 0) (k % 8) := by
  simp only [input, hashInput, bufferBlock, f.mem, State.ea, f.gpr,
    f.lane .xmm2 (by decide) 0 (by decide)]

private theorem power_frame {s t : State} (f : YFrame ghRegs s t) (k : Nat) :
    power t k = bufferPower s (k % 8) := by
  simp only [power, bufferPower, f.mem, State.ea, f.gpr]

theorem hashSteps_ok (s : State)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k)))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * k))) 16)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun i => gh8 ((i + 1) % 8))) s fun t =>
      prod (t.proj 0) = (if n = 0 then prod (s.proj 0) else
        accN (bufferBlock s) (bufferPower s) (s.lane .xmm2 0) n) ∧ YFrame ghRegs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hacc, hf⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (gh8_ok t ((n + 1) % 8) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hp _ (Nat.mod_lt _ (by decide))) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hx _ (Nat.mod_lt _ (by decide))))
      fun u ⟨ha, hu⟩ => ⟨?_, hf.trans hu⟩
    rw [ha, input_frame hf, power_frame hf, Nat.mod_mod]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, accN_succ]
    by_cases hz : n = 0
    · subst n
      simp only [Nat.zero_add, Nat.reduceMod, ite_true, accN, List.range_zero, List.foldl_nil]
    · have hm : (n + 1) % 8 ≠ 1 := by omega
      rw [ite_eq_right hm, hacc, ite_eq_right hz]

/-- One complete GHASH batch and its final reduction. -/
theorem hash8_ok (s : State)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * (8 + k)))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (512 + 16 * k))) 16)
    (hc : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hv : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block hash8) s fun t =>
      t.lane .xmm2 0 = reduceB (accN (bufferBlock s) (bufferPower s) (s.lane .xmm2 0) 8) ∧
      YFrame (ghRegs ++ ([.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] : List XReg)) s t := by
  rw [hash8, WP.block_append_iff]
  refine WP.mono (hashSteps_ok s hp hx 8 (by decide)) fun t ⟨ha, hf⟩ => ?_
  refine WP.mono (reduceFinal_ok t (by
    simpa only [hf.rd, hf.wr, State.ea, hf.gpr] using hc) (by
    simpa only [hf.mem, State.ea, hf.gpr] using hv)) fun u ⟨hu, hfu⟩ => ⟨?_, hf.comp hfu⟩
  simpa only [ha, Nat.reduceEqDiff, ite_false] using hu

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Loads -/
section

/-!
# Loading the eight counter templates

Every AES state has a distinct register. Loading the next state preserves
the states already loaded, and changes no memory or integer registers.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs)
open VG.Impl.Aes.X86_64.AesNi (at_)

theorem aregs_distinct : ∀ i < 8, ∀ j < 8,
    aregs.getD i .xmm3 = aregs.getD j .xmm3 → i = j := by decide

theorem aregs_member : ∀ i < 8, aregs.getD i .xmm3 ∈ aregs := by decide

theorem loadCounters_ok (s : State)
    (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (640 + 16 * i))) 16)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun i =>
      .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640 + 16 * i)))) s fun t =>
      (∀ i < n, t.lane (aregs.getD i .xmm3) 0 =
        s.mem.readW (s.ea (at_ .r11 (640 + 16 * i))) 128) ∧ YFrame aregs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), YFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hv, hf⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    have hi : InRegions (t.rd ++ t.wr) (t.ea (at_ .r11 (640 + 16 * n))) 16 := by
      simpa only [hf.rd, hf.wr, State.ea, hf.gpr] using hin n (by omega)
    rw [WP.block_cons_iff]
    refine ⟨t.setV .l128 (aregs.getD n .xmm3)
      (t.mem.readW (t.ea (at_ .r11 (640 + 16 * n))) 128) 0,
      by simp only [isa, exec, State.load128, hi, ite_true, Option.map_some],
      WP.block_nil ⟨?_, ?_⟩⟩
    · intro i hi
      simp only [State.lane, xmm_setV, ite_true]
      by_cases he : i = n
      · subst i
        simp only [ite_true, hf.mem, State.ea, hf.gpr]
      · have hr : aregs.getD i .xmm3 ≠ aregs.getD n .xmm3 :=
          fun h => he (aregs_distinct i (by omega) n (by omega) h)
        rw [ite_eq_right hr]
        exact hv i (by omega)
    · refine hf.trans ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro r hr l hl
      have he : r ≠ aregs.getD n .xmm3 := fun h => hr (h ▸ aregs_member n (by omega))
      simp only [State.lane, xmm_setV, ymmHi_setV_128, he, ite_false]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
