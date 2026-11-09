module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64StitchAvx
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Aes
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.AesHash
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Blocks
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64StitchAvx
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Aes
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loop
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lane0
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.YFrame
meta import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
meta import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.AesHash
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Blocks
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok

/-!
# AES-GCM-SIV's loops with AES-NI, PCLMULQDQ and AVX

Untrusted: everything here is checked by Lean. The loops of
`Impl.AesGcmSiv.X86_64StitchAvx` meet the contracts of the 256-bit ones
(`Stitch.LoopsOk`, `loops_ok`): the interleaved loop of `open` (`dec_ok`),
and sealing's POLYVAL (`hash_ok`) and counter mode (`ctr_ok`) loops; and
they pass the taint analysis. The sections below: the POLYVAL loads and the
reduction, a batch of eight blocks, the setup, the interleaved loop, the
sealing loops, and the loops together.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.StitchAvx

section

/-!
# AES-GCM-SIV's loops with AES-NI: the POLYVAL loads and the reduction

Untrusted: everything here is checked by Lean. `ghA_ok`: `ghA d k` loads the
power at `r11 + 16 k` into `xmm12` and block `k` at `rdx + d + 16 k` as it is
(POLYVAL's field element of 16 bytes is them as a little-endian number,
`Spec.GcmSiv.ofBytes`) into `xmm7`, adds `Y` to block 0, and adds their
product to the accumulators, which block 1 starts, as AES-GCM's eight-state
loop does for its byte-reversed blocks (`Proof.Gcm.X86_64.StitchAvx8.gh8_ok`,
whose products `accInit_ok` and `acc_ok` this uses). `red_ok`: `red` reduces
them into `Y`, as `StitchAvx8.reduceFinal_ok` with the reduction constant
loaded into `xmm12`. `hashSteps_ok` and `hash8_ok`: the eight loads in the
order 1, …, 7, 0 (`StitchAvx8.accN`), and the reduction.
-/

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only reduceB eval_pxor)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.AesGcmSiv.X86_64StitchAvx (ghA red hash8 polyO)
open VG.Proof.Gcm.X86_64.StitchAvx8 (accInit_ok acc_ok accN accN_succ hashInput ghRegs)
open VG.Spec.Gcm (Block)

/-! ## A load -/

/-- The power of block `k`, at `r11 + 16 k`. -/
def powerA (s : State) (k : Nat) : BitVec 128 := s.mem.readW (s.ea (at_ .r11 (16 * k))) 128

/-- Block `k` of the eight at `rdx + d`, as it is. -/
def dataA (s : State) (d k : Nat) : BitVec 128 := s.mem.readW (s.ea (at_ .rdx (d + 16 * k))) 128

/-- The block hashed: block `k`, with `Y` added to block 0. -/
def inputA (s : State) (d k : Nat) : BitVec 128 :=
  dataA s d k ^^^ (if k = 0 then s.lane .xmm2 0 else 0)

private theorem xmm_setXmm (s : State) (d r : XReg) (v : BitVec 128) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

def inputs (s : State) (d k : Nat) : State :=
  (s.setV .l128 .xmm12 (powerA s k) 0).setV .l128 .xmm7 (inputA s d k) 0

def loadInputs (d k : Nat) : List Instr :=
  [.vmovdquLoad .l128 .xmm12 (at_ .r11 (16 * k)), .vmovdquLoad .l128 .xmm7 (at_ .rdx (d + 16 * k))] ++
    (if k = 0 then [.vop (.vbin .vpxor .l128 .xmm7 .xmm7 .xmm2)] else [])

theorem prefix_ok (s : State) (d k : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * k))) 16)
    (hx : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (d + 16 * k))) 16) :
    WP isa (.block (loadInputs d k)) s fun t => t = inputs s d k := by
  apply WP.of_runBlock
  by_cases hk : k = 0 <;>
    (try simp only [hk] at hp hx) <;>
    simp only [loadInputs, hk, ite_true, ite_false, List.append_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, hp, hx,
      State.setV_rd, State.setV_wr, State.setV_ea, State.setV_mem, Option.map_some,
      VOp.exec, reduceVBinOpSse, XBinOp.eval, State.lane, xmm_setV,
      reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left',
      inputs, inputA, dataA, powerA] <;>
    simp (config := { contextual := true }) [State.setV]

theorem inputs_frame (s : State) (d k : Nat) :
    YFrame [.xmm12, .xmm7] s (inputs s d k) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro r hr l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [inputs, State.lane, xmm_setV, ymmHi_setV_128, hr.1, hr.2, ite_false]

theorem ghA_eq (d k : Nat) :
    ghA d k = loadInputs d k ++ (if k = 1 then VG.Impl.Gcm.X86_64.StitchAvx8.accInit .xmm7 .xmm12
      else VG.Impl.Gcm.X86_64.StitchAvx8.acc .xmm7 .xmm12) := by
  simp only [ghA, loadInputs, List.append_assoc]

theorem ghA_ok (s : State) (d k : Nat)
    (hp : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * k))) 16)
    (hx : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (d + 16 * k))) 16) :
    WP isa (.block (ghA d k)) s fun t =>
      prod (t.proj 0) = (if k = 1 then Prod.zero else prod (s.proj 0)).acc
        (inputA s d k) (powerA s k) ∧ YFrame ghRegs s t := by
  rw [ghA_eq, WP.block_append_iff]
  refine WP.mono (prefix_ok s d k hp hx) fun t ht => ?_
  subst t
  have hf := inputs_frame s d k
  have finish : ∀ t, YFrame [.xmm8, .xmm9, .xmm10, .xmm11] (inputs s d k) t →
      YFrame ghRegs s t := fun t h => (hf.comp h).mono fun r hr => by
        simpa only [ghRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          or_assoc] using hr
  by_cases hk : k = 1
  · rw [ite_eq_left hk]
    refine WP.mono (accInit_ok (inputs s d k)) fun t ⟨hp, hfr⟩ => ⟨?_, finish t hfr⟩
    simpa only [inputs, State.lane, xmm_setV, reduceCtorEq, ite_true, ite_false, hk, ite_true] using hp
  · rw [ite_eq_right hk]
    refine WP.mono (acc_ok (inputs s d k)) fun t ⟨hp, hfr⟩ => ⟨?_, finish t hfr⟩
    simpa only [inputs, prod, State.proj_xmm, State.lane, xmm_setV, reduceCtorEq,
      ite_true, ite_false, hk, ite_false] using hp

/-! ## The reduction -/

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

private def redSse : List Instr :=
  [.movdquLoad .xmm12 (at_ .r11 polyO),
   .xop (.bin .movdqa .xmm11 .xmm8), .xop (.pclmulqdq .xmm11 .xmm12 0x10),
   .xop (.pshufd .xmm8 .xmm8 0x4e),
   .xop (.bin .pxor .xmm9 .xmm8), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa .xmm11 .xmm9), .xop (.pclmulqdq .xmm11 .xmm12 0x10),
   .xop (.pshufd .xmm9 .xmm9 0x4e),
   .xop (.bin .movdqa .xmm2 .xmm10), .xop (.bin .pxor .xmm2 .xmm9),
   .xop (.bin .pxor .xmm2 .xmm11)]

private theorem redSse_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 polyO)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 polyO)) 128 = poly) :
    WP isa (.block redSse) s fun s' =>
      s'.xmm .xmm2 = reduceB (prod s) ∧ Only [.xmm12, .xmm2, .xmm8, .xmm9, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [redSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, hin, Option.map_some, eval_pxor, eval_movdqa,
    xmm_setXmm, reduceCtorEq, ↓reduceIte, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceB, VG.Proof.Gcm.X86_64.Pclmul.fold, prod, BitVec.xor_assoc]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The registers `red` writes. -/
abbrev redRegs : List XReg := [.xmm12, .xmm2, .xmm8, .xmm9, .xmm11]

theorem red_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 polyO)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 polyO)) 128 = poly) :
    WP isa (.block red) s fun s' =>
      s'.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧ YFrame redRegs s s' := by
  refine liftPure _ redSse _ rfl rfl ?_ _ s (redSse_ok (s.proj 0) hin hc)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [red, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

/-! ## Eight blocks -/

/-- Block `k` of the eight from `rdx + d`, as it is. -/
def bufA (s : State) (d k : Nat) : Block := s.mem.readW (s.ea (at_ .rdx (d + 16 * k))) 128

/-- The power of block `k`. -/
def powA (s : State) (k : Nat) : Block := s.mem.readW (s.ea (at_ .r11 (16 * k))) 128

private theorem input_frame {s t : State} (f : YFrame ghRegs s t) (d k : Nat) :
    inputA t d k = hashInput (bufA s d) (s.lane .xmm2 0) k := by
  simp only [inputA, dataA, hashInput, bufA, f.mem, State.ea, f.gpr,
    f.lane .xmm2 (by decide) 0 (by decide)]

private theorem power_frame {s t : State} (f : YFrame ghRegs s t) (k : Nat) :
    powerA t k = powA s k := by
  simp only [powerA, powA, f.mem, State.ea, f.gpr]

/-- The first `n` loads of the order 1, …, 7, 0. -/
theorem hashSteps_ok (s : State) (d : Nat)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * k))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (d + 16 * k))) 16)
    (n : Nat) (hn : n ≤ 8) :
    WP isa (.block ((List.range n).flatMap fun i => ghA d ((i + 1) % 8))) s fun t =>
      prod (t.proj 0) = (if n = 0 then prod (s.proj 0) else
        accN (bufA s d) (powA s) (s.lane .xmm2 0) n) ∧ YFrame ghRegs s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, YFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨hacc, hf⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (ghA_ok t d ((n + 1) % 8) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hp _ (Nat.mod_lt _ (by decide))) (by
      rw [hf.rd, hf.wr]; simp only [State.ea, hf.gpr]; exact hx _ (Nat.mod_lt _ (by decide))))
      fun u ⟨ha, hu⟩ => ⟨?_, hf.trans hu⟩
    rw [ha, input_frame hf, power_frame hf]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, accN_succ]
    by_cases hz : n = 0
    · subst n
      simp only [Nat.zero_add, Nat.reduceMod, ite_true, accN, List.range_zero, List.foldl_nil]
    · have hm : (n + 1) % 8 ≠ 1 := by omega
      rw [ite_eq_right hm, hacc, ite_eq_right hz]

/-- Eight blocks absorbed, and reduced into `Y`. -/
theorem hash8_ok (s : State) (d : Nat)
    (hp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * k))) 16)
    (hx : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (d + 16 * k))) 16)
    (hc : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 polyO)) 16)
    (hv : s.mem.readW (s.ea (at_ .r11 polyO)) 128 = poly) :
    WP isa (.block (hash8 d)) s fun t =>
      t.lane .xmm2 0 = reduceB (accN (bufA s d) (powA s) (s.lane .xmm2 0) 8) ∧
      YFrame (ghRegs ++ redRegs) s t := by
  rw [hash8, WP.block_append_iff]
  refine WP.mono (hashSteps_ok s d hp hx 8 (by decide)) fun t ⟨ha, hf⟩ => ?_
  refine WP.mono (red_ok t (by
    simpa only [hf.rd, hf.wr, State.ea, hf.gpr] using hc) (by
    simpa only [hf.mem, State.ea, hf.gpr] using hv)) fun u ⟨hu, hfu⟩ => ⟨?_, hf.comp hfu⟩
  simpa only [ha, Nat.reduceEqDiff, ite_false] using hu

end

section

/-!
# AES-GCM-SIV's loops with AES-NI: a batch of eight blocks

Untrusted: everything here is checked by Lean. `batch_ok`: `batch j g`
deciphers the eight data blocks at `rdx + 16 j` (blocks `c … c + 7`,
`AInv`): the counter blocks from the counter block at `rax`, as they are,
into the eight block registers (`ctrs_ok`: the first 32-bit word,
little-endian, advanced by `vpaddd` of 1, `ctrX`), the counter block advanced
by eight, AES of each (`Vaes.aesGL_ok` for `VEX.128`), whose bytes are
`CIPH_K` of the counter blocks' (`Stitch.aesWith_le16`), and the XOR into the
data (`StitchAvx8.xorData_ok`, on bytes by `Stitch.bytes_of_blockAt`), as the
256-bit loop's batch does (`Proof.AesGcmSiv.X86_64.Stitch.batch_ok`). The
blocks `g i` between the rounds do what `Q` says.
-/

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs)
open VG.Impl.AesGcmSiv.X86_64StitchAvx (ctrsR ctrs batch oneO)
open VG.Proof.AesGcmSiv.X86_64.Stitch (SPre kp nr cp yp hp pp dp nb kR cR yR dR pR sch ciph icb bAddr blk ctb
  d₀ rest₀ ctrX₀ le16_ctrX aesWith_le16 bytes_of_blockAt)
open VG.Proof.Aes.X86_64.Vaes (aesGL_ok YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr)
open VG.Spec.Aes (bytesAt)

/-- 1 in the first 32-bit word. -/
abbrev one128 : BitVec 128 := (0 : BitVec 64) ++ BitVec.ofNat 64 1

/-! ## The counter blocks -/

theorem ctrX_one (icb : List Byte) (d : BitVec 128) (i : Nat) :
    XBinOp.eval .paddd (ctrX icb d i) one128 = ctrX icb d (i + 1) := by
  simp only [ctrX, paddd_one]
  rw [show Spec.GcmSiv.leNat (icb.take 4) + (i + 1) = Spec.GcmSiv.leNat (icb.take 4) + i + 1 by omega,
    BitVec.ofNat_add (Spec.GcmSiv.leNat (icb.take 4) + i) 1]

/-- One block register's counter block into `b`. -/
theorem ctr1_ok (c i b : XReg) (s : State) (icb : List Byte) (d : BitVec 128) (j : Nat) (hbc : b ≠ c)
    (hbi : b ≠ i) (hc : s.lane c 0 = ctrX icb d j) (ht : s.lane i 0 = one128) :
    WP isa (.block [.vop (.vmovdqa .l128 b c), .vop (.vbin .vpaddd .l128 c c i)]) s fun s' =>
      s'.lane b 0 = ctrX icb d j ∧ s'.lane c 0 = ctrX icb d (j + 1) ∧ YFrame [b, c] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc]; simp [VOp.exec, State.lane_setV128, Ne.symm hbc, hbc]
  · have e : ((VOp.vmovdqa .l128 b c).exec s).lane c 0 = s.lane c 0 ∧
        ((VOp.vmovdqa .l128 b c).exec s).lane i 0 = s.lane i 0 := by
      simp [VOp.exec, State.lane_setV128, Ne.symm hbc, Ne.symm hbi]
    simp only [lane_vbin128, ite_true, e.1, e.2, hc, ht, VBinOp.sse, ctrX_one]
  · refine ⟨by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [VOp.exec, State.lane_setV128, hr.1, hr.2]

theorem ctrsR_ok (c i : XReg) (hci : c ≠ i) (regs : List XReg) (s : State) (icb : List Byte) (d : BitVec 128)
    (j : Nat) (hnd : regs.Nodup) (hx : ∀ r ∈ regs, r ≠ c ∧ r ≠ i)
    (hc : s.lane c 0 = ctrX icb d j) (ht : s.lane i 0 = one128) :
    WP isa (.block (ctrsR c i regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.lane regs[k] 0 = ctrX icb d (j + k)) ∧
      s'.lane c 0 = ctrX icb d (j + regs.length) ∧ YFrame (c :: regs) s s' := by
  induction regs generalizing s j with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), by simpa using hc, YFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨hbc, hbi⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrsR, WP.block_append_iff]
    refine WP.mono (ctr1_ok c i b s icb d j hbc hbi hc ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (j + 1) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (by rw [f₁.lane _ (by simp [Ne.symm hbi, hci.symm]) 0 (by decide)]; exact ht))
      fun s' ⟨e, c', f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f.lane _ (by simp [hbc, hbs]) 0 (by decide), e₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · rw [c', List.length_cons, show j + 1 + bs.length = j + (bs.length + 1) by omega]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-- A 16-byte load into a register's lower lane (`VEX.128`). -/
theorem ld_ok (x : XReg) (b : Reg) (o : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (o : Int)) 16) :
    WP isa (.block [.vmovdquLoad .l128 x (VG.Impl.Gcm.X86_64.Pclmul.at_ b o)]) s fun s' =>
      s'.lane x 0 = s.mem.readW (s.gpr b + BitVec.ofInt 64 (o : Int)) 128 ∧ YFrame [x] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨s.setV .l128 x (s.mem.readW (s.gpr b + BitVec.ofInt 64 (o : Int)) 128) 0,
    by simp only [isa, exec, State.load128, ea_at, hin, ite_true, Option.map_some], WP.block_nil ⟨?_, ?_⟩⟩
  · simp [State.lane_setV128]
  · refine ⟨by simp, by simp, by simp, by simp, fun r hr l hl => ?_⟩
    have : r ≠ x := by simpa using hr
    simp [State.lane_setV128, this]

/-- A 16-byte store of a register's lower lane. -/
theorem st_ok (x : XReg) (b : Reg) (s : State) (hin : InRegions s.wr (s.gpr b) 16) :
    WP isa (.block [.vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ b 0) x]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr b) (s.lane x 0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  have hin' : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128_eq,
    ea_at, hin', ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp [State.lane], rfl, rfl, rfl, fun _ _ => rfl⟩

theorem aregs_ok : aregs.Nodup ∧ .xmm1 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm11 ∧ r ≠ .xmm12 := by decide

theorem aregs_length : aregs.length = 8 := rfl

/-- A batch's counter blocks, from the counter block at `rax`, which is
advanced by eight. -/
theorem ctrs_ok (s : State) (icb : List Byte) (d : BitVec 128) (c : Nat)
    (hin : InRegions s.wr (s.gpr .rax) 16)
    (hone : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 oneO) 16)
    (hc : s.mem.readW (s.gpr .rax) 128 = ctrX icb d c)
    (h1 : s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 oneO) 128 = one128) :
    WP isa (.block ctrs) s fun s' =>
      (∀ k (h : k < aregs.length), s'.lane aregs[k] 0 = ctrX icb d (c + k)) ∧
      s'.mem = s.mem.writeW (s.gpr .rax) (ctrX icb d (c + 8)) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ∉ aregs → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  obtain ⟨hnd, -, hx⟩ := aregs_ok
  have hin0 : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hin
  have hone' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((oneO : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hone
  show WP isa (.block ([.vmovdquLoad .l128 .xmm11 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rax 0)] ++
      ([.vmovdquLoad .l128 .xmm12 (VG.Impl.Gcm.X86_64.Pclmul.at_ .r11 oneO)] ++
      (ctrsR .xmm11 .xmm12 aregs ++ [.vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rax 0) .xmm11])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm11 .rax 0 s hin0) fun s₁ ⟨l₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm12 .r11 oneO s₁ (by rw [f₁.rd, f₁.wr, f₁.gpr]; exact hone'))
    fun s₂ ⟨l₂, f₂⟩ => ?_
  rw [WP.block_append_iff]
  have c₂ : s₂.lane .xmm11 0 = ctrX icb d c := by
    rw [f₂.lane _ (by decide) 0 (by decide), l₁, BitVec.ofInt_natCast, BitVec.add_zero, hc]
  have o₂ : s₂.lane .xmm12 0 = one128 := by
    rw [l₂, f₁.mem, f₁.gpr, BitVec.ofInt_natCast, h1]
  refine WP.mono (ctrsR_ok .xmm11 .xmm12 (by decide) aregs s₂ icb d c hnd hx c₂ o₂) fun s₃ ⟨e₃, c₃, f₃⟩ => ?_
  refine WP.mono (st_ok .xmm11 .rax s₃ (by rw [f₃.wr, f₂.wr, f₁.wr, f₃.gpr, f₂.gpr, f₁.gpr]; exact hin))
    fun s' ⟨m', g', rd', wr', l'⟩ => ⟨fun k hk => by rw [l']; exact e₃ k hk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m', f₃.mem, f₂.mem, f₁.mem, f₃.gpr, f₂.gpr, f₁.gpr, c₃, aregs_length]
  · rw [g', f₃.gpr, f₂.gpr, f₁.gpr]
  · rw [rd', f₃.rd, f₂.rd, f₁.rd]
  · rw [wr', f₃.wr, f₂.wr, f₁.wr]
  · intro r ha h11 h12 l hl
    rw [l', f₃.lane r (by simp [ha, h11]) l hl, f₂.lane r (by simp [h12]) l hl, f₁.lane r (by simp [h11]) l hl]

/-! ## A batch -/

/-- The decipherment after `c` blocks: the counter block at `rax`, the key
schedule and its last round key, the working space with 1 at `oneO`, and
the data (blocks below `c` deciphered, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  rax : s.gpr .rax = cp s₀
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r11 : s.gpr .r11 = pp s₀
  ctr : s.mem.readW (cp s₀) 128 = ctrX (icb s₀) (d₀ s₀) c
  one : s.mem.readW (pp s₀ + BitVec.ofNat 64 oneO) 128 = one128
  frame : Frame [cR s₀, dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀, bytesAt s.mem (bAddr s₀ k) 16 = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInv s₀ c s)
    (f : YFrame rs s s') : AInv s₀ c s' :=
  ⟨h.le, by rw [f.gpr]; exact h.rax, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r11, by rw [f.mem]; exact h.ctr,
    by rw [f.mem]; exact h.one, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-- The key schedule is not in the counter block, the data or the working
space. -/
theorem sch_frame {s₀ : State} (hp : SPre s₀) {m : Mem} (hf : Frame [cR s₀, dR s₀, pR s₀] s₀.mem m) :
    bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.c_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm1 ∧ r ∉ aregs)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm1 :: aregs) s s' → Q j s')
    (hqc : ∀ s s', Q 1 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [cR s₀] s.mem s'.mem → Q 1 s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 16 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm1 → r ≠ .xmm11 → r ≠ .xmm12 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [cR s₀, ⟨bAddr s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h1, hx⟩ := aregs_ok
  have hw := hp.wrap_d
  -- The counter blocks.
  refine WP.seq (WP.mono (ctrs_ok s (icb s₀) (d₀ s₀) c (by rw [hI.wr, hI.rax]; exact hp.c_in)
    (by rw [hI.rd, hI.wr, hI.r11]; exact in_rdwr (in_sub hp.p_in (by decide))) (by rw [hI.rax]; exact hI.ctr)
    (by rw [hI.r11]; exact hI.one)) fun s₁ ⟨e₁, m₁, g₁, rd₁, wr₁, l₁⟩ => ?_)
  rw [hI.rax] at m₁
  have fC : Frame [cR s₀] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have frame₁ : Frame [cR s₀, dR s₀, pR s₀] s₀.mem s₁.mem :=
    hI.frame.trans (fC.mono fun r hr => by simp at hr ⊢; simp [hr])
  have one₁ : s₁.mem.readW (pp s₀ + BitVec.ofNat 64 oneO) 128 = one128 := by
    rw [fC.readW (r := ⟨pp s₀ + BitVec.ofNat 64 oneO, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.p_c.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    exact hI.one
  have blocks₁ : ∀ k < nb s₀, bytesAt s₁.mem (bAddr s₀ k) 16 = if k < c then ctb s₀ k else blk s₀ k :=
    fun k hk => by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_c.sub_left (Offset.sub_base _ (by omega))) (by decide)]
      exact hI.blocks k hk
  have ctr₁ : s₁.mem.readW (cp s₀) 128 = ctrX (icb s₀) (d₀ s₀) (c + 8) := by
    rw [m₁]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ :=
    ⟨by rw [g₁, hI.rdi, sch_frame hp frame₁], by rcases hp.rounds with h | h | h <;> omega,
      fun j hj => by
        rw [rd₁, wr₁, hI.rd, hI.wr, g₁, hI.rdi]
        exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩
  have hQ₁ : Q 1 s₁ := hqc s s₁ hQ g₁ rd₁ wr₁ l₁ fC
  refine WP.seq (WP.mono (aesGL_ok .l128 .xmm1 aregs hnd h1 hp.rounds g G hG Q
    hg hq s₁ hK₁ hQ₁ (by rw [g₁, hI.rsi]; simp) (by rw [g₁, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), le16 (s₂.lane aregs[k] 0) =
      ciph s₀ (Spec.GcmSiv.counterBlock (icb s₀) (c + k)) := fun k h => by
    rw [← le16_ctrX (rest₀ s₀), ← e₁ k h]
    exact (aesWith_le16 _ _ _ _ (e₂ _ (List.getElem_mem h) 0 (by decide))).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (16 * j + 16 * i) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have addr' : ∀ k, s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k)) = bAddr s₀ (c + k) := fun k => by
    rw [show 16 * (j + k) = 16 * j + 16 * k by omega, addr]
  have din : ∀ k < 8, InRegions s₂.wr (bAddr s₀ (c + k)) 16 := fun k hk => by
    rw [f₂.wr, wr₁, hI.wr]; exact in_sub hp.d_in (by omega)
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchAvx8.xorData_ok false aregs j s₂ hnd (fun k hk => by
      rw [hrdx₂, BitVec.ofInt_natCast, addr']; exact din k (by simpa [aregs] using hk))
      (fun k hk => by
        rw [VG.Proof.Gcm.X86_64.StitchAvx8.srcAddr_false, hrdx₂, addr']
        exact in_rdwr (din k (by simpa [aregs] using hk)))
      (fun a b hab hb => by
        rw [VG.Proof.Gcm.X86_64.StitchAvx8.srcAddr_false, hrdx₂, addr', addr']
        exact Offset.disjoint _ (by omega) (by simp [aregs] at hb; omega) (by simp [aregs] at hb; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s₁.mem := f₂.mem
  simp only [VG.Proof.Gcm.X86_64.StitchAvx8.srcAddr_false, hm₂, hrdx₂, addr'] at b₃ fr₃
  rw [show s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c from addr_eq hrdx] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), bytesAt s₃.mem (bAddr s₀ (c + k)) 16 =
      Spec.Cmac.xor (bytesAt s₁.mem (bAddr s₀ (c + k)) 16) (le16 (s₂.lane aregs[k] 0)) :=
    fun k h => bytes_of_blockAt (b₃ k h)
  have fr' : Frame [⟨bAddr s₀ c, 128⟩] s₁.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm1 → r ≠ .xmm11 → r ≠ .xmm12 → r ∉ aregs → r ∉ G → ∀ l < 2,
      s₃.lane r l = s.lane r l := fun r h1' h11 h12 hr hg' l hl => by
    rw [x₃ r hr l hl, f₂.lane r (by simp [h1', hr, hg']) l hl, l₁ r hr h11 h12 l hl]
  have fD : ∀ k < nb s₀, ¬ (c ≤ k ∧ k < c + 8) →
      bytesAt s₃.mem (bAddr s₀ k) 16 = bytesAt s₁.mem (bAddr s₀ k) 16 := fun k hk hn =>
    Proof.AesGcm.X86_64.bytesAt_frame fr' (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro a h₁ h₂
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂) (by decide)
  have dC : Region.Disjoint ⟨cp s₀, 16⟩ ⟨bAddr s₀ c, 128⟩ :=
    hp.d_c.symm.sub_right (Offset.sub_base _ (by omega))
  have dP : Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 oneO, 16⟩ ⟨bAddr s₀ c, 128⟩ :=
    (hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))).sub_left (Offset.sub_base _ (by decide))
  refine ⟨⟨by omega, by rw [g₃, f₂.gpr, g₁]; exact hI.rax, by rw [g₃, f₂.gpr, g₁]; exact hI.rdi,
    by rw [g₃, f₂.gpr, g₁]; exact hI.rsi, by rw [g₃, f₂.gpr, g₁]; exact hI.r10, by rw [g₃, f₂.gpr, g₁]; exact hI.r11,
    ?_, ?_, ?_, ?_, by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h2 l hl => x₃ r h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, g₁], kx, ?_⟩
  · rw [fr'.readW (r := ⟨cp s₀, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dC) (by decide)]
    exact ctr₁
  · rw [fr'.readW (r := ⟨pp s₀ + BitVec.ofNat 64 oneO, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dP) (by decide)]
    exact one₁
  · -- The data written is only in the data.
    refine frame₁.trans (fr'.sub fun r hr => ⟨dR s₀, by simp, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [fD k hk (by omega), blocks₁ k hk]
      simp only [hlo, show k < c + 8 by omega, ite_true]
    · by_cases hhi : k < c + 8
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
        have hi : i < aregs.length := by simp [aregs]; omega
        rw [hb3 i hi, blocks₁ _ hk, ks i hi]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [fD k hk (by omega), blocks₁ k hk]
        simp only [hlo, hhi, ite_false]
  · exact (fC.mono fun r hr => by simp at hr ⊢; simp [hr]).trans (fr'.mono fun r hr => by simp at hr ⊢; simp [hr])

end

section

/-!
# AES-GCM-SIV's loops with AES-NI: the setup

Untrusted: everything here is checked by Lean. `setupG_ok`: `setupG`
computes `H'` … `H'⁸` (`x · H'ᵏ = Hᵏ`) from `H` at `r8`, as AES-GCM's
eight-state loop does from its hash subkey (`StitchAvx.setupGS_ok`, whose
tree of products `StitchAvx.tree_ok` this uses). `powers_ok`: with the
stores after it, `H'⁸⁻ᵏ` at `r11 + 16 k` and the reduction constant at
`r11 + polyO`. `setup_ok`: then 1 at `r11 + oneO`, `Y` and the pointers,
the state the interleaved loop starts from (`Ready`).
-/

open VG VG.X86_64 VG.X86_64.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (constImm_ok ldrev_ok hInvImm_ok Only rev_eq)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly revMask)
open VG.Impl.AesGcmSiv.X86_64StitchAvx (setupG stores storeOne loadY setupC setup preg oneO polyO)
open VG.Proof.Gcm.X86_64.StitchAvx (preg_ne tree_ok readW_slot_self readW_slot_sep slot_eq)
open VG.Proof.AesGcmSiv.X86_64.Stitch (SPre kp nr cp yp hp pp dp nb kR cR yR dR pR hk y₀ icb bAddr blk ctb d₀
  ctrX₀)
open VG.Proof.Gcm.X86_64.Stitch (in_sub in_sub_int in_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-! ## The powers -/

theorem setupG_ok (t : State) (hin : InRegions (t.rd ++ t.wr) (t.gpr .r8) 16) :
    WP isa (.block setupG) t fun t' =>
      t'.xmm .xmm0 = revMask ∧ t'.xmm .xmm1 = poly ∧
      (∀ i < 8, x * φ (t'.xmm (preg i)) = φ (blockAt t.mem (t.gpr .r8)) ^ (i + 1)) ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hin8 : InRegions (t.rd ++ t.wr) (t.gpr .r8 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r8 0 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin8)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInvImm_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
  have o₁₄ := (o₁₂.trans o₃).trans o₄
  rw [o₁₂.mem, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast, BitVec.add_zero] at l₃
  let H := φ (blockAt t.mem (t.gpr .r8))
  have hH : x * φ (t₄.xmm (preg 0)) = H := by rw [show preg 0 = .xmm3 from rfl, h₄, l₃]
  have p₄ : t₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  have m0 : t₄.xmm .xmm0 = revMask := by
    rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁]
  have step : ∀ {k a b : Nat} (hk8 : k < 8) (ha : a < k) (hb : b < k) (hab : a + b + 1 = k) {L : List Instr} {u : State}
      (h1 : u.xmm .xmm1 = poly) (h0 : u.xmm .xmm0 = revMask)
      (hI : ∀ i < k, x * φ (u.xmm (preg i)) = H ^ (i + 1))
      {Q : State → Prop}
      (hq : ∀ u', u'.xmm .xmm1 = poly → u'.xmm .xmm0 = revMask →
        (∀ i < k + 1, i < 8 → x * φ (u'.xmm (preg i)) = H ^ (i + 1)) →
        Only [.xmm8, .xmm9, .xmm10, .xmm11, preg k] u u' → WP isa (.block L) u' Q),
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul (preg k) (preg a) (preg b) ++ L)) u Q := by
    intro k a b hk8 ha hb hab L u h1 h0 hI Q hq
    rw [WP.block_append_iff]
    refine WP.mono (tree_ok k a b hk8 ha hb hab u h1 hI) fun u' ⟨h1', hI', o'⟩ => hq u' h1' ?_ hI' o'
    rw [o'.xmm _ (by obtain ⟨-, -, -, -, -, h, -⟩ := preg_ne k; simp [Ne.symm h])]; exact h0
  have f₀ : ∀ i < 1, x * φ (t₄.xmm (preg i)) = H ^ (i + 1) := fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [hH, pow_one]
  refine step (k := 1) (a := 0) (b := 0) (by decide) (by decide) (by decide) rfl p₄ m0 f₀ fun t₅ p₅ m₅ f₅ o₅ => ?_
  refine step (k := 2) (a := 1) (b := 0) (by decide) (by decide) (by decide) rfl p₅ m₅ (fun i hi => f₅ i hi (by omega))
    fun t₆ p₆ m₆ f₆ o₆ => ?_
  refine step (k := 3) (a := 1) (b := 1) (by decide) (by decide) (by decide) rfl p₆ m₆ (fun i hi => f₆ i hi (by omega))
    fun t₇ p₇ m₇ f₇ o₇ => ?_
  refine step (k := 4) (a := 3) (b := 0) (by decide) (by decide) (by decide) rfl p₇ m₇ (fun i hi => f₇ i hi (by omega))
    fun t₈ p₈ m₈ f₈ o₈ => ?_
  refine step (k := 5) (a := 3) (b := 1) (by decide) (by decide) (by decide) rfl p₈ m₈ (fun i hi => f₈ i hi (by omega))
    fun t₉ p₉ m₉ f₉ o₉ => ?_
  refine step (k := 6) (a := 3) (b := 2) (by decide) (by decide) (by decide) rfl p₉ m₉ (fun i hi => f₉ i hi (by omega))
    fun t₁₀ p₁₀ m₁₀ f₁₀ o₁₀ => ?_
  rw [← List.append_nil (Impl.Gcm.X86_64.Pclmul.mul (preg 7) (preg 3) (preg 3))]
  refine step (k := 7) (a := 3) (b := 3) (by decide) (by decide) (by decide) rfl p₁₀ m₁₀ (fun i hi => f₁₀ i hi (by omega))
    fun t' p' m' f' o' => WP.block_nil ?_
  have o := o₁₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans o'))))))
  exact ⟨m', p', fun i hi => f' i (by omega) hi, o.gpr, o.mem, o.rd, o.wr⟩

/-! ## The stores -/

/-- The first `n` stores of the powers. -/
def powStores (n : Nat) : List Instr :=
  (List.range n).map fun k => .movdquStore (at_ .r11 (16 * k)) (preg (7 - k))

theorem powStores_ok (t : State) (hr : ∀ k < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (t.gpr .r11).toNat + 256 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block (powStores n)) t fun t' =>
      (∀ j < n, t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * j)) 128 = t.xmm (preg (7 - j))) ∧
      (∀ k < 16, n ≤ k → t'.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128 =
        t.mem.readW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) 128) ∧
      Frame [⟨t.gpr .r11, 256⟩] t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ t'.ymmHi = t.ymmHi ∧
      t'.rd = t.rd ∧ t'.wr = t.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [powStores, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (powStores_ok t hr hp n (by omega)) fun t₁ ⟨v₁, k₁, f₁, g₁, x₁, y₁, rd₁, wr₁⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    rw [WP.block_cons_iff]
    have hin : InRegions t₁.wr (t₁.gpr .r11 + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
      rw [g₁, wr₁]; exact hr _ (by omega)
    refine ⟨{ t₁ with mem := t₁.mem.writeW (t₁.gpr .r11 + BitVec.ofInt 64 ((16 * n : Nat) : Int)) (t₁.xmm (preg (7 - n))) },
      by simp only [isa, exec, State.store128, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ite_true], WP.block_nil ?_⟩
    simp only [slot_eq]
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, g₁, x₁, y₁, rd₁, wr₁⟩
    · rw [g₁, x₁]
      by_cases hjn : j = n
      · subst hjn; exact readW_slot_self
      · rw [readW_slot_sep (by omega) (by omega) (by omega)]; exact v₁ j (by omega)
    · rw [g₁, readW_slot_sep hk (by omega) (by omega)]; exact k₁ k hk (by omega)
    · rw [g₁]; exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- A 16-byte SSE store to `[r11 + 16 k]`. -/
theorem slotStore_ok (r : XReg) (k : Nat) (t : State)
    (hin : InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .r11 (16 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .r11 + BitVec.ofNat 64 (16 * k)) (t.xmm r) ∧ t'.gpr = t.gpr ∧
      t'.xmm = t.xmm ∧ t'.ymmHi = t.ymmHi ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (t.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) (t.xmm r) },
    by simp only [isa, exec, State.store128, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ite_true],
    WP.block_nil ⟨by simp only [slot_eq], rfl, rfl, rfl, rfl, rfl⟩⟩

/-- What the powers' setup leaves: the mask, the reduction constant, and in
the working space at `p`, `H'⁸⁻ᵏ` at slot `k` and the reduction constant at
slot 9; nothing else written. -/
structure PowPost (s : State) (p : Addr) (t : State) : Prop where
  m0 : t.xmm .xmm0 = revMask
  pw : ∀ k < 8, x * φ (t.mem.readW (p + BitVec.ofNat 64 (16 * k)) 128) = φ (blockAt s.mem (s.gpr .r8)) ^ (8 - k)
  pc : t.mem.readW (p + BitVec.ofNat 64 polyO) 128 = poly
  frame : Frame [⟨p, 256⟩] s.mem t.mem
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem powers_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r8) 16)
    (hr : ∀ k < 16, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hp : (s.gpr .r11).toNat + 256 ≤ 2 ^ 64) :
    WP isa (.block (setupG ++ stores)) s (PowPost s (s.gpr .r11)) := by
  rw [WP.block_append_iff]
  refine WP.mono (setupG_ok s hin) fun t₁ ⟨m0, p1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  have hr11 : t₁.gpr .r11 = s.gpr .r11 := g₁ _ (by decide)
  rw [stores, show (List.range 8).map (fun k => Instr.movdquStore (at_ .r11 (16 * k)) (preg (7 - k))) =
    powStores 8 from rfl, WP.block_append_iff]
  refine WP.mono (powStores_ok t₁ (fun k hk => by rw [wr₁, hr11]; exact hr k hk) (by rw [hr11]; exact hp) 8
    (Nat.le_refl _)) fun t₂ ⟨v₂, k₂, f₂, g₂, x₂, y₂, rd₂, wr₂⟩ => ?_
  rw [show polyO = 16 * 9 from rfl]
  refine WP.mono (slotStore_ok .xmm1 9 t₂ (by rw [wr₂, g₂, wr₁, hr11]; exact hr 9 (by decide)))
    fun t' ⟨m', g', x', y', rd', wr'⟩ => ⟨?_, fun k hk => ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [x', x₂]; exact m0
  · rw [m', g₂, hr11, readW_slot_sep (by omega) (by decide) (by omega), ← hr11, v₂ k hk, pw _ (by omega),
      ← m₁, ← g₁ _ (by decide)]
    congr 1; omega
  · rw [m', g₂, hr11, show (polyO : Nat) = 16 * 9 from rfl, readW_slot_self, x₂, p1]
  · rw [m', g₂, hr11, ← m₁]
    exact (by rw [← hr11]; exact f₂ : Frame [⟨s.gpr .r11, 256⟩] t₁.mem t₂.mem).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
  · rw [g', g₂, g₁ r hr]
  · rw [rd', rd₂, rd₁]
  · rw [wr', wr₂, wr₁]

/-! ## The rest of the setup -/

theorem storeOne_ok (t : State) (hin : InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((oneO : Nat) : Int)) 16) :
    WP isa (.block storeOne) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .r11 + BitVec.ofNat 64 oneO) one128 ∧
      (∀ r, r ≠ .r10 → t'.gpr r = t.gpr r) ∧ (∀ r, r ≠ .xmm11 → t'.xmm r = t.xmm r) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hin' : InRegions t.wr (t.gpr .r11 + BitVec.ofInt 64 ((oneO : Nat) : Int)) 16 := hin
  apply WP.of_runBlock
  simp only [storeOne, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, readSrc32, Option.map_some,
    State.setReg32, State.store128, VG.Proof.Gcm.X86_64.Pclmul.ea_at, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
    gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, ↓reduceIte, reduceCtorEq,
    hin', Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp [hr], fun r hr => ?_, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast]
    exact congrArg _ (show ((0 : BitVec 64) ++ BitVec.setWidth 64 (1 : BitVec 32)) = one128 by decide)
  · show (if r = .xmm11 then _ else _) = _
    simp [hr, State.setReg]

theorem setupC_ok (t : State) :
    WP isa (.block setupC) t fun t' =>
      t'.gpr .r10 = t.gpr .rdi + BitVec.ofNat 64 (16 * (t.gpr .rsi).toNat) ∧ t'.gpr .rax = t.gpr .rdx ∧
      t'.gpr .rdx = t.gpr .r12 ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide, and_self, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, fun r h1 h2 h3 => ?_, trivial⟩
  · bv_omega
  · simp [h1, h2, h3]

/-! ## The whole setup -/

/-- What the interleaved loop starts from: nothing deciphered, the powers
`P` and the reduction constant in the working space, `Y` in `xmm2`, `rdx`
at the data. -/
structure Ready (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  pc : s.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly
  y : s.lane .xmm2 0 = y₀ s₀

/-- The working space's slots are writable. -/
theorem slots_in {s₀ : State} (hp : SPre s₀) :
    ∀ k < 16, InRegions s₀.wr (s₀.gpr .r11 + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16 :=
  fun _ hk => in_sub_int hp.p_in (by omega)

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, x * φ (P k) = φ (hk s₀) ^ (8 - k) := by
  have hwp := hp.wrap_p
  rw [setup, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (powers_ok s₀ hp.h_in (slots_in hp) hwp) fun s₁ P₁ => ?_
  have hr11 : s₁.gpr .r11 = pp s₀ := P₁.gpr _ (by decide)
  refine WP.mono (storeOne_ok s₁ (by rw [P₁.wr, hr11]; exact in_sub_int hp.p_in (by decide)))
    fun s₂ ⟨m₂, g₂, x₂, rd₂, wr₂⟩ => ?_
  have hrcx : s₂.gpr .rcx = yp s₀ := by rw [g₂ _ (by decide), P₁.gpr _ (by decide)]
  have h0₂ : s₂.xmm .xmm0 = revMask := by rw [x₂ _ (by decide), P₁.m0, rev_eq]
  refine WP.mono (ldrev_ok .xmm2 .rcx 0 s₂ (by decide) h0₂ (by
      rw [rd₂, wr₂, P₁.rd, P₁.wr, hrcx, BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hp.y_in))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  refine WP.mono (setupC_ok s₃) fun s' ⟨r10', rax', rdx', gk', m', x', rd', wr'⟩ => ?_
  -- The registers.
  have g₃ : ∀ r, r ≠ .rax → r ≠ .r10 → s₃.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [o₃.gpr r h1, g₂ r h2, P₁.gpr r h1]
  -- Memory: only the working space is written.
  rw [hr11] at m₂
  have m₃ : s₃.mem = s₁.mem.writeW (pp s₀ + BitVec.ofNat 64 oneO) one128 := by rw [o₃.mem, m₂]
  have fP₁ : Frame [pR s₀] s₀.mem s₁.mem := P₁.frame
  have fP : Frame [pR s₀] s₀.mem s'.mem := by
    rw [m', m₃]
    exact fP₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have keepOut : ∀ {a : Addr}, Region.Disjoint ⟨a, 16⟩ (pR s₀) → s'.mem.readW a 128 = s₀.mem.readW a 128 :=
    fun hd => fP.readW (r := ⟨_, 16⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
  have slot : ∀ k < 16, k ≠ 8 → s'.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 =
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 := fun k hk h8 => by
    rw [m', m₃, show (oneO : Nat) = 16 * 8 from rfl, readW_slot_sep hk (by decide) h8]
  have hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [gk' r h1 h2 h3, g₃ r h1 h3]
  have hA : AInv s₀ 0 s' :=
    { le := Nat.zero_le _
      rax := by rw [rax', g₃ _ (by decide) (by decide)]
      rdi := hg _ (by decide) (by decide) (by decide)
      rsi := hg _ (by decide) (by decide) (by decide)
      r10 := by rw [r10', g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide)]
      r11 := hg _ (by decide) (by decide) (by decide)
      ctr := by rw [keepOut hp.p_c.symm, ctrX₀]
      one := by rw [m', m₃]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
      frame := fP.mono fun r hr => by simp at hr ⊢; simp [hr]
      blocks := fun k hk => by
        rw [Proof.AesGcm.X86_64.bytesAt_frame fP (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.d_p.sub_left (Offset.sub_base _ (by omega))) (by decide)]
        simp only [Nat.not_lt_zero, ite_false]
      rd := by rw [rd', o₃.rd, rd₂, P₁.rd]
      wr := by rw [wr', o₃.wr, wr₂, P₁.wr] }
  have hy : s'.lane .xmm2 0 = y₀ s₀ := by
    show s'.xmm .xmm2 = _
    rw [x', l₃, hrcx, BitVec.ofInt_natCast, BitVec.add_zero, m₂,
      VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (R := ⟨pp s₀ + BitVec.ofNat 64 oneO, 16⟩)
        (hp.p_y.symm.sub_right (Offset.sub_base _ (by decide))) rfl]
    exact Proof.AesGcm.X86_64.blockAt_frame fP₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.p_y.symm
  have hpc : s'.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly := by
    rw [show (polyO : Nat) = 16 * 9 from rfl, slot 9 (by decide) (by decide)]; exact P₁.pc
  have hpw : ∀ k < 8, x * φ (s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128) = φ (hk s₀) ^ (8 - k) :=
    P₁.pw
  have hrdx : s'.gpr .rdx = dp s₀ := by rw [rdx', g₃ _ (by decide) (by decide)]
  exact ⟨fun k => s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128,
    ⟨hA, hrdx, hg, fun k hk => slot k (by omega) (by omega), hpc, hy⟩, hpw⟩

end

section

/-!
# AES-GCM-SIV's loops with AES-NI: the interleaved loop

Untrusted: everything here is checked by Lean. `q_ok`: the POLYVAL work
between the rounds of a batch (`q d`) absorbs the eight blocks at `rdx + d`
into `Y` (`QH`), its loads after rounds 1 to 8 (`ghA_ok`) and its
reduction after round 9 (`red_ok`), which `StitchAvx8.finishHash` makes
eight steps of GHASH. `EInv s₀ P e s`: `e` groups of sixteen blocks are
deciphered (`AInv`), the plaintext of the first `e - 1` absorbed into `Y`;
`rdx` points to group `e - 1`, the next to hash. `body_ok`: a body deciphers
group `e` (two batches, `batch_ok`) while it hashes group `e - 1`, half in
each batch, which they do not write (`HEnv.keep`). `dec_ok`: the setup
(`setup_ok`), the first group, the loop and the last group's hashing meet
the contract of the 256-bit loop (`Stitch.DPost`).
-/

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt ofNat_sub_ofNat ea_at constImm_ok rev_eq)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly revMask)
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs)
open VG.Impl.AesGcmSiv.X86_64StitchAvx (ghA red q hash8 batch first body lastG storeY dec polyO)
open VG.Proof.Gcm.X86_64.StitchAvx8 (accN accN_succ hashInput ghRegs finishHash ghash_append8)
open VG.Proof.AesGcmSiv.X86_64.Stitch (SPre DPost kp nr cp yp hp pp dp nb kR cR yR dR pR sch ciph icb bAddr blk
  ctb hk y₀ d₀ rest₀ le16_ctrX readW_ofBytes)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr store16_ok nextE_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## The POLYVAL work of a batch -/

/-- What the POLYVAL loads of eight blocks at `rdx + d` need: the blocks
`X` there, as they are, the powers `P` and the reduction constant in the
working space. -/
structure HEnv (a p : Addr) (d : Nat) (X P : Nat → Block) (s : State) : Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = p
  xs : ∀ k < 8, bufA s d k = X k
  pv : ∀ k < 8, powA s k = P k
  ina : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (d + 16 * k))) 16
  inp : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 (16 * k))) 16
  inc : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 polyO)) 16
  pc : s.mem.readW (s.ea (at_ .r11 polyO)) 128 = poly

theorem HEnv.yframe {a p : Addr} {d : Nat} {X P : Nat → Block} {s s' : State} {rs : List XReg}
    (h : HEnv a p d X P s) (f : YFrame rs s s') : HEnv a p d X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun k hk => by simp only [bufA, State.ea, f.gpr, f.mem]; exact h.xs k hk,
    fun k hk => by simp only [powA, State.ea, f.gpr, f.mem]; exact h.pv k hk,
    fun k hk => by simp only [State.ea, f.gpr, f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by simp only [State.ea, f.gpr, f.rd, f.wr]; exact h.inp k hk,
    by simp only [State.ea, f.gpr, f.rd, f.wr]; exact h.inc,
    by simp only [State.ea, f.gpr, f.mem]; exact h.pc⟩

/-- What holds before the POLYVAL work after round `j` of a batch: the
first `j - 1` loads done, `Y` in `xmm2`; after the reduction, `Y` the
eight blocks absorbed. -/
def QH (a p : Addr) (d : Nat) (X P : Nat → Block) (y : Block) (j : Nat) (s : State) : Prop :=
  HEnv a p d X P s ∧
  (if j ≤ 9 then (2 ≤ j → prod (s.proj 0) = accN X P y (j - 1)) ∧ s.lane .xmm2 0 = y
   else s.lane .xmm2 0 = reduceB (accN X P y 8))

/-- The registers the POLYVAL work writes. -/
abbrev gRegsA : List XReg := ghRegs ++ redRegs

theorem gRegsA_ok : ∀ r ∈ gRegsA, r ≠ .xmm1 ∧ r ∉ aregs := by decide

theorem QH.yframe {a p : Addr} {d : Nat} {X P : Nat → Block} {y : Block} {j : Nat} {s s' : State}
    (h : QH a p d X P y j s) (f : YFrame (.xmm1 :: aregs) s s') : QH a p d X P y j s' := by
  obtain ⟨hE, h2⟩ := h
  have kp : prod (s'.proj 0) = prod (s.proj 0) := by
    simp only [prod, State.proj_xmm, f.lane .xmm8 (by decide) 0 (by decide), f.lane .xmm9 (by decide) 0 (by decide),
      f.lane .xmm10 (by decide) 0 (by decide)]
  have k2 : s'.lane .xmm2 0 = s.lane .xmm2 0 := f.lane .xmm2 (by decide) 0 (by decide)
  refine ⟨hE.yframe f, ?_⟩
  split
  · rw [ite_eq_left (by assumption)] at h2
    exact ⟨fun hj => by rw [kp]; exact h2.1 hj, by rw [k2]; exact h2.2⟩
  · rw [ite_eq_right (by assumption)] at h2
    rw [k2]; exact h2

theorem q_ok {a p : Addr} {d : Nat} {X P : Nat → Block} {y : Block} {K : State → Prop} :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, K s → QH a p d X P y j s →
      WP isa (.block (q d j)) s fun s' => QH a p d X P y (j + 1) s' ∧ YFrame gRegsA s s' := by
  intro j hj1 hj9 s _ ⟨hE, h2⟩
  rw [ite_eq_left hj9] at h2
  by_cases h8 : j ≤ 8
  · -- A load.
    have hk : j % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [q, show 1 ≤ j ∧ j ≤ 8 from ⟨hj1, h8⟩, and_self, ite_true]
    refine WP.mono (ghA_ok s d (j % 8) (hE.inp _ hk) (hE.ina _ hk)) fun s' ⟨p', f'⟩ =>
      ⟨⟨hE.yframe f', ?_⟩, f'.mono fun r hr => List.mem_append_left _ hr⟩
    rw [ite_eq_left (by omega)]
    refine ⟨fun _ => ?_, by rw [f'.lane _ (by decide) 0 (by decide)]; exact h2.2⟩
    have hin : inputA s d (j % 8) = hashInput X y (j % 8) := by
      simp only [inputA, dataA, hashInput]
      rw [show s.mem.readW (s.ea (at_ .rdx (d + 16 * (j % 8)))) 128 = bufA s d (j % 8) from rfl, hE.xs _ hk, h2.2]
    have hpw : powerA s (j % 8) = P (j % 8) := hE.pv _ hk
    rw [p', hin, hpw]
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [show n + 1 + 1 - 1 = n + 1 by omega, accN_succ]
    by_cases h0 : n = 0
    · subst h0; rfl
    · rw [ite_eq_right (by omega), h2.1 (by omega), show n + 1 - 1 = n by omega]
  · -- The reduction.
    obtain rfl : j = 9 := by omega
    simp only [q, show ¬ (1 ≤ 9 ∧ 9 ≤ 8) by decide, ite_false, ite_true]
    refine WP.mono (red_ok s hE.inc hE.pc) fun s' ⟨y', f'⟩ =>
      ⟨⟨hE.yframe f', ?_⟩, f'.mono fun r hr => List.mem_append_right _ hr⟩
    rw [ite_eq_right (by decide), y', h2.1 (by decide)]

/-- `QH`, kept by code that writes neither the blocks nor the working space. -/
theorem HEnv.keep {s₀ : State} (hp : SPre s₀) {a : Addr} {g h : Nat} {X P : Nat → Block} {s s' : State}
    {rs : List Region} (hE : HEnv a (pp s₀) (128 * h) X P s) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hgpr : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨bAddr s₀ (16 * g + 8 * h), 128⟩ r ∧ (pR s₀).Disjoint r) :
    HEnv a (pp s₀) (128 * h) X P s' := by
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * g := by rw [hE.rdx]; exact ha
  have hr11 : s.gpr .r11 = pp s₀ := hE.r11
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have rd16 : ∀ {a : Addr} (R : Region), Region.Sub ⟨a, 16⟩ R → (∀ r ∈ rs, R.Disjoint r) →
      s'.mem.readW a 128 = s.mem.readW a 128 := fun R hs hR => by
    rw [readW_ofBytes, readW_ofBytes, Proof.AesGcm.X86_64.bytesAt_frame hf
      (fun r hr => (hR r hr).sub_left hs) (by decide)]
  have eaD : ∀ k, s.ea (at_ .rdx (128 * h + 16 * k)) = bAddr s₀ (16 * g + 8 * h + k) := fun k => by
    rw [ea_at, BitVec.ofInt_natCast]; exact addr_eq (by omega)
  have eaP : ∀ o, s.ea (at_ .r11 o) = pp s₀ + BitVec.ofNat 64 o := fun o => by
    rw [ea_at, BitVec.ofInt_natCast, hr11]
  have e' : ∀ m, s'.ea m = s.ea m := fun m => by simp only [State.ea, hgpr]
  refine ⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun k hk => ?_, fun k hk => ?_,
    fun k hk => by rw [e', hrd, hwr]; exact hE.ina k hk,
    fun k hk => by rw [e', hrd, hwr]; exact hE.inp k hk, by rw [e', hrd, hwr]; exact hE.inc, ?_⟩
  · have hx := hE.xs k hk
    rw [show bufA s (128 * h) k = s.mem.readW (s.ea (at_ .rdx (128 * h + 16 * k))) 128 from rfl, eaD] at hx
    rw [show bufA s' (128 * h) k = s'.mem.readW (s'.ea (at_ .rdx (128 * h + 16 * k))) 128 from rfl, e', eaD,
      rd16 ⟨bAddr s₀ (16 * g + 8 * h), 128⟩ (Offset.sub _ (by omega) (by omega)) (fun r hr => (hd r hr).1)]
    exact hx
  · have hx := hE.pv k hk
    rw [show powA s k = s.mem.readW (s.ea (at_ .r11 (16 * k))) 128 from rfl, eaP] at hx
    rw [show powA s' k = s'.mem.readW (s'.ea (at_ .r11 (16 * k))) 128 from rfl, e', eaP,
      rd16 (pR s₀) (Offset.sub_base _ (by omega)) (fun r hr => (hd r hr).2)]
    exact hx
  · have hx := hE.pc
    rw [eaP] at hx
    rw [e', eaP, rd16 (pR s₀) (Offset.sub_base _ (by decide)) (fun r hr => (hd r hr).2)]
    exact hx

/-! ## The loop -/

structure EInv (s₀ : State) (P : Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  pc : s.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map fun k => Spec.GcmSiv.ofBytes (ctb s₀ k))

/-- The powers' law: eight blocks hashed with `P` are eight steps of GHASH. -/
def Law (s₀ : State) (P : Nat → Block) : Prop :=
  ∀ X y, reduceB (accN X P y 8) = ghashFrom (hk s₀) y ((List.range 8).map X)

/-- The POLYVAL loads' environment for half `h` of group `g`, from what
the loop keeps. -/
theorem henv_of {s₀ : State} (hp : SPre s₀) {P : Nat → Block} {g h c : Nat} {s : State}
    (hI : AInv s₀ c s) (hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * g)
    (hpw : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k)
    (hpc : s.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly) (hg : 16 * g + 8 * h + 8 ≤ c) :
    HEnv (s.gpr .rdx) (pp s₀) (128 * h) (fun k => Spec.GcmSiv.ofBytes (ctb s₀ (16 * g + 8 * h + k))) P s := by
  have hw := hp.wrap_d
  have hc := hI.le
  have eaD : ∀ k, s.ea (at_ .rdx (128 * h + 16 * k)) = bAddr s₀ (16 * g + 8 * h + k) := fun k => by
    rw [ea_at, BitVec.ofInt_natCast]; exact addr_eq (by omega)
  have eaP : ∀ o, s.ea (at_ .r11 o) = pp s₀ + BitVec.ofNat 64 o := fun o => by
    rw [ea_at, BitVec.ofInt_natCast, hI.r11]
  refine ⟨rfl, hI.r11, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [show bufA s (128 * h) k = s.mem.readW (s.ea (at_ .rdx (128 * h + 16 * k))) 128 from rfl, eaD,
      readW_ofBytes, hI.blocks _ (by omega), ite_eq_left (by omega)]
  · rw [show powA s k = s.mem.readW (s.ea (at_ .r11 (16 * k))) 128 from rfl, eaP]; exact hpw k hk
  · rw [eaD, hI.rd, hI.wr]; exact in_rdwr (in_sub hp.d_in (by omega))
  · rw [eaP, hI.rd, hI.wr]; exact in_rdwr (in_sub hp.p_in (by omega))
  · rw [eaP, hI.rd, hI.wr]; exact in_rdwr (in_sub hp.p_in (by decide))
  · rw [eaP]; exact hpc

/-- The batches' frames are apart from the group hashed and the working
space. -/
theorem frames_apart {s₀ : State} (hp : SPre s₀) {g h c : Nat} (hgc : 16 * g + 8 * h + 8 ≤ c)
    (hc : c + 8 ≤ nb s₀) :
    ∀ r ∈ [cR s₀, (⟨bAddr s₀ c, 128⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ (16 * g + 8 * h), 128⟩ r ∧ (pR s₀).Disjoint r := by
  have hw := hp.wrap_d
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨hp.d_c.sub_left (Offset.sub_base _ (by omega)), hp.p_c⟩
  · exact ⟨Offset.disjoint _ (by omega) (by omega) (by omega), hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))⟩

theorem QH.one_iff {a p : Addr} {d : Nat} {X P : Nat → Block} {y : Block} {s : State} :
    QH a p d X P y 1 s ↔ HEnv a p d X P s ∧ s.lane .xmm2 0 = y := by
  simp only [QH, show (1 : Nat) ≤ 9 by decide, ↓reduceIte, show ¬ (2 : Nat) ≤ 1 by decide, false_imp_iff,
    true_and]

theorem QH.ten_iff {a p : Addr} {d : Nat} {X P : Nat → Block} {y : Block} {s : State} :
    QH a p d X P y 10 s ↔ HEnv a p d X P s ∧ s.lane .xmm2 0 = reduceB (accN X P y 8) := by
  simp only [QH, show ¬ (10 : Nat) ≤ 9 by decide, ↓reduceIte]

/-- The working space, kept by a batch's frames. -/
theorem pw_keep {s₀ : State} (hp : SPre s₀) {c : Nat} {m m' : Mem}
    (hf : Frame [cR s₀, ⟨bAddr s₀ c, 128⟩] m m') (hc : c + 8 ≤ nb s₀) {o : Nat} (ho : o + 16 ≤ 256) :
    m'.readW (pp s₀ + BitVec.ofNat 64 o) 128 = m.readW (pp s₀ + BitVec.ofNat 64 o) 128 := by
  rw [readW_ofBytes, readW_ofBytes, Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => ?_) (by decide)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.p_c.sub_left (Offset.sub_base _ (by omega))
  · exact (hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))).sub_left (Offset.sub_base _ (by omega))

/-- `AInv`, kept by code that writes nothing it reads. -/
theorem AInv.keepG {s₀ : State} {c : Nat} {s s' : State} (h : AInv s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : AInv s₀ c s' :=
  ⟨h.le, by rw [hg _ (by decide) (by decide)]; exact h.rax, by rw [hg _ (by decide) (by decide)]; exact h.rdi,
    by rw [hg _ (by decide) (by decide)]; exact h.rsi, by rw [hg _ (by decide) (by decide)]; exact h.r10,
    by rw [hg _ (by decide) (by decide)]; exact h.r11, by rw [hm]; exact h.ctr, by rw [hm]; exact h.one,
    by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.blocks k hk, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr⟩

/-- The keeping obligations of `batch_ok`, for the POLYVAL work of half `h`
of group `g`, at `a`. -/
theorem keepC {s₀ : State} (hp : SPre s₀) {a : Addr} {g h c : Nat} {X P : Nat → Block} {y : Block}
    (ha : a.toNat = (dp s₀).toNat + 256 * g) (hgc : 16 * g + 8 * h + 8 ≤ c) (hc : c + 8 ≤ nb s₀) :
    ∀ s s', QH a (pp s₀) (128 * h) X P y 1 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → r ≠ .xmm11 → r ≠ .xmm12 → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [cR s₀] s.mem s'.mem → QH a (pp s₀) (128 * h) X P y 1 s' := by
  intro s s' hq hg hrd hwr hl hf
  rw [QH.one_iff] at hq ⊢
  refine ⟨hq.1.keep hp ha hg hrd hwr hf fun r hr => frames_apart hp hgc hc r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact .inl hr), ?_⟩
  rw [hl _ (by decide) (by decide) (by decide) 0 (by decide)]; exact hq.2

theorem keepX {s₀ : State} (hp : SPre s₀) {a : Addr} {g h c : Nat} {X P : Nat → Block} {y : Block}
    (ha : a.toNat = (dp s₀).toNat + 256 * g) (hgc : 16 * g + 8 * h + 8 ≤ c) (hc : c + 8 ≤ nb s₀) :
    ∀ s s', QH a (pp s₀) (128 * h) X P y 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem → QH a (pp s₀) (128 * h) X P y 10 s' := by
  intro s s' hq hg hrd hwr hl hf
  rw [QH.ten_iff] at hq ⊢
  refine ⟨hq.1.keep hp ha hg hrd hwr hf fun r hr => frames_apart hp hgc hc r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact .inr hr), ?_⟩
  rw [hl _ (by decide) 0 (by decide)]; exact hq.2

/-- Two halves of a group after the groups before it. -/
theorem ghash3 (H y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom H (ghashFrom H (ghashFrom H y ((List.range g).map f))
      ((List.range 8).map fun k => f (g + 8 * 0 + k))) ((List.range 8).map fun k => f (g + 8 * 1 + k)) =
    ghashFrom H y ((List.range (g + 8 + 8)).map f) := by
  conv_rhs => rw [ghash_append8 H y f (g + 8), ghash_append8 H y f g]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc]

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : Law s₀ P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  let f : Nat → Block := fun k => Spec.GcmSiv.ofBytes (ctb s₀ k)
  have hE₀ := henv_of (h := 0) hp hI.a hrdx hI.pw hI.pc (by omega)
  -- The first batch, with the first half of the previous group.
  refine WP.seq (WP.mono (batch_ok hp (q (128 * 0)) gRegsA gRegsA_ok
    (QH (s.gpr .rdx) (pp s₀) (128 * 0) _ P (s.lane .xmm2 0))
    (fun j h1 h9 t k hq => q_ok j h1 h9 t k hq) (fun j t t' h f => h.yframe f)
    (keepC hp hrdx (h := 0) (c := 16 * e) (by omega) (by omega)) (c := 16 * e) (j := 16)
    (keepX hp hrdx (h := 0) (c := 16 * e) (by omega) (by omega)) (by omega) hI.a (by omega) (QH.one_iff.mpr ⟨hE₀, rfl⟩))
    fun s₁ ⟨hA₁, hQ₁, hg₁, hl₁, hm₁⟩ => ?_)
  rw [QH.ten_iff] at hQ₁
  have hrdx₁ : (s₁.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1) := by rw [hg₁]; exact hrdx
  have pw₁ : ∀ k < 8, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k := fun k hk => by
    rw [pw_keep hp hm₁ (by omega) (by omega)]; exact hI.pw k hk
  have pc₁ : s₁.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly := by
    rw [pw_keep hp hm₁ (by omega) (by decide)]; exact hI.pc
  have hE₁ := henv_of (h := 1) hp hA₁ hrdx₁ pw₁ pc₁ (by omega)
  -- The second batch, with the second half.
  refine WP.seq (WP.mono (batch_ok hp (q (128 * 1)) gRegsA gRegsA_ok
    (QH (s₁.gpr .rdx) (pp s₀) (128 * 1) _ P (s₁.lane .xmm2 0))
    (fun j h1 h9 t k hq => q_ok j h1 h9 t k hq) (fun j t t' h f => h.yframe f)
    (keepC hp hrdx₁ (h := 1) (c := 16 * e + 8) (by omega) (by omega)) (c := 16 * e + 8) (j := 24)
    (keepX hp hrdx₁ (h := 1) (c := 16 * e + 8) (by omega) (by omega)) (by omega) hA₁ (by omega) (QH.one_iff.mpr ⟨hE₁, rfl⟩))
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  rw [QH.ten_iff] at hQ₂
  refine WP.mono (nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, hg₁, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have hy : s'.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀)
      ((List.range (16 * (e + 1 - 1))).map fun k => Spec.GcmSiv.ofBytes (ctb s₀ k)) := by
    rw [fl, hQ₂.2, hf, hQ₁.2, hf, hI.y, show 16 * (e + 1 - 1) = 16 * (e - 1) + 8 + 8 by omega, ghash3]
  refine ⟨⟨by rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]; exact hA₂.keepG fg fm frd fwr, by omega, ?_,
    by rw [fr9, hr9], fun r h1 h2 h3 h4 => by rw [fg r h2 h3, hg₂, hg₁]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk => by rw [fm, pw_keep hp hm₂ (by omega) (by omega)]; exact pw₁ k hk,
    by rw [fm, pw_keep hp hm₂ (by omega) (by decide)]; exact pc₁, hy⟩, ?_⟩
  · rw [frdx, hg₂, hg₁, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by omega), hrdx, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

/-- The first group, deciphered only. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) := by
  have hw := hp.wrap_d
  have h16 := hp.nb16
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0)
    (fun _ _ _ _ _ _ _ _ => trivial) (by omega) hR.a (by rw [hR.rdx]) trivial)
    fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 8)
    (fun _ _ _ _ _ _ _ _ => trivial) (by omega) hA₁ (by rw [hg₁, hR.rdx]) trivial)
    fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  have gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, fun r h1 h2 _ h4 => by
    rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk => ?_, ?_, ?_⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [pw_keep hp hm₂ (by omega) (by omega), pw_keep hp hm₁ (by omega) (by omega)]; exact hR.pw k hk
  · rw [pw_keep hp hm₂ (by omega) (by decide), pw_keep hp hm₁ (by omega) (by decide)]; exact hR.pc
  · rw [hl₂ _ (by decide) (by decide) (by decide) (by decide) (by simp) 0 (by decide),
      hl₁ _ (by decide) (by decide) (by decide) (by decide) (by simp) 0 (by decide), hR.y]
    simp [ghashFrom]

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : Law s₀ P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ < 16 * (e + 1) ∧ EInv s₀ P e s' := by
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ < 16 * (e + 1) ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ < 16 * (e + 1) ∧ EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-! ## The last group, and `Y` stored -/

theorem accN_congr {X X' P P' : Nat → Block} {y : Block} (hx : ∀ k < 8, X k = X' k)
    (hq : ∀ k < 8, P k = P' k) : ∀ n, accN X P y n = accN X' P' y n
  | 0 => rfl
  | n + 1 => by
    have hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [accN_succ, accN_succ, accN_congr hx hq n, hq _ hk]
    simp only [hashInput, hx _ hk]


theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Block} (hf : Law s₀ P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (lastG ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  let f : Nat → Block := fun k => Spec.GcmSiv.ofBytes (ctb s₀ k)
  have hE₀ := henv_of (h := 0) hp hI.a hrdx hI.pw hI.pc (by omega)
  rw [lastG, List.append_assoc, WP.block_append_iff]
  refine WP.mono (hash8_ok s (128 * 0) hE₀.inp hE₀.ina hE₀.inc hE₀.pc) fun s₁ ⟨y₁, f₁⟩ => ?_
  have hA₁ : AInv s₀ (16 * e) s₁ := hI.a.yframe f₁
  have hE₁ := henv_of (h := 1) hp hA₁ (by rw [f₁.gpr]; exact hrdx) (by rw [f₁.mem]; exact hI.pw)
    (by rw [f₁.mem]; exact hI.pc) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (hash8_ok s₁ (128 * 1) hE₁.inp hE₁.ina hE₁.inc hE₁.pc) fun s₂ ⟨y₂, f₂⟩ => ?_
  rw [storeY, WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 revMask s₂ (by decide)) fun s₃ ⟨c₃, o₃⟩ => ?_
  have hrcx : s₃.gpr .rcx = yp s₀ := by
    rw [o₃.gpr _ (by decide), f₂.gpr, f₁.gpr]; exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  have h0 : s₃.lane .xmm0 0 = VG.Proof.Gcm.X86_64.revMask := by
    show s₃.xmm .xmm0 = _; rw [c₃, rev_eq]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₃ h0 (by
    rw [hrcx, o₃.wr, f₂.wr, f₁.wr, hI.a.wr]; exact hp.y_in)) fun s' ⟨m', g', rd', wr', _⟩ => ?_
  have hm₃ : s₃.mem = s.mem := by rw [o₃.mem, f₂.mem, f₁.mem]
  rw [hrcx, hm₃] at m'
  -- `Y`.
  have hy : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (nb s₀)).map f) := by
    show s₃.xmm .xmm2 = _
    rw [o₃.xmm _ (by decide)]
    show s₂.lane .xmm2 0 = _
    have hb₁ : ∀ k < 8, bufA s₁ (128 * 1) k = _ := hE₁.xs
    have hp₁ : ∀ k < 8, powA s₁ k = P k := hE₁.pv
    have hb₀ : ∀ k < 8, bufA s (128 * 0) k = _ := hE₀.xs
    have hp₀ : ∀ k < 8, powA s k = P k := hE₀.pv
    rw [y₂, show accN (bufA s₁ (128 * 1)) (powA s₁) (s₁.lane .xmm2 0) 8 =
        accN (fun k => f (16 * (e - 1) + 8 * 1 + k)) P (s₁.lane .xmm2 0) 8 from accN_congr hb₁ hp₁ 8, hf, y₁,
      show accN (bufA s (128 * 0)) (powA s) (s.lane .xmm2 0) 8 =
        accN (fun k => f (16 * (e - 1) + 8 * 0 + k)) P (s.lane .xmm2 0) 8 from accN_congr hb₀ hp₀ 8, hf, hI.y,
      he, show 16 * e = 16 * (e - 1) + 8 + 8 by omega, ghash3]
  have cY : Region.Disjoint (cR s₀) (yR s₀) := hp.c_y
  have dY : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have fY : Frame [yR s₀] s.mem s'.mem := by
    rw [m']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [rd', o₃.rd, f₂.rd, f₁.rd, hI.a.rd],
    by rw [wr', o₃.wr, f₂.wr, f₁.wr, hI.a.wr]⟩
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dY k hk) (by decide), hI.a.blocks k hk,
      ite_eq_left (by omega)]
  · rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cY) (by decide),
      ← VG.Proof.AesGcmSiv.X86_64.le16_readW, hI.a.ctr, he, le16_ctrX (rest₀ s₀)]
  · show blockAt s'.mem (yp s₀) = _
    rw [m', VG.Proof.Gcm.X86_64.blockAt_store, hy]
  · rw [m']
    exact (hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h | h <;> simp [h]).writeW
      (r := yR s₀) (by simp) _ (Region.contains_self _ _)
  · rw [g', o₃.gpr r h1, f₂.gpr, f₁.gpr]; exact hI.gpr r h1 h2 h3 h4

/-- The loop after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Block}
    (hf : Law s₀ P) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (lastG ++ storeY))))) s (DPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ =>
    final_ok hp hf (by have := hI₄.a.le; omega) hI₄)

/-- The interleaved loop, on `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨P, hR, hpw⟩ =>
    decTail_ok hp hm (fun X y => finishHash X P (hk s₀) y hpw) hR)

end

section

/-!
# AES-GCM-SIV's loops with AES-NI: sealing's loops

Untrusted: everything here is checked by Lean. `hash_ok`:
`Impl.AesGcmSiv.X86_64StitchAvx.hash` absorbs the `r9` blocks at `rdx` (a
multiple of 16, at least 16) into `Y` at `rcx`, each the field element of
its 16 bytes as they are, with GHASH and the key `H` at `r8`: the powers as
the interleaved loop's setup computes them (`powers_ok`), then sixteen
blocks a body, the loads of its last group (`hash8_ok`), and `Y` stored
(`Stitch.HPre` to `Stitch.HPost`, the 256-bit loop's contract). `ctr_ok`:
`ctr` enciphers the `r9` blocks at `r12` in counter mode from the counter
block at `rdx`, which it advances: the batches of the interleaved loop, with
nothing between their rounds (`batch_ok`), sixteen blocks a body
(`Stitch.SPre` to `Stitch.CPost`).
-/

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt ofNat_sub_ofNat ea_at constImm_ok rev_eq ldrev_ok)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly revMask)
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs)
open VG.Impl.AesGcmSiv.X86_64StitchAvx (hash8 lastG storeY hbody hash setupG stores loadY storeOne setupC batch
  cbody ctr polyO oneO)
open VG.Proof.Gcm.X86_64.StitchAvx8 (accN finishHash ghash_append8)
open VG.Proof.AesGcmSiv.X86_64.Stitch (SPre HPre HPost CPost kp nr cp yp hp pp dp nb xp xR xel kR cR yR dR pR sch
  ciph icb bAddr blk ctb hk y₀ d₀ rest₀ ctrX₀ le16_ctrX readW_ofBytes nextC_ok)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr store16_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## POLYVAL of the groups -/

/-- The hashing loop's state: `g` groups absorbed into `Y` (in `xmm2`). -/
structure HInv (s₀ : State) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  rdx : s.gpr .rdx = xp s₀ + BitVec.ofNat 64 (256 * g)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * g)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128 = P k
  pc : s.mem.readW (pp s₀ + BitVec.ofNat 64 polyO) 128 = poly
  frame : Frame [pR s₀] s₀.mem s.mem
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * g)).map (xel s₀))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The setup: the powers, stored, and `Y`. -/
theorem hsetup_ok {s₀ : State} (hp : HPre s₀) :
    WP isa (.block (setupG ++ stores ++ loadY)) s₀ fun s => ∃ P, HInv s₀ P 0 s ∧ Law s₀ P := by
  rw [WP.block_append_iff]
  refine WP.mono (powers_ok s₀ hp.h_in (fun _ hk => in_sub_int hp.p_in (by omega)) hp.wrap_p) fun s₁ P₁ => ?_
  have h0 : s₁.xmm .xmm0 = VG.Proof.Gcm.X86_64.revMask := by rw [P₁.m0, rev_eq]
  have hrcx : s₁.gpr .rcx = yp s₀ := P₁.gpr _ (by decide)
  refine WP.mono (ldrev_ok .xmm2 .rcx 0 s₁ (by decide) h0 (by
      rw [P₁.rd, P₁.wr, hrcx, BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hp.y_in))
    fun s₂ ⟨l₂, o₂⟩ => ?_
  have fP₁ : Frame [pR s₀] s₀.mem s₁.mem := P₁.frame
  refine ⟨fun k => s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (16 * k)) 128,
    ⟨?_, ?_, fun r h1 _ _ => by rw [o₂.gpr r h1, P₁.gpr r h1], fun k _ => by rw [o₂.mem],
      by rw [o₂.mem]; exact P₁.pc, by rw [o₂.mem]; exact fP₁, ?_, by rw [o₂.rd, P₁.rd],
      by rw [o₂.wr, P₁.wr]⟩, fun X y => finishHash X _ (hk s₀) y P₁.pw⟩
  · rw [o₂.gpr _ (by decide), P₁.gpr _ (by decide), Nat.mul_zero, BitVec.add_zero]
  · rw [o₂.gpr _ (by decide), P₁.gpr _ (by decide), Nat.mul_zero, Nat.sub_zero]; simp
  · show s₂.xmm .xmm2 = _
    rw [l₂, hrcx, BitVec.ofInt_natCast, BitVec.add_zero, Proof.AesGcm.X86_64.blockAt_frame fP₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.p_y.symm)]
    simp [ghashFrom]

/-- Eight blocks of group `g`, half `h`, as `hash8_ok` reads them. -/
theorem hblocks {s₀ : State} (hp : HPre s₀) {g h : Nat} {s : State} (hg : 16 * (g + 1) ≤ nb s₀) (hh : h < 2)
    (hrdx : s.gpr .rdx = xp s₀ + BitVec.ofNat 64 (256 * g)) (hf : Frame [pR s₀] s₀.mem s.mem) :
    ∀ k < 8, bufA s (128 * h) k = xel s₀ (16 * g + 8 * h + k) := fun k hk => by
  have hw := hp.wrap_x
  rw [show bufA s (128 * h) k = s.mem.readW (s.ea (at_ .rdx (128 * h + 16 * k))) 128 from rfl, ea_at,
    BitVec.ofInt_natCast, hrdx, Offset.add_add, readW_ofBytes,
    Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.p_x.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
    show 256 * g + (128 * h + 16 * k) = 16 * (16 * g + 8 * h + k) by omega]

/-- A body: the group at `rdx` absorbed. -/
theorem hbody_ok {s₀ : State} (hp : HPre s₀) {P : Nat → Block} (hf : Law s₀ P) {g : Nat}
    (hg : 16 * (g + 1) ≤ nb s₀) {s : State} (hI : HInv s₀ P g s) :
    WP isa (.block hbody) s fun s' => HInv s₀ P (g + 1) s' ∧ s'.zf = some (decide (nb s₀ - 16 * (g + 1) = 0)) := by
  have hw := hp.wrap_x
  have hwp := hp.wrap_p
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr _ (by decide) (by decide) (by decide)
  have eaP : ∀ (t : State), t.gpr = s.gpr → ∀ o, t.ea (at_ .r11 o) = pp s₀ + BitVec.ofNat 64 o := fun t ht o => by
    rw [ea_at, BitVec.ofInt_natCast, ht, hr11]
  have ins : ∀ (t : State), t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr →
      (∀ k < 8, InRegions (t.rd ++ t.wr) (t.ea (at_ .r11 (16 * k))) 16) ∧
      (∀ h < 2, ∀ k < 8, InRegions (t.rd ++ t.wr) (t.ea (at_ .rdx (128 * h + 16 * k))) 16) ∧
      InRegions (t.rd ++ t.wr) (t.ea (at_ .r11 polyO)) 16 := fun t hg' hrd hwr => by
    refine ⟨fun k hk => ?_, fun h hh k hk => ?_, ?_⟩
    · rw [eaP t hg', hrd, hwr, hI.rd, hI.wr]; exact in_rdwr (in_sub hp.p_in (by omega))
    · rw [ea_at, BitVec.ofInt_natCast, hg', hI.rdx, Offset.add_add, hrd, hwr, hI.rd, hI.wr]
      exact in_sub hp.x_in (by omega)
    · rw [eaP t hg', hrd, hwr, hI.rd, hI.wr]; exact in_rdwr (in_sub hp.p_in (by decide))
  obtain ⟨ip, ix, ic⟩ := ins s rfl rfl rfl
  have pv : ∀ (t : State), t.gpr = s.gpr → t.mem = s.mem → ∀ k < 8, powA t k = P k := fun t hg' hm k hk => by
    rw [show powA t k = t.mem.readW (t.ea (at_ .r11 (16 * k))) 128 from rfl, eaP t hg', hm]; exact hI.pw k hk
  rw [hbody, lastG, List.append_assoc, WP.block_append_iff]
  refine WP.mono (hash8_ok s (128 * 0) ip (ix 0 (by decide)) ic (by rw [eaP s rfl]; exact hI.pc))
    fun s₁ ⟨y₁, f₁⟩ => ?_
  obtain ⟨ip₁, ix₁, ic₁⟩ := ins s₁ f₁.gpr f₁.rd f₁.wr
  rw [WP.block_append_iff]
  refine WP.mono (hash8_ok s₁ (128 * 1) ip₁ (ix₁ 1 (by decide)) ic₁ (by rw [eaP s₁ f₁.gpr, f₁.mem]; exact hI.pc))
    fun s₂ ⟨y₂, f₂⟩ => ?_
  refine WP.mono (nextC_ok s₂) fun s' ⟨frdx, fr9, fzf, fg, fl, fm, frd, fwr⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have m₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (g + 1)) := by
    rw [g₂, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg _ (by omega)
  refine ⟨⟨?_, by rw [fr9, hr9], fun r h1 h2 h3 => by rw [fg r h2 h3, g₂]; exact hI.gpr r h1 h2 h3,
    fun k hk => by rw [fm, m₂]; exact hI.pw k hk, by rw [fm, m₂]; exact hI.pc, by rw [fm, m₂]; exact hI.frame,
    ?_, by rw [frd, f₂.rd, f₁.rd]; exact hI.rd, by rw [fwr, f₂.wr, f₁.wr]; exact hI.wr⟩, ?_⟩
  · rw [frdx, g₂, hI.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      Offset.add_add]
    congr 2
  · rw [fl, y₂, accN_congr (hblocks hp hg (by decide) (by rw [f₁.gpr]; exact hI.rdx) (by rw [f₁.mem]; exact hI.frame))
      (pv s₁ f₁.gpr f₁.mem) 8, hf, y₁, accN_congr (hblocks hp hg (by decide) hI.rdx hI.frame) (pv s rfl rfl) 8, hf,
      hI.y, show 16 * (g + 1) = 16 * g + 8 + 8 by omega, ghash3]
  · rw [fzf, hr9]
    simp only [Option.some.injEq]
    by_cases h : nb s₀ - 16 * (g + 1) = 0
    · simp [h]
    · simp only [h, decide_false]
      exact beq_false_of_ne fun h' => h (by
        have := congrArg BitVec.toNat h'
        rwa [toNat_ofNat_lt (by omega)] at this)

/-- `Y` stored. -/
theorem hfin_ok {s₀ : State} (hp : HPre s₀) {P : Nat → Block} {g : Nat} (hg : nb s₀ = 16 * g) {s : State}
    (hI : HInv s₀ P g s) : WP isa (.block storeY) s (HPost s₀) := by
  rw [storeY, WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm0 revMask s (by decide)) fun s₃ ⟨c₃, o₃⟩ => ?_
  have hrcx : s₃.gpr .rcx = yp s₀ := by
    rw [o₃.gpr _ (by decide)]; exact hI.gpr _ (by decide) (by decide) (by decide)
  have h0 : s₃.lane .xmm0 0 = VG.Proof.Gcm.X86_64.revMask := by
    show s₃.xmm .xmm0 = _; rw [c₃, rev_eq]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₃ h0 (by rw [hrcx, o₃.wr, hI.wr]; exact hp.y_in))
    fun s' ⟨m', g', rd', wr', _⟩ => ?_
  rw [hrcx, o₃.mem] at m'
  have hy : s₃.lane .xmm2 0 = s.lane .xmm2 0 := by show s₃.xmm .xmm2 = s.xmm .xmm2; rw [o₃.xmm _ (by decide)]
  refine ⟨?_, ?_, fun r h1 h2 h3 => ?_, by rw [rd', o₃.rd, hI.rd], by rw [wr', o₃.wr, hI.wr]⟩
  · show blockAt s'.mem (yp s₀) = _
    rw [m', VG.Proof.Gcm.X86_64.blockAt_store, hy, hI.y, hg]
  · rw [m']
    exact (hI.frame.mono fun r hr => by simp at hr ⊢; simp [hr]).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · rw [g', o₃.gpr r h1]; exact hI.gpr r h1 h2 h3

/-- POLYVAL of the groups. -/
theorem hash_ok {s₀ : State} (hp : HPre s₀) : WP isa hash s₀ (HPost s₀) := by
  have h16 := hp.nb16
  have hm := hp.nm
  refine WP.seq (WP.mono (hsetup_ok hp) fun s₁ ⟨P, hI₁, hf⟩ => WP.seq ?_)
  let I : Nat → State → Prop := fun m s => ∃ g, m = nb s₀ - 16 * g ∧ 16 * (g + 1) ≤ nb s₀ ∧ HInv s₀ P g s
  have hstep : ∀ m s, I m s → WP isa (.block hbody) s (fun s' =>
      (eval .ne s' = some false ∧ ∃ g, nb s₀ = 16 * g ∧ HInv s₀ P g s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨g, rfl, hg, hI⟩
    refine WP.mono (hbody_ok hp hf hg hI) fun s' ⟨hI', hzf⟩ => ?_
    by_cases h0 : nb s₀ - 16 * (g + 1) = 0
    · exact .inl ⟨by simp only [eval, hzf, h0, decide_true, Option.map_some, Bool.not_true],
        g + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hzf, h0, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (g + 1), by omega, g + 1, rfl, by omega, hI'⟩
  exact WP.mono (WP.loop (M := isa) I hstep (nb s₀ - 16 * 0) s₁ ⟨0, rfl, by omega, hI₁⟩)
    fun s ⟨g, hg, hI⟩ => hfin_ok hp hg hI

/-! ## Counter mode on the groups -/

/-- The loop's state: `g` groups enciphered. -/
structure CInv (s₀ : State) (g : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * g) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * g)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * g)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r

/-- The setup: 1 in the working space, the pointers. -/
theorem csetup_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block (storeOne ++ setupC)) s₀ (CInv s₀ 0) := by
  have hwp := hp.wrap_p
  rw [WP.block_append_iff]
  refine WP.mono (storeOne_ok s₀ (in_sub_int hp.p_in (by decide))) fun s₁ ⟨m₁, g₁, _, rd₁, wr₁⟩ => ?_
  refine WP.mono (setupC_ok s₁) fun s' ⟨r10', rax', rdx', gk', m', _, rd', wr'⟩ => ?_
  have fP : Frame [pR s₀] s₀.mem s'.mem := by
    rw [m', m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [gk' r h1 h2 h3, g₁ r h3]
  refine ⟨{ le := Nat.zero_le _
            rax := by rw [rax', g₁ _ (by decide)]
            rdi := hg _ (by decide) (by decide) (by decide)
            rsi := hg _ (by decide) (by decide) (by decide)
            r10 := by rw [r10', g₁ _ (by decide), g₁ _ (by decide)]
            r11 := hg _ (by decide) (by decide) (by decide)
            ctr := by
              rw [readW_ofBytes, Proof.AesGcm.X86_64.bytesAt_frame fP (fun r hr => by
                simp only [List.mem_singleton] at hr; subst hr; exact hp.p_c.symm) (by decide), ← readW_ofBytes,
                Nat.mul_zero, ctrX₀]
            one := by rw [m', m₁]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
            frame := fP.mono fun r hr => by simp at hr ⊢; simp [hr]
            blocks := fun k hk => by
              rw [Proof.AesGcm.X86_64.bytesAt_frame fP (fun r hr => by
                simp only [List.mem_singleton] at hr; subst hr
                exact hp.d_p.sub_left (Offset.sub_base _ (by have := hp.wrap_d; omega))) (by decide)]
              simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
            rd := by rw [rd', rd₁]
            wr := by rw [wr', wr₁] }, ?_, ?_, fun r h1 h2 _ h4 => hg r h1 h2 h4⟩
  · rw [rdx', g₁ _ (by decide), Nat.mul_zero, BitVec.add_zero]
  · rw [gk' _ (by decide) (by decide) (by decide), g₁ _ (by decide)]; simp

/-- A body: group `g` enciphered. -/
theorem cbody_ok {s₀ : State} (hp : SPre s₀) {g : Nat} (hg : 16 * (g + 1) ≤ nb s₀) {s : State}
    (hI : CInv s₀ g s) :
    WP isa cbody s fun s' => CInv s₀ (g + 1) s' ∧ s'.zf = some (decide (nb s₀ - 16 * (g + 1) = 0)) := by
  have hw := hp.wrap_d
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * g := by
    rw [hI.rdx, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 256 * g) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * g) (j := 0)
    (fun _ _ _ _ _ _ _ _ => trivial) (by omega) hI.a (by rw [hrdx]; omega) trivial)
    fun s₁ ⟨hA₁, _, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * g + 8) (j := 8)
    (fun _ _ _ _ _ _ _ _ => trivial) (by omega) hA₁ (by rw [hg₁, hrdx]; omega) trivial)
    fun s₂ ⟨hA₂, _, hg₂, _, _⟩ => ?_)
  refine WP.mono (nextC_ok s₂) fun s' ⟨frdx, fr9, fzf, fg, _, fm, frd, fwr⟩ => ?_
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (g + 1)) := by
    rw [hg₂, hg₁, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg _ (by omega)
  refine ⟨⟨by rw [show 16 * (g + 1) = 16 * g + 8 + 8 by omega]; exact hA₂.keepG fg fm frd fwr, ?_,
    by rw [fr9, hr9], fun r h1 h2 h3 h4 => by rw [fg r h2 h3, hg₂, hg₁]; exact hI.gpr r h1 h2 h3 h4⟩, ?_⟩
  · rw [frdx, hg₂, hg₁, hI.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, Offset.add_add]
    exact congrArg _ (congrArg _ (by omega))
  · rw [fzf, hr9]
    simp only [Option.some.injEq]
    by_cases h : nb s₀ - 16 * (g + 1) = 0
    · simp [h]
    · simp only [h, decide_false]
      exact beq_false_of_ne fun h' => h (by
        have := congrArg BitVec.toNat h'
        rwa [toNat_ofNat_lt (by omega)] at this)

/-- Counter mode on the groups. -/
theorem ctr_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa ctr s₀ (CPost s₀) := by
  have h16 := hp.nb16
  refine WP.seq (WP.mono (csetup_ok hp) fun s₁ hI₁ => ?_)
  let I : Nat → State → Prop := fun m s => ∃ g, m = nb s₀ - 16 * g ∧ 16 * (g + 1) ≤ nb s₀ ∧ CInv s₀ g s
  have hstep : ∀ m s, I m s → WP isa cbody s (fun s' =>
      (eval .ne s' = some false ∧ ∃ g, nb s₀ = 16 * g ∧ CInv s₀ g s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨g, rfl, hg, hI⟩
    refine WP.mono (cbody_ok hp hg hI) fun s' ⟨hI', hzf⟩ => ?_
    by_cases h0 : nb s₀ - 16 * (g + 1) = 0
    · exact .inl ⟨by simp only [eval, hzf, h0, decide_true, Option.map_some, Bool.not_true],
        g + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hzf, h0, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (g + 1), by omega, g + 1, rfl, by omega, hI'⟩
  refine WP.mono (WP.loop (M := isa) I hstep (nb s₀ - 16 * 0) s₁ ⟨0, rfl, by omega, hI₁⟩)
    fun s ⟨g, hg, hI⟩ => ⟨fun k hk => ?_, ?_, ?_, hI.gpr, hI.a.rd, hI.a.wr⟩
  · rw [hI.a.blocks k hk, ite_eq_left (by omega)]
  · rw [← VG.Proof.AesGcmSiv.X86_64.le16_readW, hI.a.ctr, ← hg, le16_ctrX (rest₀ s₀)]
  · exact hI.a.frame

end

section

/-!
# AES-GCM-SIV's loops with AES-NI, PCLMULQDQ and AVX meet `LoopsOk`

Untrusted: everything here is checked by Lean.
`Impl.AesGcmSiv.X86_64StitchAvx.loops`: their contracts (`dec_ok`,
`hash_ok`, `ctr_ok`), the taint analysis of each, and what the artifacts'
frame needs of their code.
-/

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64StitchAvx
open VG.Proof.AesGcmSiv.X86_64.Stitch (LoopsOk LoopsCode)

theorem loops_ok : LoopsOk loops where
  dec hp hm := dec_ok hp hm
  hash hp := hash_ok hp
  ctr hp hm := ctr_ok hp hm
  decT := ⟨_, by taint_decide⟩
  hashT := ⟨_, by taint_decide⟩
  ctrT := ⟨_, by taint_decide⟩

set_option linter.unusedSimpArgs false in
theorem loops_code : LoopsCode loops := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [loops, Impl.AesGcmSiv.X86_64StitchAvx.dec, setup, setupG, stores, storeOne, loadY, setupC, first,
    batch, ctrs, ctrsR, body, q, ghA, red, lastG, hash8, storeY, Impl.AesGcmSiv.X86_64StitchAvx.hash, hbody,
    Impl.AesGcmSiv.X86_64StitchAvx.ctr, cbody, Code.allInstrs, Code.all, Code.x86_64Depth] <;>
  decide +kernel

end

end VG.Proof.AesGcmSiv.X86_64.StitchAvx
