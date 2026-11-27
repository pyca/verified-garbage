module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Impl.Rc4.PPC64LE
public import VerifiedGarbage.Proof.Rc4.PPC64LE.Schedule
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Rc4.PPC64LE.Schedule
meta import VerifiedGarbage.Proof.Rc4.Memory
meta import VerifiedGarbage.Impl.Rc4.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Rc4
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Rc4.PPC64LE.Init`, which only this module used -/

section

/-! # RC4 on PPC64LE: checked initialization -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- Memory changed only within the 258-byte context at `p`. -/
def CtxFrame (p : Addr) (m m' : Mem) : Prop := ∀ x, ¬ (x - p).toNat < 258 → m' x = m x

theorem init_finish (s : State) (hp : InRegions s.wr (s.gpr .r3) 258) :
    WP isa (.block [.li .r12 0, .stb .r12 .r3 256, .stb .r12 .r3 257, .li .r3 0]) s fun t =>
      t.gpr .r3 = 0#64 ∧
      t.mem = (s.mem.write (s.gpr .r3 + 256#64) 1 0#8).write (s.gpr .r3 + 257#64) 1 0#8 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257]
  rfl

theorem ctx_frame_finish (m m' : Mem) (p : Addr) (h : TableFrame p m m') (a b : Byte) :
    CtxFrame p m ((m'.write (p + 256#64) 1 a).write (p + 257#64) 1 b) := by
  intro x hx
  have h1 : x ≠ p + 256#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  have h2 : x ≠ p + 257#64 := by
    intro he; apply hx; rw [he, Mem.sub_ofNat_toNat p (by decide)]; decide
  rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
  exact h x (by omega_using [hx])

theorem init_valid (s : State)
    (hlen : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .r5) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3) (s.gpr .r4).toNat)
    (hs : Mem.Sep (s.gpr .r3) (s.gpr .r4).toNat (s.gpr .r5) 256) :
    WP isa initValid s fun t => t.gpr .r3 = 0#64 ∧
      contextAt t.mem (s.gpr .r5) =
        { table := keySchedule (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat), i := 0, j := 0 } ∧
      CtxFrame (s.gpr .r5) s.mem t.mem := by
  have hstart : WP isa (.block [.logic .or .r7 .r3 .r3, .logic .or .r3 .r5 .r5, .li .r6 0]) s
      fun a => a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .r3 = s.gpr .r5 ∧
        a.gpr .r4 = s.gpr .r4 ∧ a.gpr .r7 = s.gpr .r3 ∧ a.gpr .r6 = 0#64 := by
    rrun [BitVec.or_self]
  unfold initValid
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, hap, ha4, ha7, ha6⟩ := ha
  have hpa : InRegions a.wr (a.gpr .r3) 256 := by
    rw [haw, hap]
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  have hia : IdentityInv a 0 a :=
    ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, rfl, by rw [ha6]⟩
  refine WP.seq (WP.mono (identity_loop a a (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hbp, hb7, hb4, _⟩ := hb
  have hreset : WP isa (.block [.li .r6 0, .li .r5 0, .li .r9 0, .li .r8 0]) b
      fun c => c.mem = b.mem ∧ c.rd = b.rd ∧ c.wr = b.wr ∧ c.gpr .r3 = b.gpr .r3 ∧
        c.gpr .r7 = b.gpr .r7 ∧ c.gpr .r4 = b.gpr .r4 ∧ c.gpr .r6 = 0#64 ∧
        c.gpr .r5 = 0#64 ∧ c.gpr .r9 = 0#64 ∧ c.gpr .r8 = 0#64 := by
    rrun
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcp, hc7, hc4, hc6, hc5, hc9, hc8⟩ := hc
  have hlc : 1 ≤ (c.gpr .r4).toNat ∧ (c.gpr .r4).toNat ≤ 256 := by
    rw [hc4, hb4, ha4]; exact hlen
  have hpc : InRegions c.wr (c.gpr .r3) 256 := by rw [hcw, hcp, hbw, hbp]; exact hpa
  have hkc : InRegions (c.rd ++ c.wr) (c.gpr .r7) (c.gpr .r4).toNat := by
    rw [hcr, hcw, hc7, hc4, hbr, hbw, hb7, hb4, har, haw, ha7, ha4]; exact hk
  have hsc : Mem.Sep (c.gpr .r7) (c.gpr .r4).toNat (c.gpr .r3) 256 := by
    rw [hc7, hc4, hcp, hb7, hb4, hbp, ha7, ha4, hap]; exact hs
  have hic : ScheduleInv c 0 c := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, hc8, rfl, rfl⟩
    · rw [hcm, hbm, hcp, hbp, identityMem_table, schedule_zero]
    · rw [hc9]; rfl
    · rw [hc6]
    · rw [hc5, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop c c (by decide) hlc hpc hkc hsc hic) fun d hd => ?_)
  have hpd : InRegions d.wr (d.gpr .r3) 258 := by
    rw [hd.wr, hd.p, hcw, hcp, hbw, hbp, haw, hap]; exact hp
  refine WP.mono (init_finish d hpd) fun e ⟨he3, hem⟩ => ?_
  have hp0 : d.gpr .r3 = s.gpr .r5 := by rw [hd.p, hcp, hbp, hap]
  have hkey : keyAt c = bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat := by
    unfold keyAt
    rw [hcm, hc7, hc4, hb7, hb4, ha7, ha4, hbm, ham]
    exact bytes_table_frame _ _ _ _ _ (s.gpr .r4).isLt
      (identityMem_frame _ _ _ (by decide)) (by rw [hap]; exact hs)
  refine ⟨he3, ?_, ?_⟩
  · rw [hem, hp0, context_finish, ← hp0, hd.p, hd.table, ← keySchedule_eq, hkey]
    rfl
  · rw [hem, hp0]
    refine ctx_frame_finish _ _ _ ?_ _ _
    have hf := hd.frame
    rw [hcm, hbm, hcp, hbp, hap, ham] at hf
    exact (identityMem_frame _ _ _ (by decide)).trans hf

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = (0 : BitVec 64) ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
  omega_using []

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .r5) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3) (s.gpr .r4).toNat)
    (hs : Mem.Sep (s.gpr .r3) (s.gpr .r4).toNat (s.gpr .r5) 256) :
    WP isa VG.Impl.Rc4.PPC64LE.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) with
      | .ok ctx => t.gpr .r3 = 0#64 ∧ contextAt t.mem (s.gpr .r5) = ctx
      | .error .invalidKeyLength => t.gpr .r3 = 1#64) ∧
      CtxFrame (s.gpr .r5) s.mem t.mem := by
  have hcheck : WP isa (.block [.subi .r12 .r4 1, .lsr .d .r12 .r12 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r3 = s.gpr .r3 ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 ∧
      t.gpr .r12 = (s.gpr .r4 - 1#64) >>> 8 := by
    rrun
  unfold VG.Impl.Rc4.PPC64LE.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, ht3, ht4, ht5, ht12⟩ := ht
  let good := 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 256
  have hcond : isa.eval (.nonzero .d .r12) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht12, bne]
    congr 1
    by_cases hg : good
    · rw [beq_iff_eq.mpr ((valid_length _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [beq_eq_false_iff_ne.mpr (fun h => hg ((valid_length _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun [htm]
    exact fun _ _ => rfl
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .r5) 258 := by rw [htw, ht5]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .r3) (t.gpr .r4).toNat := by
      rw [htr, htw, ht3, ht4]; exact hk
    have hst : Mem.Sep (t.gpr .r3) (t.gpr .r4).toNat (t.gpr .r5) 256 := by
      rw [ht3, ht4, ht5]; exact hs
    have hlt : 1 ≤ (t.gpr .r4).toNat ∧ (t.gpr .r4).toNat ≤ 256 := ht4 ▸ hg
    refine WP.mono (init_valid t hlt hpt hkt hst) fun u ⟨hu0, huc, huf⟩ => ?_
    simp only [htm, ht3, ht4, ht5] at huc huf
    exact ⟨⟨hu0, huc⟩, huf⟩

end VG.Proof.Rc4.PPC64LE

end

end

/-! ### `Rc4.PPC64LE.Apply`, which only this module used -/

section

/-! ### `Rc4.PPC64LE.ApplyStep`, which only this module used -/

section

/-! # RC4 on PPC64LE: one PRGA step -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- `i += 1`, then `j += S[i]`, copied to the index of the replacement. -/
def applyBefore : List Instr :=
  ([.addi .r6 .r6 1, .lsl .r6 .r6 56, .lsr .d .r6 .r6 56] : List Instr) ++ loadI ++
    ([.add .r7 .r7 .r0, .lsl .r7 .r7 56, .lsr .d .r7 .r7 56, .logic .or .r9 .r7 .r7] : List Instr)

/-- `S[i] := S[j]` (in `r10`), and the index `S[i] + S[j]` of the keystream byte. -/
def applyMiddle : List Instr :=
  loadI ++ ([.stb .r10 .r12 0, .add .r9 .r10 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] :
    List Instr)

/-- The keystream byte XORed into the data. -/
def applyAfter : List Instr :=
  [.lbz .r0 .r4 0, .logic .xor .r0 .r0 .r10, .stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]

theorem applyStep_eq :
    applyStep = applyBefore ++ (replace ++ (applyMiddle ++ (lookup ++ applyAfter))) := by
  simp only [applyStep, applyBefore, applyMiddle, applyAfter, List.append_assoc]

theorem byte_inc (i : Byte) :
    ((i.setWidth 64 + 1#64) <<< 56) >>> 56 = (i + 1#8).setWidth 64 := by
  obtain h := byte_add i 1#8
  rwa [show (1#8).setWidth 64 = 1#64 from rfl] at h

theorem apply_before (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.gpr .r6 = (i + 1#8).setWidth 64 ∧
      t.gpr .r7 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      Keep [.r0, .r6, .r7, .r9, .r12] s t ∧ t.mem = s.mem := by
  obtain hi : InRegions (s.rd ++ s.wr) (s.gpr .r3 + (i + 1#8).setWidth 64) 1 := by
    rw [byte_addr (i + 1#8)]
    exact region_offset _ _ _ _ _ (by have := (i + 1#8).isLt; omega_using [])
      (by have := (i + 1#8).isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r6 = (i + 1#8).setWidth 64 ∧
      t.gpr .r7 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.mem = s.mem) [.r0, .r6, .r7, .r9, .r12] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
  unfold applyBefore loadI
  rrun [hcx, h7, byte_inc, hi, BitVec.or_self]
  rw [byte_addr (i + 1#8), byte_add]

theorem apply_middle (s : State) (ii b : Byte)
    (hcx : s.gpr .r6 = ii.setWidth 64) (hax : s.gpr .r10 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)).setWidth 64 ∧
      Keep [.r0, .r9, .r12] s t := by
  obtain hw' : InRegions s.wr (s.gpr .r3 + ii.setWidth 64) 1 := by rw [byte_addr ii]; exact hw
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + ii.setWidth 64) 1 := by
    obtain ⟨r, hr, hc⟩ := hw'
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b ∧
      t.gpr .r9 = (b + s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)).setWidth 64)
      [.r0, .r9, .r12] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold applyMiddle loadI
  rrun [hcx, hax, hw', hr, low_byte, byte_add]
  rw [byte_addr ii]
  exact ⟨rfl, rfl⟩

theorem low_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [xor_byte, low_byte]

theorem apply_after (s : State) (k : Byte) (hax : s.gpr .r10 = k.setWidth 64)
    (hd : InRegions s.wr (s.gpr .r4) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .r4) 1 (s.mem (s.gpr .r4) ^^^ k) ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧
      Keep [.r0, .r4, .r5] s t := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .r4) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r4) 1 (s.mem (s.gpr .r4) ^^^ k) ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64) [.r0, .r4, .r5] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2, hk⟩
  unfold applyAfter
  rrun [hax, hd, hr, low_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .r3 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .r3 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .r3 + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = swapped.write (s.gpr .r4) 1 (swapped (s.gpr .r4) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧
      t.gpr .r6 = ii.setWidth 64 ∧ t.gpr .r7 = jj.setWidth 64 := by
  intro ii a jj b swapped k
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [applyStep_eq, WP.block_append_iff]
  refine WP.mono (apply_before s i j hcx h7 hr) fun t ⟨tcx, t7, t9, tk, tm⟩ => ?_
  obtain tp : t.gpr .r3 = s.gpr .r3 := tk.gpr (by decide)
  obtain t4 : t.gpr .r4 = s.gpr .r4 := tk.gpr (by decide)
  obtain t5 : t.gpr .r5 = s.gpr .r5 := tk.gpr (by decide)
  obtain t8 : t.gpr .r8 = s.gpr .r8 := tk.gpr (by decide)
  obtain htp : InRegions t.wr (t.gpr .r3) 256 := by rw [tk.2.2, tp]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (replace_core t jj ii t9 (t8.trans h8) tcx htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tp] at uax um
  obtain ucx : u.gpr .r6 = ii.setWidth 64 := (uk.gpr (by decide)).trans tcx
  obtain u7 : u.gpr .r7 = jj.setWidth 64 := (uk.gpr (by decide)).trans t7
  obtain up : u.gpr .r3 = s.gpr .r3 := (uk.gpr (by decide)).trans tp
  obtain u4 : u.gpr .r4 = s.gpr .r4 := (uk.gpr (by decide)).trans t4
  obtain u5 : u.gpr .r5 = s.gpr .r5 := (uk.gpr (by decide)).trans t5
  obtain u8 : u.gpr .r8 = s.gpr .r8 := (uk.gpr (by decide)).trans t8
  obtain urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  obtain uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  obtain hw : InRegions u.wr (u.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [uwr, up]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hp
  rw [WP.block_append_iff]
  refine WP.mono (apply_middle u ii b ucx uax hw) fun v ⟨vm, v9, vk⟩ => ?_
  obtain ha : u.mem (u.gpr .r3 + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, up, write_byte]
    split <;> rfl
  rw [ha] at v9
  rw [up, um] at vm
  have hvm : v.mem = swapped := vm
  obtain v9' : v.gpr .r9 = (a + b).setWidth 64 := by rw [v9, BitVec.add_comm]
  obtain vp : v.gpr .r3 = s.gpr .r3 := (vk.gpr (by decide)).trans up
  obtain v8 : v.gpr .r8 = s.gpr .r8 := (vk.gpr (by decide)).trans u8
  obtain vrd : v.rd = s.rd := vk.2.1.trans urd
  obtain vwr : v.wr = s.wr := vk.2.2.trans uwr
  obtain hvp : InRegions (v.rd ++ v.wr) (v.gpr .r3) 256 := by rw [vrd, vwr, vp]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (lookup_core v (a + b) v9' (v8.trans h8) hvp)
    (by decide +kernel)) fun w ⟨⟨wax, wm⟩, wk⟩ => ?_
  rw [hvm, vp] at wax
  obtain w4 : w.gpr .r4 = s.gpr .r4 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u4)
  obtain w5 : w.gpr .r5 = s.gpr .r5 := (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans u5)
  obtain wp : w.gpr .r3 = s.gpr .r3 := (wk.gpr (by decide)).trans vp
  obtain w8 : w.gpr .r8 = s.gpr .r8 := (wk.gpr (by decide)).trans v8
  obtain wrd : w.rd = s.rd := wk.2.1.trans vrd
  obtain wwr : w.wr = s.wr := wk.2.2.trans vwr
  obtain hwd : InRegions w.wr (w.gpr .r4) 1 := by rw [wwr, w4]; exact hd
  refine WP.mono (apply_after w k wax hwd) fun z ⟨zm, z4, z5, zk⟩ => ?_
  refine ⟨?_, zk.2.1.trans wrd, zk.2.2.trans wwr, (zk.gpr (by decide)).trans wp,
    (zk.gpr (by decide)).trans w8, ?_, ?_, ?_, ?_⟩
  · rw [zm, wm, hvm, w4]
  · rw [z4, w4]
  · rw [z5, w5]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), ucx]
  · rw [zk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), u7]

end VG.Proof.Rc4.PPC64LE

end

end


/-! # RC4 on PPC64LE: the stream function -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1)
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .r3)).table, i, j }
    WP isa (.block applyStep) s fun t =>
      (contextAt t.mem (s.gpr .r3)).table = next.1.table ∧
      t.gpr .r6 = next.1.i.setWidth 64 ∧ t.gpr .r7 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .r4) = s.mem (s.gpr .r4) ^^^ next.2 ∧
      StreamFrame (s.gpr .r3) (s.gpr .r4) 1 s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r4 = s.gpr .r4 + 1#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hcx h7 h8 hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h8', h1, h2, hi, hj⟩ := ht
  refine ⟨?_, hi, hj, ?_, ?_, hrd, hwr, h0, h8', h1, h2⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .r4 ≠ s.gpr .r3 + BitVec.ofNat 64 idx.toNat := by
      intro he
      obtain hn := hs (s.gpr .r4) (by rw [he, Mem.sub_ofNat_toNat _ (by omega_using [])]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    obtain ht := table_swap s.mem (s.gpr .r3) (i + 1#8)
      (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · rw [hmem]
    exact stream_frame_step _ _ _ _ _ _

/-- The unconsumed data remains unchanged by a stream iteration. -/
theorem apply_step_tail (s : State) (i j : Byte) (n : Nat)
    (hn : n + 1 < 2 ^ 64)
    (hcx : s.gpr .r6 = i.setWidth 64) (h7 : s.gpr .r7 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256) (hd : InRegions s.wr (s.gpr .r4) 1)
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) (n + 1)) :
    WP isa (.block applyStep) s fun t =>
      bytesAt t.mem (s.gpr .r4 + 1#64) n = bytesAt s.mem (s.gpr .r4 + 1#64) n := by
  refine WP.mono (apply_step s i j hcx h7 h8 hp hd) fun t ht => ?_
  rw [ht.1]
  rw [bytes_write_sep _ _ _ _ _ (by omega_using [hn])
    (sep_symm (Offset.sep_base (s.gpr .r4) (by decide) (by omega_using [hn])))]
  exact bytes_table_frame _ _ _ _ _ (by omega_using [hn]) (swap_frame _ _ _ _)
    (sep_symm (sep_tail hn hs))

structure LoopPost (s : State) (ctx : Context) (n : Nat) (t : State) : Prop where
  table : (contextAt t.mem (s.gpr .r3)).table =
    (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.table
  i : t.gpr .r6 = (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.i.setWidth 64
  j : t.gpr .r7 = (update ctx (bytesAt s.mem (s.gpr .r4) n)).1.j.setWidth 64
  data : bytesAt t.mem (s.gpr .r4) n = (update ctx (bytesAt s.mem (s.gpr .r4) n)).2
  frame : StreamFrame (s.gpr .r3) (s.gpr .r4) n s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  p : t.gpr .r3 = s.gpr .r3

theorem len_ne (n : Nat) (hn : n + 1 + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1 + 1) - 1#64 == (0 : BitVec 64)) = false := by
  apply beq_eq_false_iff_ne.mpr
  rw [Offset.ofNat_sub_ofNat (by omega_using [])]
  intro hz0
  obtain hh := congrArg BitVec.toNat hz0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])] at hh
  change n + 1 + 1 - 1 = 0 at hh
  omega_using [hh]

/-- Streaming correctness by induction on the public byte count. -/
theorem apply_loop (n : Nat) (s : State) (ctx : Context)
    (hn : n + 1 < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .r3)).table = ctx.table)
    (hcx : s.gpr .r6 = ctx.i.setWidth 64) (h7 : s.gpr .r7 = ctx.j.setWidth 64)
    (h8 : s.gpr .r8 = 0)
    (hlen : s.gpr .r5 = BitVec.ofNat 64 (n + 1))
    (hp : InRegions s.wr (s.gpr .r3) 256)
    (hd : InRegions s.wr (s.gpr .r4) (n + 1))
    (hs : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) (n + 1)) :
    WP isa (.loop (.block applyStep) (.nonzero .d .r5)) s (LoopPost s ctx (n + 1)) := by
  induction n generalizing s ctx with
  | zero =>
    have hd1 : InRegions s.wr (s.gpr .r4) 1 := hd
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .r3)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 h8 hp hd1 hs
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, _, _, hcount⟩ := ht
    have hbytes (m : Mem) : bytesAt m (s.gpr .r4) 1 = [m (s.gpr .r4)] := by
      simp [bytesAt]
    refine ⟨_, t, .loopExit he ?_, ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hcount, hlen]
      rfl
    · constructor
      · simpa only [Nat.zero_add, hbytes, update] using htab
      · simpa only [Nat.zero_add, hbytes, update] using hti
      · simpa only [Nat.zero_add, hbytes, update] using htj
      · simp only [Nat.zero_add, hbytes, update, hbyte]
      · exact hf
      · exact hrd
      · exact hwr
      · exact hp0
  | succ n ih =>
    obtain hd1 : InRegions s.wr (s.gpr .r4) 1 := by
      obtain hh := region_offset _ _ _ 0 1 (by decide) (by omega_using []) hd
      simpa only [BitVec.add_zero] using hh
    obtain hs1 : Mem.Sep (s.gpr .r3) 256 (s.gpr .r4) 1 := fun x hx hy => hs x hx (by omega_using [hy])
    obtain hctx : ({ table := (contextAt s.mem (s.gpr .r3)).table, i := ctx.i, j := ctx.j } :
        Context) = ctx := context_ext htable rfl rfl
    obtain hstep := apply_step_table s ctx.i ctx.j hcx h7 h8 hp hd1 hs1
    rw [hctx] at hstep
    obtain ⟨tr, t, he, ht⟩ := hstep
    obtain ⟨htab, hti, htj, hbyte, hf, hrd, hwr, hp0, ht8, hdptr, hcount⟩ := ht
    obtain htail : bytesAt t.mem (s.gpr .r4 + 1#64) (n + 1) =
        bytesAt s.mem (s.gpr .r4 + 1#64) (n + 1) := by
      obtain ⟨_, u, he', hh⟩ := apply_step_tail s ctx.i ctx.j (n + 1) hn hcx h7 h8 hp hd1 hs
      obtain ⟨_, rfl⟩ := Exec.det he' he
      exact hh
    obtain htlen : t.gpr .r5 = BitVec.ofNat 64 (n + 1) := by
      rw [hcount, hlen]
      exact Offset.ofNat_sub_ofNat (by omega_using [])
    obtain hpt : InRegions t.wr (t.gpr .r3) 256 := by rw [hwr, hp0]; exact hp
    obtain hdt : InRegions t.wr (t.gpr .r4) (n + 1) := by
      rw [hwr, hdptr]
      exact region_offset _ _ _ 1 (n + 1) (by decide) (by omega_using []) hd
    obtain hst : Mem.Sep (t.gpr .r3) 256 (t.gpr .r4) (n + 1) := by
      rw [hp0, hdptr]
      exact sep_tail hn hs
    obtain htab' : (contextAt t.mem (t.gpr .r3)).table = (step ctx).1.table := by
      rw [hp0]; exact htab
    obtain ⟨tr', u, he', hu⟩ := ih t (step ctx).1 (by omega_using [hn]) htab' hti htj (ht8.trans h8) htlen
      hpt hdt hst
    refine ⟨_, u, .loopNext he ?_ he', ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hcount, hlen, bne, len_ne n hn,
        Bool.not_false]
    · have hresult : update ctx (bytesAt s.mem (s.gpr .r4) (n + 1 + 1)) =
          ((update (step ctx).1 (bytesAt t.mem (t.gpr .r4) (n + 1))).1,
            (s.mem (s.gpr .r4) ^^^ (step ctx).2) ::
              (update (step ctx).1 (bytesAt t.mem (t.gpr .r4) (n + 1))).2) := by
        rw [bytes_cons, hdptr, htail]
        rfl
      constructor
      · rw [hresult, ← hp0]; exact hu.table
      · rw [hresult]; exact hu.i
      · rw [hresult]; exact hu.j
      · rw [bytes_cons, hresult]
        obtain hh : u.mem (s.gpr .r4) = t.mem (s.gpr .r4) := by
          have hf' := hu.frame
          rw [hp0, hdptr] at hf'
          exact stream_head _ _ _ _ _ hn hf' hs
        rw [hh, hbyte, ← hdptr, hu.data]
      · have hf' := hu.frame
        rw [hp0, hdptr] at hf'
        exact stream_frame_trans_tail hf hf'
      · exact hu.rd.trans hrd
      · exact hu.wr.trans hwr
      · exact hu.p.trans hp0

theorem apply_finish (s : State) (ctx : Context) (d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .r3)).table = ctx.table)
    (hcx : s.gpr .r6 = ctx.i.setWidth 64) (h7 : s.gpr .r7 = ctx.j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .r3) 258)
    (hs : Mem.Sep d n (s.gpr .r3) 258) :
    WP isa (.block [.stb .r6 .r3 256, .stb .r7 .r3 257]) s fun t =>
      contextAt t.mem (s.gpr .r3) = ctx ∧ bytesAt t.mem d n = bytesAt s.mem d n ∧
      t.mem = (s.mem.write (s.gpr .r3 + 256#64) 1 ctx.i).write (s.gpr .r3 + 257#64) 1 ctx.j := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, hcx, h7, low_byte]
  refine ⟨?_, ?_⟩
  · rw [context_finish, htable]
  · rw [bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide)),
      bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide))]

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 258) :
    WP isa (.block [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 ∧
      t.gpr .r6 = (contextAt s.mem (s.gpr .r3)).i.setWidth 64 ∧
      t.gpr .r7 = (contextAt s.mem (s.gpr .r3)).j.setWidth 64 ∧ t.gpr .r8 = 0 := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257, contextAt]

/-- Memory changed only within the context and the data. -/
def ApplyFrame (p d : Addr) (n : Nat) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 258 → ¬ (x - d).toNat < n → m' x = m x

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .r3) 258)
    (hd : InRegions s.wr (s.gpr .r4) (s.gpr .r5).toNat)
    (hs : Mem.Sep (s.gpr .r3) 258 (s.gpr .r4) (s.gpr .r5).toNat) :
    WP isa VG.Impl.Rc4.PPC64LE.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .r3))
        (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
      (contextAt t.mem (s.gpr .r3) = result.1 ∧
        bytesAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = result.2) ∧
      ApplyFrame (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat s.mem t.mem := by
  obtain hpRead : InRegions (s.rd ++ s.wr) (s.gpr .r3) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.PPC64LE.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, ha0, ha1, ha2, ha6, ha7, ha8⟩ := ha
  refine WP.ite (s.gpr .r5 == 0) (by simp only [eval, State.read, BitVec.setWidth_eq, ha2])
    (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .r5 = 0 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨⟨context_ext rfl rfl rfl, rfl⟩, fun _ _ _ => rfl⟩
  · have hnz' : s.gpr .r5 ≠ 0 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .r5).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .r5).toNat = n + 1 at hnEq
    obtain hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .r5).isLt
    obtain hpa : InRegions a.wr (a.gpr .r3) 256 := by
      rw [haw, ha0]
      obtain hh := region_offset _ _ _ 0 256 (by decide) (by decide) hp
      simpa only [BitVec.add_zero] using hh
    obtain hda : InRegions a.wr (a.gpr .r4) (n + 1) := by rw [haw, ha1, ← hnEq]; exact hd
    obtain hsa : Mem.Sep (a.gpr .r3) 256 (a.gpr .r4) (n + 1) := by
      rw [ha0, ha1, ← hnEq]
      exact fun x hx hy => hs x (by omega_using [hx]) hy
    obtain htable : (contextAt a.mem (a.gpr .r3)).table = (contextAt s.mem (s.gpr .r3)).table := by
      rw [ham, ha0]
    obtain hlen : a.gpr .r5 = BitVec.ofNat 64 (n + 1) := by
      rw [ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.seq (WP.mono (apply_loop n a (contextAt s.mem (s.gpr .r3)) hbound htable ha6 ha7
      ha8 hlen hpa hda hsa) fun b hb => ?_)
    obtain hpb : InRegions b.wr (b.gpr .r3) 258 := by rw [hb.wr, hb.p, haw, ha0]; exact hp
    obtain hsb : Mem.Sep (s.gpr .r4) (n + 1) (b.gpr .r3) 258 := by
      rw [hb.p, ha0, ← hnEq]
      exact sep_symm hs
    obtain htab : (contextAt b.mem (b.gpr .r3)).table =
        (update (contextAt s.mem (s.gpr .r3)) (bytesAt a.mem (a.gpr .r4) (n + 1))).1.table := by
      rw [hb.p]; exact hb.table
    refine WP.mono (apply_finish b _ (s.gpr .r4) (n + 1) (by omega_using [hnEq]) htab hb.i hb.j hpb hsb)
      fun t ⟨htc, htd, htm⟩ => ?_
    have hdata := hb.data
    rw [ha1, ham] at hdata
    rw [hb.p, ha0, ham, ha1] at htc
    rw [hnEq]
    refine ⟨⟨htc, htd.trans hdata⟩, ?_⟩
    intro x hx hy
    have hf := hb.frame
    rw [ha0, ha1, ham] at hf
    rw [htm, hb.p, ha0]
    obtain h1 : x ≠ s.gpr .r3 + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    obtain h2 : x ≠ s.gpr .r3 + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [write_byte, ite_eq_right h2, write_byte, ite_eq_right h1]
    exact hf x (by omega_using [hx]) hy

end VG.Proof.Rc4.PPC64LE

end

end

/-! # RC4 on PPC64LE: verified against the shared contracts -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- The registers the code writes: all volatile. -/
def written : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ctx : Region := ⟨s.gpr .r5, 258⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) with
    | .ok c => (s'.gpr .r3).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .r5) = c
    | .error .invalidKeyLength => (s'.gpr .r3).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, hkc⟩ := hs
  have hp : InRegions s.wr (s.gpr .r5) 258 :=
    ⟨⟨s.gpr .r5, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .r3) (s.gpr .r4).toNat :=
    ⟨⟨s.gpr .r3, (s.gpr .r4).toNat⟩,
      by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .r3) (s.gpr .r4).toNat (s.gpr .r5) 256 :=
    fun x hx hy => hkc x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy])
  obtain ⟨tr, t, he, ⟨hpost, -⟩, hkeep⟩ :=
    WP.keep written (init_ok s hp hk hsep) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), ?_⟩
  unfold initX
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) with
  | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 1 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified target init (Spec.Rc4.initContract abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, initX, abi, argRegs]
      [initSat]
      using initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .r3, 258⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    s.rd = [] ∧ s.wr = [ctx, data] ∧ ctx.Disjoint data
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .r3))
      (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
    contextAt s'.mem (s.gpr .r3) = result.1 ∧
      bytesAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat = result.2
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp ∧
    [(s₁.mem (s₁.gpr .r3 + 256)).toNat] = [(s₂.mem (s₂.gpr .r3 + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd⟩ := hs
  have hp : InRegions s.wr (s.gpr .r3) 258 :=
    ⟨⟨s.gpr .r3, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .r4) (s.gpr .r5).toNat :=
    ⟨⟨s.gpr .r4, (s.gpr .r5).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .r3) 258 (s.gpr .r4) (s.gpr .r5).toNat :=
    fun x hx hy => hcd x (by simp only [Region.Contains]; omega_using [hx]) (by simp only [Region.Contains]; omega_using [hy])
  obtain ⟨tr, t, he, ⟨hpost, -⟩, hkeep⟩ :=
    WP.keep written (apply_ok s hp hd hsep) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hpost⟩

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .r3 = b.gpr .r3
  data : a.gpr .r4 = b.gpr .r4
  len : a.gpr .r5 = b.gpr .r5
  sp : a.sp = b.sp
  i : (contextAt a.mem (a.gpr .r3)).i = (contextAt b.mem (b.gpr .r3)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .r3) 258

def startBlock : List Instr := [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public; and `r8` is zero. -/
theorem apply_start_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block startBlock) fun a b =>
      PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r8]) a b := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => EntryAgree a b) (.block startBlock) fun _ _ => True :=
    RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5]) (fun a b h => by
      refine ⟨h.sp, fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.p
      · exact h.data
      · exact h.len) (by taint_decide)
  obtain ⟨htrace, -⟩ := hct a b tr tr' a' b' hab ea eb
  obtain ⟨_, u, eu, hau⟩ := apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, ha0, ha1, ha2, ha6, _, ha8⟩ := hau
  obtain ⟨_, _, _, hb0, hb1, hb2, hb6, _, hb8⟩ := hbv
  refine ⟨htrace, ⟨(Exec.sp eu).trans (hab.sp.trans (Exec.sp ev).symm), fun r hr => ?_⟩⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha0.trans (hab.p.trans hb0.symm)
  · exact ha1.trans (hab.data.trans hb1.symm)
  · exact ha2.trans (hab.len.trans hb2.symm)
  · rw [ha6, hb6, hab.i]
  · rw [ha8, hb8]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b h
    simp only [eval, State.read, h.2 .r5 (by simp [PPC64LE.Taint.mem_ofRegs])]
  · exact RelCT.taint (A := vectorTaint) (Taint.ofRegs []) (fun _ _ h => ⟨h.1.1, by simp⟩)
      (by taint_decide)
  · exact RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r8]) (fun _ _ h => h.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : ReadValid s :=
    ⟨⟨s.gpr .r3, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified target apply (Spec.Rc4.applyContract abi) :=
  Verified.of_correct apply_correct apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
      applyX, abi, argRegs] [applySat]
      using applySat)

end VG.Proof.Rc4.PPC64LE
