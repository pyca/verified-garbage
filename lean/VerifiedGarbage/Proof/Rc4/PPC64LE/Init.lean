module

import VerifiedGarbage.Proof.Rc4.PPC64LE.Schedule
public import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Stream
public import VerifiedGarbage.Impl.Rc4.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rc4.PPC64LE.Lookup
public import VerifiedGarbage.Spec.Rc4

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
  exact h x (by omega)

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
  omega

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
