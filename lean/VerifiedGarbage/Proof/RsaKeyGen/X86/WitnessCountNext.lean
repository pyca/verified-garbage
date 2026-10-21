module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessCount
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap

/-! # Accumulate one witness and its exact uniform-sampling bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessCount
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.WitnessCount

def nextClob : List Reg := [.eax, .ebx, .edx, .esi]
def nextRanges : List (Nat × Nat) := [(roundsOffset, 4), (uniformOffset, 4)]

theorem mask_bit (uniform : Bool) : cmask uniform &&& 1 = BitVec.ofNat 32 uniform.toNat := by
  cases uniform <;> decide

theorem next_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32} {uniform : Bool}
    (S : Prepare.Data g c capacity p s) (mask : s.mem.readW (off g.W 144) 32 = cmask uniform)
    (roundsFit : w32 s.mem g.W roundsOffset + 1 < 2 ^ 32)
    (uniformFit : w32 s.mem g.W uniformOffset + uniform.toNat < 2 ^ 32) :
    WP isa (.block next) s fun t =>
      Prepare.Data g c capacity p t ∧
      t.gpr .esi = s.gpr .eax ∧
      t.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) ∧
      t.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) ∧
      t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 ∧
      w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 ∧
      w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat ∧
      Outs g.W nextRanges s.mem t.mem ∧ Keeps nextClob s t := by
  have head := v.headerFit
  unfold next
  refine wp_movS rfl fun a A _ => ?_
  have Sa := S.ready.scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by unfold roundsOffset; omega)) fun b B _ =>
    wp_addS rfl fun d D _ => ?_
  have Kd : Keeps nextClob s d := ((A.keeps.mono (by unfold nextClob; decide)).widen B.keeps).widen D.keeps
  have Sd := S.ready.scratch.of_keeps Kd (by unfold nextClob; decide)
  have valueD : d.gpr .eax = BitVec.ofNat 32 (w32 s.mem g.W roundsOffset + 1) := by
    rw [D.gpr, B.gpr, A.mem]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32 = (w32 s.mem g.W roundsOffset + 1) % 2 ^ 32
    rfl
  refine wp_storeS (Sd.ea (by unfold roundsOffset; omega)) (Sd.write (by unfold roundsOffset; omega)) fun e E => ?_
  have Ke := Kd.widen (E.keeps [])
  have Se := S.ready.scratch.of_keeps Ke (by unfold nextClob; decide)
  have Oe : Outside g.W roundsOffset 4 s.mem e.mem := by
    rw [E.mem, D.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by unfold roundsOffset; decide)
  have sampleE : e.mem.readW (off g.W 144) 32 = cmask uniform := by
    exact (BitVec.eq_of_toNat_eq (Oe.w32 (d := 144)
      (by unfold roundsOffset; decide) (by decide))).trans mask
  refine wp_movS (readSrc_sc Se (d := 144) (by omega)) fun f F _ => wp_andi fun h H => ?_
  have Kh := (Ke.widen F.keeps).widen H.keeps
  have Sh := S.ready.scratch.of_keeps Kh (by unfold nextClob; decide)
  have uRead := readSrc_sc Sh (d := uniformOffset) (by unfold uniformOffset; omega)
  refine wp_addS uRead fun i I _ => ?_
  have Ki := Kh.widen I.keeps
  have Si := S.ready.scratch.of_keeps Ki (by unfold nextClob; decide)
  have valueI : i.gpr .ebx = BitVec.ofNat 32 (w32 s.mem g.W uniformOffset + uniform.toNat) := by
    have same : h.mem.readW (off g.W uniformOffset) 32 = s.mem.readW (off g.W uniformOffset) 32 := by
      rw [H.mem, F.mem]
      exact BitVec.eq_of_toNat_eq (Oe.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold uniformOffset; decide))
    rw [I.gpr, H.gpr, F.gpr, sampleE, mask_bit, same]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := uniform.toNat) (by have := Bool.toNat_le uniform; omega)]
    change (uniform.toNat + w32 s.mem g.W uniformOffset) % 2 ^ 32 = (w32 s.mem g.W uniformOffset + uniform.toNat) % 2 ^ 32
    rw [Nat.add_comm]
  refine wp_storeS (Si.ea (by unfold uniformOffset; omega)) (Si.write (by unfold uniformOffset; omega)) fun j J => ?_
  have Kj := Ki.widen (J.keeps [])
  have Sj := S.ready.scratch.of_keeps Kj (by unfold nextClob; decide)
  refine wp_movS (readSrc_sc Sj (d := checksOffset) (by unfold checksOffset; omega)) fun t T _ => WP.block_nil ?_
  have K := Kj.widen T.keeps
  have Oj : Outside g.W uniformOffset 4 e.mem j.mem := by
    rw [J.mem, I.mem, H.mem, F.mem]
    exact writeW32_outside _ _ _ (by unfold uniformOffset; decide)
  have O : Outs g.W nextRanges s.mem t.mem := by
    rw [T.mem]
    exact (Outs.of_outside Oe (by simp [nextRanges])).trans (Outs.of_outside Oj (by simp [nextRanges]))
  have gap : Outside g.W 128 96 s.mem t.mem := by
    rw [T.mem]
    exact (Oe.mono (by unfold roundsOffset; decide) (by unfold roundsOffset; decide)).trans
      (Oj.mono (by unfold uniformOffset; decide) (by unfold uniformOffset; decide))
  have roundT : w32 t.mem g.W roundsOffset = w32 s.mem g.W roundsOffset + 1 := by
    rw [T.mem, Oj.w32 (by unfold uniformOffset roundsOffset; decide) (by unfold roundsOffset; decide),
      E.mem, w32_write_self, valueD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt roundsFit]
  have uniformT : w32 t.mem g.W uniformOffset = w32 s.mem g.W uniformOffset + uniform.toNat := by
    rw [T.mem, J.mem, w32_write_self, valueI, BitVec.toNat_ofNat, Nat.mod_eq_of_lt uniformFit]
  have checksT : t.gpr .edx = s.mem.readW (off g.W checksOffset) 32 := by
    rw [T.gpr]
    exact BitVec.eq_of_toNat_eq ((Oj.w32 (by unfold uniformOffset checksOffset; decide) (by unfold checksOffset; decide)).trans
      (Oe.w32 (by unfold roundsOffset checksOffset; decide) (by unfold checksOffset; decide)))
  refine ⟨S.keepHeader v (by decide) (by decide) gap K (by unfold nextClob; decide) (by unfold nextClob; decide),
    ?_, ?_, ?_, checksT, roundT, uniformT, O, K⟩
  · rw [T.other .esi (by decide), J.gpr, I.other .esi (by decide), H.other .esi (by decide),
      F.other .esi (by decide), E.gpr, D.other .esi (by decide), B.other .esi (by decide)]
    exact A.gpr
  · rw [T.other .eax (by decide), J.gpr, I.other .eax (by decide), H.other .eax (by decide), F.other .eax (by decide), E.gpr]
    exact valueD
  · rw [T.other .ebx (by decide), J.gpr]; exact valueI

end VG.Proof.RsaKeyGen.X86.WitnessCount
