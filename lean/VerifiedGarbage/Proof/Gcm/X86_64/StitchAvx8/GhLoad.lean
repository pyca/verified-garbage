import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.GhBits

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
