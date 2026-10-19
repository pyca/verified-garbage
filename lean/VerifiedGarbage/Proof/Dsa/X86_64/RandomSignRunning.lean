module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInit
import VerifiedGarbage.Proof.Framework.Omega

/-! The persistent state of the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomVolatile : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem random_saved_not_volatile {r : Reg} (h : r ∈ calleeSaved) : r ∉ randomVolatile := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure RandomSignRunning {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop where
  ready : ∃ m draws, RandomReady (randomContextOf h m hq) used draws t
  saved : RandomSaved s t.mem
  attempts : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key
  digest : Src t (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem random_sign_init_running {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      t.gpr .rax = 1 ∧ RandomSignRunning h hq 0 8 t := by
  refine WP.mono_mx (by decide) (random_sign_init h hq)
    fun t ⟨⟨⟨m, draws, hrax, hr⟩, hs, ha, hkey, hdigest⟩, hk⟩ hmx => ?_
  have hkv : Keep randomVolatile (allocState Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨hrax, ⟨m, draws, hr⟩, hs, ha, hk.2.1, hk.2.2, hkey, hdigest, ?_, ?_⟩
  · intro r hr hne
    rw [hkv.gpr (random_saved_not_volatile hr)]
    simp only [allocState, State.setReg, ite_eq_right hne]
  · rw [hmx]
    rfl

theorem RandomSignRunning.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hm : u.mem = t.mem) (hk : Keep [.rax] t u)
    (hmx : u.mxcsr = t.mxcsr) : RandomSignRunning h hq used fuel u := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := by rw [hm]; exact InScr.refl _ _ _
  refine ⟨⟨m, draws, hready.congr hm hk⟩, by rw [hm]; exact hr.saved,
    by rw [hm]; exact hr.attempts, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hr.key.congrK hf hk, hr.digest.congrK hf hk, ?_, ?_⟩
  · intro r hc hne
    exact ((hk.mono (show ∀ r ∈ [Reg.rax], r ∈ randomVolatile by decide)).gpr
      (random_saved_not_volatile hc)).trans (hr.callee r hc hne)
  · rw [hmx]; exact hr.mxcsr

end VG.Proof.Dsa.X86_64
