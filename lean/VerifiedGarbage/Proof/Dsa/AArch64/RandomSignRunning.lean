module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInputs

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInit
import VerifiedGarbage.Proof.Framework.Omega

/-! The persistent state of the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomVolatile : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem random_saved_not_volatile {r : Reg} (h : r ∈ preserved) : r ∉ randomVolatile := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure RandomSignRunning {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop where
  ready : ∃ m draws, RandomReady (randomContextOf h m hq) used draws t
  saved : RandomSaved s t.mem
  attempts : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Src t (randomBase s) Random.frameBytes (s.gpr .x3) (randomInput s).key
  digest : Src t (randomBase s) Random.frameBytes (s.gpr .x7) (randomInput s).digest
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  link : word t.mem (randomBase s) RandomSign.oLink = s.gpr .x30

theorem random_sign_init_running {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) fun t =>
      t.gpr .x0 = 1 ∧ RandomSignRunning h hq 0 8 t := by
  refine WP.mono (random_sign_init h hq)
    fun t ⟨⟨⟨m, draws, hresult, hr⟩, hs, ha, hkey, hdigest, hlink⟩, hk⟩ => ?_
  have hkv : Keep randomVolatile (allocated Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨hresult, ⟨m, draws, hr⟩, hs, ha, hk.rd, hk.wr, hkey, hdigest, ?_, hk.vcs, hlink⟩
  intro r hr
  exact hkv.gpr r (random_saved_not_volatile hr)

theorem RandomSignRunning.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hm : u.mem = t.mem) (hk : Keep [.x0, .x4] t u) : RandomSignRunning h hq used fuel u := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := by rw [hm]; exact InScr.refl _ _ _
  refine ⟨⟨m, draws, hready.congr hm hk⟩, by rw [hm]; exact hr.saved,
    by rw [hm]; exact hr.attempts, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hr.key.congrK hf hk, hr.digest.congrK hf hk, ?_,
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), by rw [hm]; exact hr.link⟩
  intro r hc
  exact ((hk.mono (show ∀ r ∈ [Reg.x0, Reg.x4], r ∈ randomVolatile by decide)).gpr r
    (random_saved_not_volatile hc)).trans (hr.callee r hc)

end VG.Proof.Dsa.AArch64
