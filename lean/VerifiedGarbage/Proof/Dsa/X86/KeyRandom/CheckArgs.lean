module

public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallArgs

/-! # The domain checker's six outgoing arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

def argsMem (s₀ : State) (m : Mem) : Mem :=
  ((((((m.writeW (off (rBase s₀) 0) (X86.arg s₀ 3)).writeW (off (rBase s₀) 4) (X86.arg s₀ 4)).writeW (off (rBase s₀) 8) (X86.arg s₀ 5)).writeW (off (rBase s₀) 12) (X86.arg s₀ 6)).writeW (off (rBase s₀) 16) (X86.arg s₀ 9)).writeW (off (rBase s₀) 20) (X86.arg s₀ 10))

theorem argsMem_slots (s₀ : State) (m : Mem) (sp : BitVec 32) :
    ∀ i < 6, slot (argsMem s₀ m) (rBase s₀) (4 * i) = callVal s₀ sp i := by
  intro i hi
  unfold argsMem
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp (disch := decide) only [slot_write_self, slot_write_ne, Nat.reduceMul, callVal]

theorem argsMem_outs (s₀ : State) (m : Mem) : Outs (rBase s₀) [(0, 24)] m (argsMem s₀ m) := by
  unfold argsMem
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 24) =>
    KeyRandom.store_in (rBase s₀) m (rs := [(0, 24)]) (o := 0) (n := 24) (d := d) v
      (List.mem_singleton_self _) (Nat.zero_le _) h (by omega)
  exact (((((e _ (by decide)).trans (e _ (by decide))).trans (e _ (by decide))).trans
    (e _ (by decide))).trans (e _ (by decide))).trans (e _ (by decide))

theorem checkArgs_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Ready s₀ u → u.mem = argsMem s₀ t.mem → Keeps [.eax] t u → WP isa (.block is) u Q) :
    WP isa (.block (checkArgs ++ is)) t Q := by
  unfold checkArgs
  simp only [List.append_assoc]
  refine KeyRandom.copyArg_ok A h (by decide) (by decide) fun u1 h1 m1 k1 => ?_
  refine KeyRandom.copyArg_ok A h1 (by decide) (by decide) fun u2 h2 m2 k2 => ?_
  refine KeyRandom.copyArg_ok A h2 (by decide) (by decide) fun u3 h3 m3 k3 => ?_
  refine KeyRandom.copyArg_ok A h3 (by decide) (by decide) fun u4 h4 m4 k4 => ?_
  refine KeyRandom.copyArg_ok A h4 (by decide) (by decide) fun u5 h5 m5 k5 => ?_
  refine KeyRandom.copyArg_ok A h5 (by decide) (by decide) fun u6 h6 m6 k6 => ?_
  refine k u6 h6 ?_ ((((((k1).trans k2).trans k3).trans k4).trans k5).trans k6)
  rw [m6, m5, m4, m3, m2, m1]
  rfl

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
