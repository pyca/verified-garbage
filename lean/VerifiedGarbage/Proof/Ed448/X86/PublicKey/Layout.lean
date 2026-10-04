import VerifiedGarbage.Proof.Ed448.X86.Shake.Entry
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 public-key derivation on x86 (32-bit): the contract the proof is written against

`pkLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/PublicKey/Layout.lean`)
with 57-byte buffers: what `vg_ed448_public_key(out, seed, scratch)` reads
and writes, their separation, and the 280 bytes of stack below its return
address. `Facts` are its separation and bounds, and `kit` the layout facts
the calls need (`Shake.Kit`).
-/

namespace VG.Proof.Ed448.X86.PublicKey

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

def pkRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
def pkWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 280
    s.rd = pkRd s ∧ s.wr = pkWr s ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

abbrev Ctx (s t : State) : Prop := VG.Proof.Ed25519.X86.Whole.Ctx (base s) s.gpr s.mem (pkRd s) (pkWr s) t

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev SEED (s : State) : Region := ⟨(arg s 1).setWidth 64, 57⟩

structure Facts (s : State) : Prop where
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR (arg s 2))
  sc : (SEED s).Disjoint (SCR (arg s 2))
  ao : (ARGS s 3).Disjoint (OUT s)
  ac : (ARGS s 3).Disjoint (SCR (arg s 2))
  ro : (RET s).Disjoint (OUT s)
  rc : (RET s).Disjoint (SCR (arg s 2))
  ko : (below (s.gpr .esp) 280).Disjoint (OUT s)
  ks : (below (s.gpr .esp) 280).Disjoint (SEED s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 2))
  out : (arg s 0).toNat + 57 ≤ 2 ^ 32
  seed : (arg s 1).toNat + 57 ≤ 2 ^ 32
  scratch : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem facts {s : State} (h : pkLocal.pre s) : Facts s := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, a, b, c, d, e⟩ := h
  exact ⟨os, oc, sc, ao, ac, ro, rc, ko, ks, kc, a, b, c, d, e⟩

theorem seed_in (s : State) : SEED s ∈ pkRd s := List.mem_cons_self
theorem args_in (s : State) : ARGS s 3 ∈ pkRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem out_in (s : State) : OUT s ∈ pkWr s := List.mem_cons_self
theorem scr_in (s : State) : SCR (arg s 2) ∈ pkWr s := List.mem_cons_of_mem _ List.mem_cons_self

theorem kit {s : State} (h : Facts s) : Kit (base s) (arg s 2) 3 (pkRd s) (pkWr s) := by
  refine Shake.kit h.below (by have := h.above; omega) h.scratch (scr_in s) ?_ ?_ ?_ (args_in s)
  · intro R hR
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [h.ko, h.kc]
  · intro r hr R hR
    simp only [pkRd, pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr hR
    rcases hr with rfl | rfl <;> rcases hR with rfl | rfl
    exacts [h.os.symm, h.sc, h.ao, h.ac]
  · intro r hr
    simp only [pkRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.ks.symm, Shake.args_stack (n := 3) h.below (by have := h.above; omega) (by decide)]

theorem ret_out {s : State} (h : Facts s) : ∀ R ∈ pkWr s, (RET s).Disjoint R := by
  intro R hR
  simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [h.ro, h.rc]

end VG.Proof.Ed448.X86.PublicKey
