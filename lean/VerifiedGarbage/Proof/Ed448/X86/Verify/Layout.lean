import VerifiedGarbage.Proof.Ed448.X86.Shake.Entry
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification on x86 (32-bit): the contract the proof is written against

`vfLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/VerifyMessage`):
what `vg_ed448_verify(pk, context, ctxlen, message, len, signature,
scratch)` reads (the public key, the context, the message, the signature
and its arguments) and writes (`scratch`), their separation, and the 280
bytes of stack below its return address. The inputs are public (`pub`
includes their bytes). `Facts` are its separation and bounds, and `kit` the
layout facts the calls need (`Shake.Kit`).
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

abbrev PK (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev CTX (s : State) : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
abbrev MSG (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev SIG (s : State) : Region := ⟨(arg s 5).setWidth 64, 114⟩

def vfRd (s : State) : List Region := [PK s, CTX s, MSG s, SIG s, ⟨argAddr s 0, 28⟩]
def vfWr (s : State) : List Region := [⟨(arg s 6).setWidth 64, 8192⟩]

def vfLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let sig : Region := ⟨(arg s 5).setWidth 64, 114⟩
    let scr : Region := ⟨(arg s 6).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := below (s.gpr .esp) 280
    s.rd = vfRd s ∧ s.wr = vfWr s ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s t := t.gpr .eax = if Spec.Ed448.verify
    (Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57)
    (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) 114) then 1 else 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧ arg s 5 = arg t 5 ∧ arg s 6 = arg t 6 ∧
    Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57 = Spec.Ed448.bytesAt t.mem ((arg t 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Ed448.bytesAt t.mem ((arg t 1).setWidth 64) (arg t 2).toNat ∧
    Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Ed448.bytesAt t.mem ((arg t 3).setWidth 64) (arg t 4).toNat ∧
    Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) 114 = Spec.Ed448.bytesAt t.mem ((arg t 5).setWidth 64) 114

structure Facts (s : State) : Prop where
  pc : (PK s).Disjoint (SCR (arg s 6))
  xc : (CTX s).Disjoint (SCR (arg s 6))
  mc : (MSG s).Disjoint (SCR (arg s 6))
  sc : (SIG s).Disjoint (SCR (arg s 6))
  ac : (ARGS s 7).Disjoint (SCR (arg s 6))
  rc : (RET s).Disjoint (SCR (arg s 6))
  kp : (below (s.gpr .esp) 280).Disjoint (PK s)
  kx : (below (s.gpr .esp) 280).Disjoint (CTX s)
  km : (below (s.gpr .esp) 280).Disjoint (MSG s)
  ks : (below (s.gpr .esp) 280).Disjoint (SIG s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 6))
  pk : (arg s 0).toNat + 57 ≤ 2 ^ 32
  ctx : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  msg : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  sig : (arg s 5).toNat + 114 ≤ 2 ^ 32
  scratch : (arg s 6).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32

theorem facts {s : State} (h : vfLocal.pre s) : Facts s := by
  obtain ⟨_, _, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, f, g⟩ := h
  exact ⟨pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, f, g⟩

theorem pk_in (s : State) : PK s ∈ vfRd s := List.mem_cons_self
theorem ctx_in (s : State) : CTX s ∈ vfRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem msg_in (s : State) : MSG s ∈ vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem sig_in (s : State) : SIG s ∈ vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem args_in (s : State) : ARGS s 7 ∈ vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
theorem scr_in (s : State) : SCR (arg s 6) ∈ vfWr s := List.mem_cons_self

theorem kit {s : State} (h : Facts s) : Kit (base s) (arg s 6) 7 (vfRd s) (vfWr s) := by
  refine Shake.kit h.below (by have := h.above; omega) h.scratch (scr_in s) ?_ ?_ ?_ (args_in s)
  · intro R hR
    rw [List.mem_singleton.mp hR]; exact h.kc
  · intro r hr R hR
    rw [List.mem_singleton.mp hR]
    simp only [vfRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.pc, h.xc, h.mc, h.sc, h.ac]
  · intro r hr
    simp only [vfRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kp.symm, h.kx.symm, h.km.symm, h.ks.symm,
      Shake.args_stack (n := 7) h.below (by have := h.above; omega) (by decide)]

theorem ret_out {s : State} (h : Facts s) : ∀ R ∈ vfWr s, (RET s).Disjoint R := by
  intro R hR
  rw [List.mem_singleton.mp hR]; exact h.rc

end VG.Proof.Ed448.X86.Verify
