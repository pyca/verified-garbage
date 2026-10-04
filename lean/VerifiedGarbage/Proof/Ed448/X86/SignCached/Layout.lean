import VerifiedGarbage.Proof.Ed448.X86.Shake.Entry
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 signing with a cached key on x86 (32-bit): the contract the proof is written against

`scLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/SignCached`): what
`vg_ed448_sign_cached(out, seed, pk, context, ctxlen, message, len, scratch)`
reads (the private and public keys, the context, the message and its
arguments) and writes (`out` and `scratch`), their separation, the 280 bytes
of stack below its return address, the public key of the private key, and a
context of at most 255 bytes. Only pointers and lengths are public. `Facts`
are its separation and bounds, and `kit` the layout facts the calls need.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 114⟩
abbrev SEED (s : State) : Region := ⟨(arg s 1).setWidth 64, 57⟩
abbrev PK (s : State) : Region := ⟨(arg s 2).setWidth 64, 57⟩
abbrev CTX (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev MSG (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩

def scRd (s : State) : List Region := [SEED s, PK s, CTX s, MSG s, ⟨argAddr s 0, 32⟩]
def scWr (s : State) : List Region := [OUT s, ⟨(arg s 7).setWidth 64, 8192⟩]

def scLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 114⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let msg : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scr : Region := ⟨(arg s 7).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := below (s.gpr .esp) 280
    s.rd = scRd s ∧ s.wr = scWr s ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
      (arg s 7).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
      Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57) ∧
      (arg s 4).toNat ≤ 255
  post s t := Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
    (Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧ arg s 5 = arg t 5 ∧ arg s 6 = arg t 6 ∧ arg s 7 = arg t 7

structure Facts (s : State) : Prop where
  os : (OUT s).Disjoint (SEED s)
  op : (OUT s).Disjoint (PK s)
  ox : (OUT s).Disjoint (CTX s)
  om : (OUT s).Disjoint (MSG s)
  oa : (OUT s).Disjoint (ARGS s 8)
  oc : (OUT s).Disjoint (SCR (arg s 7))
  ko : (below (s.gpr .esp) 280).Disjoint (OUT s)
  ro : (RET s).Disjoint (OUT s)
  sc : (SEED s).Disjoint (SCR (arg s 7))
  pc : (PK s).Disjoint (SCR (arg s 7))
  xc : (CTX s).Disjoint (SCR (arg s 7))
  mc : (MSG s).Disjoint (SCR (arg s 7))
  ac : (ARGS s 8).Disjoint (SCR (arg s 7))
  rc : (RET s).Disjoint (SCR (arg s 7))
  ks : (below (s.gpr .esp) 280).Disjoint (SEED s)
  kp : (below (s.gpr .esp) 280).Disjoint (PK s)
  kx : (below (s.gpr .esp) 280).Disjoint (CTX s)
  km : (below (s.gpr .esp) 280).Disjoint (MSG s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 7))
  out : (arg s 0).toNat + 114 ≤ 2 ^ 32
  seed : (arg s 1).toNat + 57 ≤ 2 ^ 32
  pk : (arg s 2).toNat + 57 ≤ 2 ^ 32
  ctx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  msg : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratch : (arg s 7).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 36 ≤ 2 ^ 32
  key : Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
  ctxlen : (arg s 4).toNat ≤ 255

theorem facts {s : State} (h : scLocal.pre s) : Facts s := by
  obtain ⟨_, _, os, op, ox, om, oa, oc, ko, ro, sc, pc, xc, mc, ac, rc, ks, kp, kx, km, kc,
    a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨os, op, ox, om, oa, oc, ko, ro, sc, pc, xc, mc, ac, rc, ks, kp, kx, km, kc, a, b, c, d, e, f, g, i, j, k⟩

theorem seed_in (s : State) : SEED s ∈ scRd s := List.mem_cons_self
theorem pk_in (s : State) : PK s ∈ scRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem ctx_in (s : State) : CTX s ∈ scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem msg_in (s : State) : MSG s ∈ scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem args_in (s : State) : ARGS s 8 ∈ scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
theorem out_in (s : State) : OUT s ∈ scWr s := List.mem_cons_self
theorem scr_in (s : State) : SCR (arg s 7) ∈ scWr s := List.mem_cons_of_mem _ List.mem_cons_self

theorem kit {s : State} (h : Facts s) : Kit (base s) (arg s 7) 8 (scRd s) (scWr s) := by
  refine Shake.kit h.below (by have := h.above; omega) h.scratch (scr_in s) ?_ ?_ ?_ (args_in s)
  · intro R hR
    simp only [scWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [h.ko, h.kc]
  · intro r hr R hR
    simp only [scRd, scWr, List.mem_cons, List.not_mem_nil, or_false] at hr hR
    rcases hR with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.os.symm, h.op.symm, h.ox.symm, h.om.symm, h.oa.symm, h.sc, h.pc, h.xc, h.mc, h.ac]
  · intro r hr
    simp only [scRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.ks.symm, h.kp.symm, h.kx.symm, h.km.symm,
      Shake.args_stack (n := 8) h.below (by have := h.above; omega) (by decide)]

theorem ret_out {s : State} (h : Facts s) : ∀ R ∈ scWr s, (RET s).Disjoint R := by
  intro R hR
  simp only [scWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [h.ro, h.rc]

/-- The two halves of `out`: `R`, then `r` and `S`. -/
abbrev OUT1 (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev OUT2 (s : State) : Region := ⟨(arg s 0).setWidth 64 + BitVec.ofNat 64 57, 57⟩

theorem out1_within (s : State) : VG.Proof.Ed25519.X86.Whole.Within (OUT1 s) (OUT s) :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩

theorem out2_within (s : State) : VG.Proof.Ed25519.X86.Whole.Within (OUT2 s) (OUT s) :=
  ⟨57, rfl, by show 57 + 57 ≤ 114; decide⟩

theorem out2_addr {s : State} (h : Facts s) : (arg s 0 + BitVec.ofNat 32 57).setWidth 64 =
    (arg s 0).setWidth 64 + BitVec.ofNat 64 57 :=
  addr_eq (by have := h.out; omega)

theorem out12 (s : State) : (OUT1 s).Disjoint (OUT2 s) := Offset.base_disjoint _ (by decide) (by decide)

end VG.Proof.Ed448.X86.SignCached
