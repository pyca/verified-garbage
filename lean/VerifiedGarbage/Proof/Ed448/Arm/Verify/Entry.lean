import VerifiedGarbage.Proof.Ed448.Arm.Verify.Body
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap

/-!
# Ed448 verification on ARMv7: the contract, and the frame

`verifyLocal`, the contract the proof is written against; `inner_ok`, the
frame (`Whole.wrap_ok`) around the body for a context of fewer than 256
bytes; `verify_ok`, the whole function, with the check of the context's
length before it.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok
  Whole.originalWord Whole.Ctx)
open VG.Proof.X25519.Arm (op2_lsr op2_imm)

/-- `vg_ed448_verify(pk = r0, context = r1, ctxlen = r2, message = r3, len = [sp],
signature = [sp, #4], scratch = [sp, #8]) -> r0`, with 280 bytes of stack. -/
def verifyLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let sig : Region := ⟨State.addr (stackArg s 1), 114⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 8192⟩
    let args : Region := ⟨State.addr s.sp, 12⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [pk, ctx, msg, sig, args] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s t := t.gpr .r0 = signWord (Spec.Ed448.verify
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) 114))
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, Whole.base s⟩

section
variable {s : State} (h : verifyLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem entry_top : s.sp.toNat + 12 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem original_args : (lay s).ORIG = ⟨State.addr s.sp, 12⟩ := by
  unfold Lay.ORIG lay
  rw [Whole.base_addr (entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1, List.mem_singleton] at hr
  subst r
  rw [stack_eq h]
  exact h.2.2.2.2.2.2.2.2.2.2.2.1

theorem lay_ok (hl : (s.gpr .r2).toNat < 256) : (lay s).Ok := by
  have hb := entry_below h
  have ht := entry_top h
  have ho := original_args h
  have hs : (lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, ps, xs, ms, ss, os, kp, kx, km, ks, kc, np, nx, nm, ns, nc, _, _⟩ := h
  refine ⟨?_, hl, ps, xs, ms, ss, by rw [ho]; exact os, by rw [hs]; exact kp, by rw [hs]; exact kx,
    by rw [hs]; exact km, by rw [hs]; exact ks, by rw [hs]; exact kc, np, nx, nm, ns, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 292 ≤ 2 ^ 32
  omega

theorem entry_regions : (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.PK, Lay.CTX, Lay.MSG, Lay.SIG, Lay.SCR, Lay.ARGS,
    lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  rw [(entry_regions h).1, (entry_regions h).2]
  exact hc

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  have hb := entry_below h
  have ht := entry_top h
  intro j hj
  obtain ⟨hj11, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega) hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, lay, stackArg, stackArgAddr] using hw
  · obtain rfl : j = 10 := by omega
    have hf := Whole.saved_frame hb hp
    have hbt := Whole.base_top hb
    have ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10) = State.addr (s.sp + BitVec.ofNat 32 8) := by
      rw [addr_add (by omega), Whole.base_addr hb, show (248 + 4 * 10 : Nat) = 280 + 8 from rfl,
        ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
        BitVec.sub_add_cancel]
    change p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10)) 32 = stackArg s 2
    rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10), 4⟩) (Region.contains_self _ _)
      (by
        rintro r hr
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), ea]
    rfl

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  have ht := entry_top h
  intro j hj h4
  have hj' : j = 4 ∨ j = 5 := by omega
  refine ⟨⟨State.addr s.sp, 12⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega)]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega) (by omega)

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, kp, kx, km, ks, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact ks.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 12) (by decide)

end

/-- The frame around the body, for a context of fewer than 256 bytes. -/
theorem inner_ok (hv : EqOk) {s : State} (h : verifyLocal.pre s) (hl : (s.gpr .r2).toNat < 256) :
    WP isa (wrap 6 body) s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 6 ≤ 6) (entry_below h)
    (by have := entry_top h; omega) (entry_read h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r0)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) 114)))
    (fun p hp => WP.mono (body_ok hv (entry_ctx h hp) (lay_ok h hl) (entry_args h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have e0 := entry_input h hf (r := ⟨State.addr (s.gpr .r0), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have e1 := entry_input h hf (r := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat ≤ 2 ^ 64; have := (s.gpr .r2).isLt; omega)
  have e3 := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega)
  have e5 := entry_input h hf (r := ⟨State.addr (stackArg s 1), 114⟩) (by rw [h.1]; simp)
    (by change 114 ≤ 2 ^ 64; decide)
  change u.gpr .r0 = _
  rw [hp]
  simp only at e0 e1 e3 e5
  rw [e0, e1, e3, e5]

/-- The check of the context's length: `r12 = ctxlen >> 8`, and Z set exactly when it is 0. -/
def checked (s : State) : State :=
  subFlags (s.setReg .r12 (s.gpr .r2 >>> 8)) (s.gpr .r2 >>> 8) 0

theorem check_exec (s : State) : WP isa (.block check) s fun u => u = checked s :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg .r12 (s.gpr .r2 >>> 8))
    (by simp only [exec]; rw [op2_lsr (by decide)]; rfl)
    (VG.Proof.X25519.Arm.WP.cons (s' := checked s)
      (by simp only [exec]; rw [op2_imm (v := 0) (by decide)]; rfl)
      (WP.block_nil rfl))

theorem checked_pre {s : State} (h : verifyLocal.pre s) : verifyLocal.pre (checked s) := h
theorem checked_post {s u : State} (h : verifyLocal.post (checked s) u) : verifyLocal.post s u := h
theorem checked_abi {s u : State} (h : abiPreserved (checked s) u) : abiPreserved s u := by
  refine ⟨fun r hr => (h.1 r hr).trans ?_, h.2⟩
  have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
  exact RegUpd.gpr_setReg_of_ne _ _ this

theorem checked_z (s : State) : (checked s).z = (s.gpr .r2 >>> 8 - 0 == 0) := rfl

theorem shr8_eq_zero {x : BitVec 32} : (x >>> 8 - 0 == 0) = decide (x.toNat < 256) := by
  show (x >>> 8 - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  by_cases h : x.toNat < 256
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_shr]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [VG.Proof.X25519.Arm.toNat_shr] at this; simp at this; omega

theorem verify_ok (hv : EqOk) {s : State} (h : verifyLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  refine WP.seq (WP.mono (check_exec s) fun u hu => ?_)
  subst hu
  refine WP.ite (decide ((s.gpr .r2).toNat < 256))
    (by rw [VG.Proof.X25519.Arm.eval_eq, checked_z, shr8_eq_zero]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (inner_ok hv (checked_pre h) (of_decide_eq_true hb)) fun u ⟨ha, hp⟩ =>
      ⟨checked_abi ha, checked_post hp⟩
  · refine VG.Proof.X25519.Arm.wp_movw fun u vu => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
      have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
      rw [vu.other r h0]
      exact RegUpd.gpr_setReg_of_ne _ _ h12
    · rw [vu.sp]; rfl
    · change u.gpr .r0 = _
      rw [vu.gpr]
      have hl : ¬ (s.gpr .r2).toNat < 256 := by simpa using hb
      have hlen : ¬ (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat).length ≤ 255 := by
        simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; omega
      simp only [Spec.Ed448.verify, hlen, decide_false, Bool.false_and, signWord]
      rfl

end VG.Proof.Ed448.Arm.Verify
